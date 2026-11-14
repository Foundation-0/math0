// cubic_leapfrog_prover.cpp
// Exact C++20 Norm-Divisor Leapfrog Solver & Unconditional Odd-S Monic Certifier
// Target repository: https://github.com/CrocSwap/integer-mult-bounds
// License: Apache-2.0

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <numeric>
#include <omp.h>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

using i64 = int64_t;
using u64 = uint64_t;
using i128 = __int128_t;
using u128 = __uint128_t;

static inline i128 abs128(i128 x) { return x < 0 ? -x : x; }

static inline i128 odd128(i128 x) {
    if (x == 0) return 0;
    u128 ux = static_cast<u128>(x < 0 ? -x : x);
    while ((ux & 1U) == 0U) ux >>= 1U;
    return static_cast<i128>(ux);
}

static inline i64 odd64(i64 x) {
    u64 ux = static_cast<u64>(x < 0 ? -x : x);
    return ux ? static_cast<i64>(ux >> __builtin_ctzll(ux)) : 0;
}

static inline i128 gcd128(i128 a, i128 b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        i128 t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static std::vector<int> g_primes;
static void init_primes(int lim = 300000) {
    std::vector<bool> comp(lim + 1, false);
    for (int i = 3; i <= lim; i += 2) {
        if (!comp[i]) {
            g_primes.push_back(i);
            if (static_cast<i64>(i) * i <= lim) {
                for (int j = i * i; j <= lim; j += 2 * i) comp[j] = true;
            }
        }
    }
}

static void get_odd_divisors(i64 n, std::vector<i64> &divs) {
    divs.clear();
    divs.push_back(1);
    for (int p : g_primes) {
        if (static_cast<i64>(p) * p > n) break;
        if (n % p == 0) {
            int cnt = 0;
            while (n % p == 0) {
                n /= p;
                cnt++;
            }
            size_t sz = divs.size();
            i64 pw = 1;
            for (int c = 1; c <= cnt; ++c) {
                pw *= p;
                for (size_t i = 0; i < sz; ++i) divs.push_back(divs[i] * pw);
            }
        }
    }
    if (n > 1) {
        size_t sz = divs.size();
        for (size_t i = 0; i < sz; ++i) divs.push_back(divs[i] * n);
    }
}

bool verify_exact_triple(i64 r, i128 u0, i128 v0, i128 u1, i128 v1, i128 u2, i128 v2) {
    if (gcd128(u0, v0) != 1 || gcd128(u1, v1) != 1 || gcd128(u2, v2) != 1) return false;
    i128 d01 = u0 * v1 - u1 * v0;
    i128 d02 = u0 * v2 - u2 * v0;
    i128 d12 = u1 * v2 - u2 * v1;
    if (d01 == 0 || d02 == 0 || d12 == 0) return false;
    i128 w0 = 6 * v0 - (2 * r - 1) * u0;
    i128 w1 = 6 * v1 - (2 * r - 1) * u1;
    i128 w2 = 6 * v2 - (2 * r - 1) * u2;
    i128 K = 6 * static_cast<i128>(r) * r - 6 * r - 3;
    if (u0 * w1 * w2 + u1 * w0 * w2 + u2 * w0 * w1 + K * u0 * u1 * u2 != 0) return false;

    auto is_dyadic_q = [&](i128 ua, i128 ub, i128 wb, i128 uc, i128 wc, i128 dab, i128 dac) -> bool {
        if (ua == 0) return false;
        i128 num = static_cast<i128>(r) * (r - 1) * (ub * wc + uc * wb);
        i128 f1 = odd128(3 * ua);
        if (gcd128(num, f1) != f1) return false;
        num /= f1;
        i128 f2 = odd128(dab);
        if (gcd128(num, f2) != f2) return false;
        num /= f2;
        i128 f3 = odd128(dac);
        return gcd128(num, f3) == f3;
    };
    return is_dyadic_q(u0, u1, w1, u2, w2, d01, d02) &&
           is_dyadic_q(u1, u0, w0, u2, w2, d01, d12) &&
           is_dyadic_q(u2, u0, w0, u1, w1, d02, d12);
}

struct OddSCert {
    int r;
    i64 S;
    i64 M;
    bool solvable;
    i64 pairs_checked;
    i64 c0, c1, c2;
};

OddSCert certify_odd_s_arity(int r) {
    i64 S = static_cast<i64>(r) * (r - 1) / 2;
    i64 M = 2LL * r * r - 2LL * r - 1LL;
    i64 two_r_1 = 2LL * r - 1LL;
    OddSCert out{r, S, M, false, 0, 0, 0, 0};
    std::vector<i64> divs;

    for (i64 ax = 1; ax < 2 * S; ax += 2) {
        i128 rem = 3 * static_cast<i128>(ax) * ax - M;
        if (rem == 0) {
            i64 t_odd = static_cast<i64>(odd128(static_cast<i128>(S) * ax));
            get_odd_divisors(t_odd, divs);
            for (int sx : {-1, 1}) {
                i64 x = sx * ax;
                for (i64 ay : divs) {
                    for (int sy : {-1, 1}) {
                        i64 y = sy * ay;
                        if (y == x) continue;
                        out.pairs_checked++;
                        for (i64 w0 : {-3 * x, -x - 4 * y}) {
                            if ((w0 + two_r_1) % 6 != 0) continue;
                            i64 c0 = (w0 + two_r_1) / 6;
                            if (verify_exact_triple(r, 1, c0, 1, c0 + x, 1, c0 + y)) {
                                out.solvable = true;
                                out.c0 = c0; out.c1 = c0 + x; out.c2 = c0 + y;
                                return out;
                            }
                        }
                    }
                }
            }
            continue;
        }
        i64 t_odd = static_cast<i64>(odd128(static_cast<i128>(S) * abs128(rem)));
        get_odd_divisors(t_odd, divs);
        for (int sx : {-1, 1}) {
            i64 x = sx * ax;
            for (i64 ay : divs) {
                if (ay < ax) continue;
                for (int sy : {-1, 1}) {
                    i64 y = sy * ay;
                    if (y == x) continue;
                    out.pairs_checked++;
                    i128 disc = 4 * (static_cast<i128>(x) * x - static_cast<i128>(x) * y + static_cast<i128>(y) * y) - M;
                    if (disc < 0) continue;
                    i64 rt = static_cast<i64>(std::round(std::sqrt(static_cast<long double>(disc))));
                    while (static_cast<i128>(rt) * rt < disc) rt++;
                    while (static_cast<i128>(rt) * rt > disc) rt--;
                    if (static_cast<i128>(rt) * rt != disc) continue;
                    for (int sr : {-1, 1}) {
                        i64 w0 = sr * rt - 2 * x - 2 * y;
                        if ((w0 + two_r_1) % 6 != 0) continue;
                        i64 c0 = (w0 + two_r_1) / 6;
                        if (verify_exact_triple(r, 1, c0, 1, c0 + x, 1, c0 + y)) {
                            out.solvable = true;
                            out.c0 = c0; out.c1 = c0 + x; out.c2 = c0 + y;
                            return out;
                        }
                    }
                }
            }
        }
    }
    return out;
}


void run_leapfrog_search(int r_lo, int r_hi) {
    for (int r = r_lo; r <= r_hi; ++r) {
        i64 S = static_cast<i64>(r) * (r - 1) / 2;
        if (S % 2 != 0) continue; // Even-S arities targeted by dyadic-determinant leapfrog
        i64 K = 6LL * r * r - 6LL * r - 3LL;
        i64 two_r_1 = 2LL * r - 1LL;
        i64 rr1 = static_cast<i64>(r) * (r - 1);
        i64 orr1 = odd64(rr1);
        bool found = false;

        #pragma omp parallel for schedule(dynamic)
        for (i64 v1 = -2500; v1 <= 2500; ++v1) {
            if (found) continue;
            i64 w1 = 6LL * v1 - two_r_1;
            i128 norm1 = static_cast<i128>(K) - static_cast<i128>(w1) * w1;
            i128 cand = static_cast<i128>(orr1) * odd128(norm1);
            int odds[32], nodds = 0;
            for (int s = 1; s <= 125 && nodds < 32; s += 2) {
                if (cand % s == 0) odds[nodds++] = s;
            }
            for (int u2 = 1; u2 <= 35 && !found; ++u2) {
                for (int oi = 0; oi < nodds && !found; ++oi) {
                    i64 s = odds[oi];
                    for (int p2 = 0; p2 <= 17 && !found; ++p2) {
                        i64 mag = s << p2;
                        for (int sgn : {-1, 1}) {
                            i64 d12 = sgn * mag;
                            i64 v2 = u2 * v1 + d12;
                            if (u2 == 1 && v2 <= v1) continue;
                            if (std::gcd(static_cast<i64>(u2), std::abs(v2)) != 1) continue;
                            i64 w2 = 6LL * v2 - two_r_1 * u2;
                            i64 alpha = w2 + u2 * w1;
                            if (alpha == 0) continue;

                            i128 Q1 = static_cast<i128>(u2) * w1 * w1 + 2 * static_cast<i128>(w1) * w2 + static_cast<i128>(K) * u2;
                            if (Q1 == 0) continue;
                            i128 oQ1 = odd128(Q1);
                            i128 num1 = 3 * static_cast<i128>(rr1) * (static_cast<i128>(K) * u2 * u2 - static_cast<i128>(w2) * w2);
                            if (num1 % oQ1 != 0 || (num1 / oQ1) % s != 0) continue;

                            i128 Q2 = static_cast<i128>(w2) * w2 + 2 * static_cast<i128>(u2) * w1 * w2 + static_cast<i128>(K) * u2 * u2;
                            if (Q2 == 0) continue;
                            i128 oQ2 = odd128(Q2);
                            i128 num2 = 3 * static_cast<i128>(rr1) * norm1;
                            if (num2 % oQ2 != 0 || (num2 / oQ2) % s != 0) continue;

                            i128 beta = -(static_cast<i128>(w1) * w2 + static_cast<i128>(K) * u2);
                            i128 raw_u0 = 6 * static_cast<i128>(alpha);
                            i128 raw_v0 = beta + static_cast<i128>(two_r_1) * alpha;
                            i128 g0 = gcd128(raw_u0, raw_v0);
                            i128 u0 = raw_u0 / g0, v0 = raw_v0 / g0;
                            if (u0 < 0) { u0 = -u0; v0 = -v0; }
                            if (verify_exact_triple(r, u0, v0, 1, v1, u2, v2)) {
                                #pragma omp critical
                                {
                                    if (!found) {
                                        found = true;
                                        std::cout << "r=" << r << " : (" << static_cast<i64>(u0) << ","
                                                  << static_cast<i64>(v0) << "), (1," << v1 << "), ("
                                                  << u2 << "," << v2 << ")\n";
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc >= 4 && std::strcmp(argv[1], "--search") == 0) { run_leapfrog_search(std::stoi(argv[2]), std::stoi(argv[3])); return 0; }
    init_primes();
    int r_max = 200;
    bool json_mode = false;
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "--json") == 0) json_mode = true;
        else if (std::strcmp(argv[i], "--rmax") == 0 && i + 1 < argc) r_max = std::stoi(argv[++i]);
    }

    std::vector<int> odd_rs;
    for (int r = 3; r <= r_max; ++r) {
        if (((static_cast<i64>(r) * (r - 1)) / 2) % 2 != 0) odd_rs.push_back(r);
    }

    std::vector<OddSCert> certs(odd_rs.size());
    #pragma omp parallel for schedule(dynamic)
    for (size_t i = 0; i < odd_rs.size(); ++i) {
        certs[i] = certify_odd_s_arity(odd_rs[i]);
    }

    if (json_mode) {
        std::cout << "[\n";
        for (size_t i = 0; i < certs.size(); ++i) {
            const auto &c = certs[i];
            std::cout << "  {\"arity\": " << c.r << ", \"S\": " << c.S << ", \"M\": " << c.M
                      << ", \"status\": \"" << (c.solvable ? "SOLVABLE" : "IMPOSSIBLE_OVER_Z3") << "\""
                      << ", \"divisor_pairs_checked\": " << c.pairs_checked;
            if (c.solvable) {
                std::cout << ", \"c\": [" << c.c0 << ", " << c.c1 << ", " << c.c2 << "]";
            } else {
                std::cout << ", \"c\": null";
            }
            std::cout << "}" << (i + 1 < certs.size() ? "," : "") << "\n";
        }
        std::cout << "]\n";
    } else {
        int sol = 0, imp = 0;
        for (const auto &c : certs) {
            if (c.solvable) sol++; else imp++;
        }
        std::cout << "Certified odd-S arities in [3, " << r_max << "]: solvable=" << sol
                  << ", unconditionally impossible over Z^3=" << imp << "\n";
    }
    return 0;
}
