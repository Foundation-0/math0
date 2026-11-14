#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <omp.h>
#include <vector>

using i64 = int64_t;
using i128 = __int128_t;
using u128 = __uint128_t;

static inline i128 odd128(i128 x) {
    if (x == 0) return 0;
    u128 ux = static_cast<u128>(x < 0 ? -x : x);
    while ((ux & 1U) == 0U) ux >>= 1U;
    return static_cast<i128>(ux);
}
static inline i128 gcd128(i128 a, i128 b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) { i128 t = a % b; a = b; b = t; }
    return a;
}

bool verify_exact_triple(i64 r, i128 u0, i128 v0, i128 u1, i128 v1, i128 u2, i128 v2) {
    if (u0 == 0 || u1 == 0 || u2 == 0) return false;
    if (u0 == 1 && u1 == 1 && u2 == 1) return false;
    if (gcd128(u0, v0) != 1 || gcd128(u1, v1) != 1 || gcd128(u2, v2) != 1) return false;
    i128 d01 = u0 * v1 - u1 * v0, d02 = u0 * v2 - u2 * v0, d12 = u1 * v2 - u2 * v1;
    if (d01 == 0 || d02 == 0 || d12 == 0) return false;
    i128 w0 = 6 * v0 - (2 * r - 1) * u0, w1 = 6 * v1 - (2 * r - 1) * u1, w2 = 6 * v2 - (2 * r - 1) * u2;
    i128 K = 6 * static_cast<i128>(r) * r - 6 * r - 3;
    if (u0 * w1 * w2 + u1 * w0 * w2 + u2 * w0 * w1 + K * u0 * u1 * u2 != 0) return false;
    auto is_dyadic_q = [&](i128 ua, i128 ub, i128 wb, i128 uc, i128 wc, i128 dab, i128 dac) -> bool {
        i128 num = static_cast<i128>(r) * (r - 1) * (ub * wc + uc * wb);
        i128 f1 = odd128(3 * ua); if (gcd128(num, f1) != f1) return false; num /= f1;
        i128 f2 = odd128(dab);    if (gcd128(num, f2) != f2) return false; num /= f2;
        i128 f3 = odd128(dac);    return gcd128(num, f3) == f3;
    };
    return is_dyadic_q(u0, u1, w1, u2, w2, d01, d02) &&
           is_dyadic_q(u1, u0, w0, u2, w2, d01, d12) &&
           is_dyadic_q(u2, u0, w0, u1, w1, d02, d12);
}

int main() {
    std::cout << std::unitbuf;
    std::vector<int> targets;
    for (int r = 83; r <= 200; ++r) {
        if (((r * (r - 1)) / 2) % 2 == 1) targets.push_back(r);
    }
    for (int r : {40, 61, 141, 165, 168}) targets.push_back(r);

    for (int r : targets) {
        i64 S = static_cast<i64>(r) * (r - 1) / 2;
        i64 K = 6LL * r * r - 6LL * r - 3LL;
        i64 two_r_1 = 2LL * r - 1LL;
        i64 rr1 = static_cast<i64>(r) * (r - 1);
        i64 orr1 = static_cast<i64>(odd128(rr1));
        bool found = false;

        #pragma omp parallel for schedule(dynamic)
        for (i64 v1 = -180; v1 <= 180; ++v1) {
            if (found) continue;
            i64 w1 = 6LL * v1 - two_r_1;
            i128 norm1 = static_cast<i128>(K) - static_cast<i128>(w1) * w1;
            if (norm1 == 0) continue;
            // Exact squareness filter! (K - w1^2)*(K*u2^2 - w2^2)*(K*u0^2 - w0^2) == square!
            // Even faster: Q1/Q2 filter from Theorem 2!
            i128 cand = 3 * static_cast<i128>(orr1) * odd128(norm1);
            int odds[32], nodds = 0;
            for (int s = 1; s <= 401 && nodds < 32; s += 2) {
                if (cand % s == 0) odds[nodds++] = s;
            }
            for (int u2 = 1; u2 <= 17 && !found; ++u2) {
                for (int oi = 0; oi < nodds && !found; ++oi) {
                    i64 s = odds[oi];
                    for (int p2 = 0; p2 <= 9 && !found; ++p2) {
                        i64 mag = s << p2;
                        for (int sgn : {-1, 1}) {
                            i64 d12 = sgn * mag;
                            i64 v2 = u2 * v1 + d12;
                            if (std::gcd(static_cast<i64>(u2), std::abs(v2)) != 1) continue;
                            i64 w2 = 6LL * v2 - two_r_1 * u2;
                            i64 alpha = w2 + u2 * w1;
                            if (alpha == 0) continue;
                            i128 Q2 = static_cast<i128>(w2) * w2 + 2 * static_cast<i128>(u2) * w1 * w2 + static_cast<i128>(K) * u2 * u2;
                            if (Q2 == 0) continue;
                            i128 oQ2 = odd128(Q2);
                            i128 num2 = 3 * static_cast<i128>(rr1) * norm1;
                            if (num2 % oQ2 != 0) continue;
                            i128 Q1 = static_cast<i128>(u2) * w1 * w1 + 2 * static_cast<i128>(w1) * w2 + static_cast<i128>(K) * u2;
                            if (Q1 == 0) continue;
                            i128 oQ1 = odd128(Q1);
                            i128 num1 = 3 * static_cast<i128>(rr1) * (static_cast<i128>(K) * u2 * u2 - static_cast<i128>(w2) * w2);
                            if (num1 % oQ1 != 0) continue;
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
                                        std::cout << "HIT r=" << r << " (S=" << S << ", S%2=" << (S%2) << "): ("
                                                  << static_cast<i64>(u0) << "," << static_cast<i64>(v0) << "), (1,"
                                                  << v1 << "), (" << u2 << "," << v2 << ")\n";
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    std::cout << "DONE\n";
    return 0;
}
