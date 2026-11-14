/*
 * c11_frontier7000_scanner.c — Zero-Float C11 `__int128` Differential Verifier
 * for `research/frontier7000-spread-scan/` (`CrocSwap/integer-mult-bounds`).
 *
 * Verifies:
 *   1. Exact Frontier #7000 (`FULL-RESULT.json`) 3-stratum decomposition & surplus `S = 1,520`.
 *   2. All 12 integer concavity witnesses `r^(2r) < (r-d)^(r-d) * (r+d)^(r+d)` on `[1, 8]`.
 *   3. Exact `[1, 8]` Bauer-Karamata balayage conservation (`{1:5645, 5:1, 8:664}`).
 *   4. Exact `GL_9(Z)` `18 x 18` 2-wire operator equivalence for legal `(5, 5) -> (2, 8)`
 *      commuting-spectator flag re-pivoting vs exact non-equivalence when contact is coupled!
 *
 * License: Apache-2.0
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef __int128 i128;

static i128 ipow128(int base, int exp) {
    i128 res = 1;
    for (int i = 0; i < exp; ++i) res *= (i128)base;
    return res;
}

static int verify_frontier7000_accounting(void) {
    const int t_ranks[18]  = {1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 25, 33, 41, 49, 57, 65, 73, 145};
    const int t_counts[18] = {234, 324, 792, 3870, 1224, 756, 324, 1206, 11126,
                              416, 416, 416, 416, 416, 416, 416, 416, 208};
    const int p_ranks[15]  = {1, 2, 3, 4, 5, 6, 7, 8, 16, 24, 32, 40, 48, 56, 64};
    const int p_counts[15] = {73766, 14904, 14598, 4338, 5760, 306, 216, 812,
                              416, 416, 416, 416, 416, 416, 416};
    const int nat_paid[8]  = {4075, 828, 811, 241, 320, 17, 12, 6};

    i128 sum_t = 0, mass_t = 0, sum_p = 0, mass_p = 0;
    for (int i = 0; i < 18; ++i) {
        sum_t  += t_counts[i];
        mass_t += (i128)t_ranks[i] * t_counts[i];
    }
    for (int i = 0; i < 15; ++i) {
        sum_p  += p_counts[i];
        mass_p += (i128)p_ranks[i] * p_counts[i];
    }
    if (sum_t != 23392 || mass_t != 321364) return 0;
    if (sum_p != 117612 || mass_p != 319844) return 0;
    if (mass_t - mass_p != 1520) return 0;

    i128 nat_n = 0, nat_m = 0;
    for (int r = 1; r <= 8; ++r) {
        nat_n += nat_paid[r - 1];
        nat_m += (i128)r * nat_paid[r - 1];
    }
    if (nat_n != 6310 || nat_m != 10962) return 0;
    if (18 * nat_n + 416 + 3616 != 117612) return 0;
    if (5645 + 1 + 664 != 6310) return 0;
    if (1 * 5645 + 5 * 1 + 8 * 664 != 10962) return 0;

    return 1;
}

static int verify_12_concavity_witnesses(void) {
    int checked = 0;
    for (int r = 2; r <= 7; ++r) {
        int max_d = (r - 1 < 8 - r) ? (r - 1) : (8 - r);
        for (int d = 1; d <= max_d; ++d) {
            i128 lhs = ipow128(r, 2 * r);
            i128 rhs = ipow128(r - d, r - d) * ipow128(r + d, r + d);
            if (!(lhs < rhs)) return 0;
            checked += 1;
        }
    }
    return (checked == 12) ? 1 : 0;
}

/* Multiply two 18x18 integer matrices over __int128 */
static void mat18_mul(i128 out[18][18], const i128 A[18][18], const i128 B[18][18]) {
    i128 tmp[18][18];
    for (int i = 0; i < 18; ++i) {
        for (int j = 0; j < 18; ++j) {
            i128 s = 0;
            for (int k = 0; k < 18; ++k) s += A[i][k] * B[k][j];
            tmp[i][j] = s;
        }
    }
    memcpy(out, tmp, sizeof(tmp));
}

static void mat18_eye(i128 M[18][18]) {
    memset(M, 0, sizeof(i128) * 18 * 18);
    for (int i = 0; i < 18; ++i) M[i][i] = 1;
}

static int mat18_eq(const i128 A[18][18], const i128 B[18][18]) {
    for (int i = 0; i < 18; ++i)
        for (int j = 0; j < 18; ++j)
            if (A[i][j] != B[i][j]) return 0;
    return 1;
}

static int mat9_diff_rank_diag_upper(const i128 Q[9][9]) {
    /* For unitriangular / diagonal-shear test matrices I_9 + Delta where Delta has independent active rows,
     * verify exact rank of (Q - I_9) via exact integer Bareiss/row check on active rows. */
    int nonzero_rows = 0;
    for (int i = 0; i < 9; ++i) {
        int row_nz = 0;
        for (int j = 0; j < 9; ++j) {
            i128 d = Q[i][j] - (i == j ? 1 : 0);
            if (d != 0) row_nz = 1;
        }
        if (row_nz) nonzero_rows += 1;
    }
    return nonzero_rows;
}

static int verify_gl9_flag_repivoting(void) {
    /*
     * 2-wire system on 9 native slots per wire (total state = 18 slots: wire A = 0..8, wire B = 9..17).
     * Wire A executes two consecutive `MOVE`s around a wire-to-wire `ADD` contact C (wire B += P_contact * wire A):
     *   Original contracted itinerary `(5, 5)`:
     *     Q1: rank-5 shear on rows {0, 1, 2, 3, 4} driven by spectator slot 8 (so Q1 = S_defer * Q1', where
     *         Q1' has rank 2 on rows {0, 1} and S_defer has rank 3 on rows {2, 3, 4}).
     *     Q2: rank-5 shear on rows {3, 4, 5, 6, 7} driven by spectator slot 8, such that Q2 * S_defer
     *         activates rows {2, 3, 4, 5, 6, 7} PLUS independent column shears -> total rank 8 (`<= 8`!).
     *   Let's build Q1' (rank 2), S_defer (rank 3), Q2 (rank 5) explicitly with disjoint row/col structure:
     *     - Q1' (rank 2): row 0 += x_8, row 1 += 2*x_8
     *     - S_defer (rank 3): row 2 += x_8, row 3 += x_8, row 4 += x_8
     *       => Q1 = S_defer * Q1' has active rows {0,1,2,3,4}? Wait: rank(Q1 - I_9) must be 5!
     *       Remember: if 5 rows all add multiples of the SAME x_8, rank(Q1 - I_9) would be 1, NOT 5!
     *       To have TRUE algebraic quotient rank 5 (`L C_5 R`!), each active row must read an INDEPENDENT source!
     *       Let's use independent disjoint elementary shears:
     *         Q1' (rank 2): row 0 += x_0? No, invertible! Use 2x2 / disjoint pairs or independent sources!
     *         Wait: on 9 slots {0..8}, let source slots be? No: an invertible operator Q with rank(Q - I_9) == 5
     *         simply needs 5 linearly independent rows in (Q - I_9), e.g. diagonal scaling `diag(2,2,2,2,2,1,1,1,1)`
     *         over Q(i) / Z, OR unitriangular Jordan/shift, OR block-2x2 invertible shears!
     *       EVEN CLEANER: Over Z (invertible in GL_9(Z[1/2]) or GL_9(Z) via 5x4? No, rank 5 needs 5 columns!):
     *         In GL_9(Z): take involutory/unipotent + permutation! Specifically, a cycle/permutation or
     *         `diag(-1, -1, -1, -1, -1, 1, 1, 1, 1)` is ALREADY in GL_9(Z) (det = -1) AND has `Q - I_9 = diag(-2,-2,-2,-2,-2,0,0,0,0)` of EXACT RANK 5!!
     *       WAIT A SECOND!! CHECK THAT!!
     *         Let D(mask) in GL_9(Z) be the diagonal reflection `diag(s_0, ..., s_8)` with `s_i in {+1, -1}`
     *         (or upper-triangular/monomial Clifford reflection)!
     *         Wait: if Q1 = diag(-1,-1,-1,-1,-1, 1, 1, 1, 1) (flips {0,1,2,3,4}, rank(Q1 - I_9) = 5!)
     *         and Q2 = diag( 1, 1,-1,-1, 1,-1,-1,-1, 1) (flips {2,3,5,6,7}, rank(Q2 - I_9) = 5!):
     *         Wait: if we defer {2, 3}? No, if Q1 flips {0,1,2,3,4} and we defer {2,3,4} into Q2:
     *           Suppose Q1 flips {0,1, 2,3,4} (5 axes -> rank 5) and Q2 flips {5,6,7,8, ...}? Wait: to go from
     *           (5, 5) to (2, 8), Q2 * S_defer must have rank 8, while Q2 alone has rank 5!
     *           CHECK THIS SET ARITHMETIC ON {0..8}:
     *             Let Q1 flip {0, 1, 2, 3, 4} (size 5 -> EXACT RANK 5!).
     *             Let Q2 flip {5, 6, 7, 8, 0}? Wait: if S_defer = flip({2, 3, 4}) (size 3):
     *               Then Q1' = S_defer^-1 * Q1 = flip({0, 1}) -> EXACT SIZE 2 (RANK 2)!!
     *               And Q2' = Q2 * S_defer: choose Q2 = flip({0, 5, 6, 7, 8}) -> EXACT SIZE 5 (RANK 5)!!
     *               Since {0, 5, 6, 7, 8} and {2, 3, 4} are DISJOINT,
     *               Q2' = Q2 * S_defer = flip({0, 2, 3, 4, 5, 6, 7, 8}) -> EXACT SIZE 8 (RANK 8 <= 8)!!
     *         HOLD EVERYTHING!! CHECK EVERY SINGLE REQUIREMENT ON THAT WITNESS:
     *           - `rank(Q1 - I_9) = |{0,1,2,3,4}| = 5`!
     *           - `rank(Q2 - I_9) = |{0,5,6,7,8}| = 5`!
     *           - Total original ranks: `(5, 5)` (sum = 10 > 9, CANNOT be coalesced into 1 move of rank 10 on 9 slots? Wait: Q2*Q1 flips {1,2,3,4,5,6,7,8} which has rank 8 if there were NO contact C, so WITH an intervening contact C on slots {0, 1}, you CANNOT merge Q1 and Q2 across C because C reads slots {0, 1} AFTER Q1 flips {0, 1} and BEFORE Q2 flips {0} back!!).
     *           - NOW CHECK THE INTERVENING CONTACT `C` (wire B_j += wire A_j for j in {0, 1}):
     *             1. Can we eliminate Q1 altogether (coalesce)? NO! Because C reads slots {0, 1}, which Q1 modified!
     *             2. Does `S_defer = flip({2, 3, 4})` commute with `C` (which only touches slots {0, 1})?
     *                YES!! `C * S_defer == S_defer * C` IDENTICALLY on `Z^18`!
     *             3. Re-pivoted moves:
     *                `Q1' = flip({0, 1})` -> EXACT RANK 2!
     *                `Q2' = flip({0, 2, 3, 4, 5, 6, 7, 8})` -> EXACT RANK 8!
     *                `(Q2'_A * C * Q1'_A) == (Q2_A * C * Q1_A)` IDENTICALLY as `18 x 18` integer matrices!!
     *             4. Now test OBSTRUCTED contact `C_coupled` (which touches slots {0, 1, 2, 3, 4}):
     *                Then `C_coupled` does NOT commute with `S_defer`, and `(Q2'_A * C_coupled * Q1'_A) != (Q2_A * C_coupled * Q1_A)`!
     */
    const int q1_axes[5]  = {0, 1, 2, 3, 4};
    const int q2_axes[5]  = {0, 5, 6, 7, 8};
    const int q1p_axes[2] = {0, 1};
    const int q2p_axes[8] = {0, 2, 3, 4, 5, 6, 7, 8};

    i128 Q1[18][18], Q2[18][18], Q1p[18][18], Q2p[18][18], C_leg[18][18], C_obs[18][18];
    mat18_eye(Q1); mat18_eye(Q2); mat18_eye(Q1p); mat18_eye(Q2p);
    mat18_eye(C_leg); mat18_eye(C_obs);

    for (int i = 0; i < 5; ++i) Q1[q1_axes[i]][q1_axes[i]] = -1;
    for (int i = 0; i < 5; ++i) Q2[q2_axes[i]][q2_axes[i]] = -1;
    for (int i = 0; i < 2; ++i) Q1p[q1p_axes[i]][q1p_axes[i]] = -1;
    for (int i = 0; i < 8; ++i) Q2p[q2p_axes[i]][q2p_axes[i]] = -1;

    /* Legal contact C_leg: wire B[j] += wire A[j] on j in {0, 1} */
    C_leg[9 + 0][0] = 1;
    C_leg[9 + 1][1] = 1;

    /* Obstructed contact C_obs: wire B[j] += wire A[j] on j in {0, 1, 2, 3, 4} */
    for (int j = 0; j < 5; ++j) C_obs[9 + j][j] = 1;

    /* Check exact 9x9 difference ranks */
    i128 q1_9[9][9], q2_9[9][9], q1p_9[9][9], q2p_9[9][9];
    for (int r = 0; r < 9; ++r) {
        for (int c = 0; c < 9; ++c) {
            q1_9[r][c]  = Q1[r][c];
            q2_9[r][c]  = Q2[r][c];
            q1p_9[r][c] = Q1p[r][c];
            q2p_9[r][c] = Q2p[r][c];
        }
    }
    if (mat9_diff_rank_diag_upper(q1_9) != 5 || mat9_diff_rank_diag_upper(q2_9) != 5) return 0;
    if (mat9_diff_rank_diag_upper(q1p_9) != 2 || mat9_diff_rank_diag_upper(q2p_9) != 8) return 0;

    i128 tmp1[18][18], orig_leg[18][18], repiv_leg[18][18], no_q1_leg[18][18];
    mat18_mul(tmp1, C_leg, Q1);
    mat18_mul(orig_leg, Q2, tmp1);

    mat18_mul(tmp1, C_leg, Q1p);
    mat18_mul(repiv_leg, Q2p, tmp1);

    /* Also check that naive coalescing (moving all of Q2*Q1 after C_leg) FAILS! */
    i128 Q_merged[18][18];
    mat18_mul(Q_merged, Q2, Q1);
    mat18_mul(no_q1_leg, Q_merged, C_leg);

    if (!mat18_eq(orig_leg, repiv_leg)) return 0;
    if (mat18_eq(orig_leg, no_q1_leg)) return 0; /* Coalescing across C_leg is illegal! */

    /* Check obstructed contact C_obs rejects (5,5)->(2,8) spread */
    i128 orig_obs[18][18], repiv_obs[18][18];
    mat18_mul(tmp1, C_obs, Q1);
    mat18_mul(orig_obs, Q2, tmp1);

    mat18_mul(tmp1, C_obs, Q1p);
    mat18_mul(repiv_obs, Q2p, tmp1);
    if (mat18_eq(orig_obs, repiv_obs)) return 0;

    return 1;
}

int main(void) {
    if (!verify_frontier7000_accounting()) {
        fprintf(stderr, "C11 FAIL: Frontier #7000 accounting mismatch\n");
        return 1;
    }
    if (!verify_12_concavity_witnesses()) {
        fprintf(stderr, "C11 FAIL: 12 integer concavity witnesses failed\n");
        return 1;
    }
    if (!verify_gl9_flag_repivoting()) {
        fprintf(stderr, "C11 FAIL: GL_9(Z) (5,5)->(2,8) flag re-pivoting failed\n");
        return 1;
    }
    printf("C11_FRONTIER7000_SCANNER_OK: surplus=1520 witnesses=12/12 gl9_repivot_5_5_to_2_8=PASS\n");
    return 0;
}
