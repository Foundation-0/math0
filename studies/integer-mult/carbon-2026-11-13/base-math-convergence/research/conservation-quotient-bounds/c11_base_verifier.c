/*
 * c11_base_verifier.c — Zero-Float C11 `__int128` Independent Differential Checker
 * for `research/conservation-quotient-bounds/` (`CrocSwap/integer-mult-bounds`).
 *
 * Compile: gcc -std=c11 -O2 -Wall -Wextra -Werror c11_base_verifier.c -o c11_base_verifier
 * License: Apache-2.0
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef __int128 i128;

/* 1. Graph Cut-Deletion Unreachability Check (Trustless BFS, zero Dinic trust) */
static int verify_cut_disconnection(
    int num_vertices,
    int num_edges,
    const int (*edges)[2],
    int num_cut_edges,
    const int *cut_edge_indices,
    int num_sources,
    const int *sources,
    int num_sinks,
    const int *sinks
) {
    if (num_vertices <= 0 || num_vertices > 256) return 0;
    unsigned char deleted[1024];
    unsigned char visited[256];
    int queue[256];
    if (num_edges > 1024) return 0;
    memset(deleted, 0, sizeof(deleted));
    memset(visited, 0, sizeof(visited));

    for (int i = 0; i < num_cut_edges; ++i) {
        int idx = cut_edge_indices[i];
        if (idx < 0 || idx >= num_edges) return 0;
        deleted[idx] = 1;
    }

    int q_head = 0, q_tail = 0;
    for (int i = 0; i < num_sources; ++i) {
        int s = sources[i];
        if (s < 0 || s >= num_vertices) return 0;
        if (!visited[s]) {
            visited[s] = 1;
            queue[q_tail++] = s;
        }
    }

    while (q_head < q_tail) {
        int u = queue[q_head++];
        for (int e = 0; e < num_edges; ++e) {
            if (deleted[e]) continue;
            if (edges[e][0] == u) {
                int v = edges[e][1];
                if (v < 0 || v >= num_vertices) return 0;
                if (!visited[v]) {
                    visited[v] = 1;
                    queue[q_tail++] = v;
                }
            }
        }
    }

    for (int i = 0; i < num_sinks; ++i) {
        int t = sinks[i];
        if (t < 0 || t >= num_vertices) return 0;
        if (visited[t]) return 0; /* Cut failed: sink still reachable! */
    }
    return 1;
}

/* 2. Exact `__int128` Verification of Scaled-by-4 Helper300 Persistent+Cache Left Inverse */
static int verify_helper_left_inverse_i128(void) {
    /* Dimensions matching our explicit certified block instance: nx = 8, ny = 8, m = 12, k = 8.
     * Total input state dimension N = 8 + 8 + 12 = 28; output dimension M_out = 8 + 8 + 12 + 8 = 36.
     * Verify:
     *   (1) E * B^T == I_8
     *   (2) P_persist_4 * K_null == 0 (exact 8-field null space!)
     *   (3) C_cache * K_null == 4 * I_8
     *   (4) L_4 * F_4 == 4 * I_28 across all 28 basis columns!
     */
    const int nx = 8, m = 12, k = 8;
    i128 M_mat[8][8];
    i128 E_mat[8][12];
    i128 BT_mat[12][8];

    for (int i = 0; i < nx; ++i) {
        for (int j = 0; j < k; ++j) {
            M_mat[i][j] = (i == j) ? 3 : ((i + j) % 3 == 0 ? -1 : ((i == j + 1) ? 2 : 0));
        }
    }
    memset(E_mat, 0, sizeof(E_mat));
    memset(BT_mat, 0, sizeof(BT_mat));
    for (int i = 0; i < k; ++i) {
        E_mat[i][i] = 1;
        BT_mat[i][i] = 1;
    }
    /* Non-trivial mixing on extra helper coordinates 8..11 while keeping E * B^T == I_8:
     * E has columns 8..11 = 0 or orthogonal to BT rows 8..11: set BT[8+r][c] != 0 and E[r][8+c] = 0.
     * Even sharper: set E[i][8 + (i % 4)] = 1 and shift BT[i][j] = delta_{ij} - BT[8 + (i % 4)][j]
     * so E * B^T == I_8 holds with dense cross-coupling! */
    for (int r = 0; r < 4; ++r) {
        for (int j = 0; j < k; ++j) {
            BT_mat[8 + r][j] = ((r + j) % 2 == 0) ? 1 : -1;
        }
    }
    for (int i = 0; i < k; ++i) {
        int r = i % 4;
        E_mat[i][8 + r] = 1;
        for (int j = 0; j < k; ++j) {
            BT_mat[i][j] = (i == j ? 1 : 0) - BT_mat[8 + r][j];
        }
    }

    /* Check E * B^T == I_8 */
    for (int i = 0; i < k; ++i) {
        for (int j = 0; j < k; ++j) {
            i128 acc = 0;
            for (int l = 0; l < m; ++l) acc += E_mat[i][l] * BT_mat[l][j];
            if (acc != (i == j ? 1 : 0)) return 0;
        }
    }

    /* Check all 8 null-space basis vectors z = e_col:
     * x = -M z, y = 0, h = 4 * B^T z => X4 = 4x - 4y + M E h == 0, Hout = h - B^T E h == 0, C = E h == 4 z */
    for (int col = 0; col < k; ++col) {
        i128 x[8], h[12], eh[8];
        for (int i = 0; i < nx; ++i) x[i] = -M_mat[i][col];
        for (int l = 0; l < m; ++l) h[l] = 4 * BT_mat[l][col];
        for (int i = 0; i < k; ++i) {
            i128 s = 0;
            for (int l = 0; l < m; ++l) s += E_mat[i][l] * h[l];
            eh[i] = s;
            if (eh[i] != (i == col ? 4 : 0)) return 0;
        }
        for (int i = 0; i < nx; ++i) {
            i128 me_i = 0;
            for (int j = 0; j < k; ++j) me_i += M_mat[i][j] * eh[j];
            i128 x4_i = 4 * x[i] + me_i;
            if (x4_i != 0) return 0;
        }
        for (int l = 0; l < m; ++l) {
            i128 bte_l = 0;
            for (int j = 0; j < k; ++j) bte_l += BT_mat[l][j] * eh[j];
            if (h[l] - bte_l != 0) return 0;
        }
    }

    /* Check exact 28-column identity recovery via closed-form decoder L on EVERY unit basis input */
    for (int basis = 0; basis < 28; ++basis) {
        i128 x[8] = {0}, y[8] = {0}, h[12] = {0};
        if (basis < 8) x[basis] = 1;
        else if (basis < 16) y[basis - 8] = 1;
        else h[basis - 16] = 1;

        /* Forward map (scaled by 4 on X4) */
        i128 eh[8] = {0}, mty[8] = {0};
        for (int i = 0; i < k; ++i) {
            for (int l = 0; l < m; ++l) eh[i] += E_mat[i][l] * h[l];
            for (int j = 0; j < nx; ++j) mty[i] += M_mat[j][i] * y[j];
        }
        i128 X4[8], Y_out[8], H_out[12], C_out[8];
        for (int i = 0; i < nx; ++i) {
            i128 meh_i = 0;
            for (int j = 0; j < k; ++j) meh_i += M_mat[i][j] * eh[j];
            X4[i] = 4 * x[i] - 4 * y[i] + meh_i;
            Y_out[i] = y[i];
        }
        for (int l = 0; l < m; ++l) {
            i128 bteh_l = 0;
            for (int j = 0; j < k; ++j) bteh_l += BT_mat[l][j] * eh[j];
            H_out[l] = h[l] - bteh_l;
        }
        for (int i = 0; i < k; ++i) {
            C_out[i] = eh[i] - mty[i];
        }

        /* Closed-form polynomial decoder L */
        i128 eh_rec[8];
        for (int i = 0; i < k; ++i) {
            i128 mty_rec = 0;
            for (int j = 0; j < nx; ++j) mty_rec += M_mat[j][i] * Y_out[j];
            eh_rec[i] = C_out[i] + mty_rec;
        }
        for (int i = 0; i < nx; ++i) {
            i128 meh_rec = 0;
            for (int j = 0; j < k; ++j) meh_rec += M_mat[i][j] * eh_rec[j];
            i128 x4_rec = X4[i] + 4 * Y_out[i] - meh_rec;
            if (x4_rec != 4 * x[i]) return 0;
            if (Y_out[i] != y[i]) return 0;
        }
        for (int l = 0; l < m; ++l) {
            i128 bteh_rec = 0;
            for (int j = 0; j < k; ++j) bteh_rec += BT_mat[l][j] * eh_rec[j];
            i128 h_rec = H_out[l] + bteh_rec;
            if (h_rec != h[l]) return 0;
        }
    }
    return 1;
}

/* 3. Exact `__int128` Concavity & Frontier #7000 Rational Relation Check */
static int verify_integer_identities_i128(void) {
    /* Verify 6^12 < 5^5 * 7^7 */
    i128 six12 = 1;
    for (int i = 0; i < 12; ++i) six12 *= 6;
    i128 five5 = 1;
    for (int i = 0; i < 5; ++i) five5 *= 5;
    i128 seven7 = 1;
    for (int i = 0; i < 7; ++i) seven7 *= 7;
    if (six12 != (i128)2176782336ULL) return 0;
    if (five5 * seven7 != (i128)2573571875ULL) return 0;
    if (!(six12 < five5 * seven7)) return 0;

    /* Verify Aska PR #469 exact work conservation:
     * r = {1, 2, 3, 4, 5, 6, 7, 8, 14, 56}
     * PR #450 vs PR #469 sums both equal 93,192 out of m*W = 78 * 1200 = 93,600 (3883/3900) */
    const int r[10] = {1, 2, 3, 4, 5, 6, 7, 8, 14, 56};
    const int n450[10] = {27060, 11132, 3036, 3465, 1188, 462, 154, 99, 1, 184};
    const int n469[10] = {26411, 11209, 3201, 3465, 1089, 660, 55, 99, 1, 184};
    i128 w450 = 0, w469 = 0, cnt450 = 0, cnt469 = 0;
    for (int i = 0; i < 10; ++i) {
        w450 += (i128)r[i] * n450[i];
        w469 += (i128)r[i] * n469[i];
        cnt450 += n450[i];
        cnt469 += n469[i];
    }
    if (w450 != 93192 || w469 != 93192) return 0;
    if (cnt450 != 46781 || cnt469 != 46374) return 0;
    if (w450 * 3900 != (i128)93600 * 3883) return 0;

    /* Verify Frontier #7000 kappa = 363005817 / 100000000000 > PR #6030 kappa = 781451 / 250000000
     * and BIT ordinary saving 0.00385248 = 385248 / 100000000 > kappa_7000 */
    i128 k7000_num = 363005817LL, k7000_den = 100000000000LL;
    i128 k6030_num = 781451LL,    k6030_den = 250000000LL;
    i128 kbit_num  = 385248LL,    kbit_den  = 100000000LL;
    if (!(k7000_num * k6030_den > k6030_num * k7000_den)) return 0;
    if (!(kbit_num * k7000_den > k7000_num * kbit_den)) return 0;

    return 1;
}

int main(void) {
    /* Test cut graph matching our certified 4-input / 4-output bottleneck-3 circuit */
    const int edges[13][2] = {
        {0, 4}, {1, 4}, {1, 5}, {2, 5}, {2, 6}, {3, 6},
        {4, 7}, {5, 8}, {6, 9}, /* <--- 3 bottleneck bridge edges (indices 6, 7, 8) */
        {7, 10}, {7, 11}, {8, 11}, {9, 12}
    };
    const int sources[4] = {0, 1, 2, 3};
    const int sinks[4]   = {10, 11, 12, 13};
    const int cut_idx[3] = {6, 7, 8};
    const int bad_cut[2] = {6, 7};

    if (!verify_cut_disconnection(14, 13, edges, 3, cut_idx, 4, sources, 4, sinks)) {
        fprintf(stderr, "C11 FAIL: valid 3-edge cut did not disconnect!\n");
        return 1;
    }
    if (verify_cut_disconnection(14, 13, edges, 2, bad_cut, 4, sources, 4, sinks)) {
        fprintf(stderr, "C11 FAIL: incomplete 2-edge cut falsely disconnected!\n");
        return 1;
    }
    if (!verify_helper_left_inverse_i128()) {
        fprintf(stderr, "C11 FAIL: Helper300 persistent+cache left inverse failed!\n");
        return 1;
    }
    if (!verify_integer_identities_i128()) {
        fprintf(stderr, "C11 FAIL: integer concavity / Frontier #7000 check failed!\n");
        return 1;
    }

    printf("C11_BASE_VERIFIER_OK: cut_rank=PASS left_inverse_28d=PASS concavity_6_12=PASS frontier7000=PASS\n");
    return 0;
}
