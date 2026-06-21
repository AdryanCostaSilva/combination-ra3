/*
 * TRABALHO AVALIATIVO - RA03 | Complexidade de Algoritmos | PUCPR
 * ================================================================
 * Set Cover via Greedy + Lazy Heap em C
 *
 * Compilar:
 *   Windows (MinGW):  gcc -O2 ra03.c -o ra03.exe
 *   Windows (MSVC):   cl /O2 ra03.c
 *   Linux/Mac:        gcc -O2 ra03.c -o ra03
 *
 * Uso:
 *   ./ra03              -> roda todos (14, 13, 12, 11)
 *   ./ra03 11            -> roda so p=11
 *   ./ra03 12 11         -> roda p=12 e p=11
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

/* ============================================================
 * CONSTANTES
 * ============================================================ */
#define N  25
#define K  15
#define BA_SIZE  (1 << N)          /* 33,554,432 */
#define BA_BYTES (BA_SIZE / 8)     /* 4,194,304 = 4 MB */

/* C(25,15) = 3,268,760 */
#define S15_MAX  3268760

/* ============================================================
 * BITARRAY — O(1) membership via direct bit addressing
 * ============================================================
 * Instead of a hash set (Python's set()), we use a flat bit array
 * of 2^25 bits = 4 MB. Checking if mask M is in the set:
 *   byte = ba[M >> 3], bit = M & 7
 *   result = (byte >> bit) & 1
 * This is one memory read + two bitwise ops = ~2 nanoseconds.
 * Python's set lookup: ~100-200 nanoseconds.
 * ============================================================ */
#define BA_SET(ba, m)  ((ba)[(m) >> 3] |=  (1u << ((m) & 7)))
#define BA_CLR(ba, m)  ((ba)[(m) >> 3] &= ~(1u << ((m) & 7)))
#define BA_GET(ba, m)  (((ba)[(m) >> 3] >> ((m) & 7)) & 1)

/* ============================================================
 * COMBINATORICS TABLE
 * ============================================================ */
static long long C[26][26];

static void init_comb(void) {
    for (int i = 0; i <= 25; i++) {
        C[i][0] = 1;
        for (int j = 1; j <= i; j++)
            C[i][j] = C[i-1][j-1] + C[i-1][j];
    }
}

/* ============================================================
 * COMBINATION GENERATION
 * ============================================================ */

/* Generate all C(n,k) combinations as bitmasks into `out`.
 * Returns count. */
static int gen_masks(int n, int k, uint32_t *out) {
    int *idx = (int *)malloc(k * sizeof(int));
    int count = 0;
    for (int i = 0; i < k; i++) idx[i] = i;

    for (;;) {
        uint32_t mask = 0;
        for (int i = 0; i < k; i++) mask |= (1u << idx[i]);
        out[count++] = mask;

        int i = k - 1;
        while (i >= 0 && idx[i] == n - k + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < k; j++) idx[j] = idx[j-1] + 1;
    }
    free(idx);
    return count;
}

/* Generate all C(n,k) combinations directly INTO a bitarray.
 * No storage needed for the targets themselves. Returns count. */
static int gen_to_bitarray(int n, int k, uint8_t *ba) {
    int *idx = (int *)malloc(k * sizeof(int));
    int count = 0;
    for (int i = 0; i < k; i++) idx[i] = i;

    for (;;) {
        uint32_t mask = 0;
        for (int i = 0; i < k; i++) mask |= (1u << idx[i]);
        BA_SET(ba, mask);
        count++;

        int i = k - 1;
        while (i >= 0 && idx[i] == n - k + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < k; j++) idx[j] = idx[j-1] + 1;
    }
    free(idx);
    return count;
}

/* Extract the K set-bit positions from a mask */
static void extract_bits(uint32_t mask, uint8_t bits[K]) {
    int j = 0;
    for (int i = 0; i < N; i++)
        if (mask & (1u << i)) bits[j++] = (uint8_t)i;
}

/* ============================================================
 * SCORING — the hot path
 * ============================================================
 * For num_to_clear = 15 - target_size bits, we generate all
 * submasks by choosing which bits to XOR off, using nested loops.
 *
 * Each submask check is:  BA_GET(ba, mask ^ (bit_a | bit_b | ...))
 * = one memory read + one AND. In C this compiles to ~3 instructions.
 *
 * Why nested loops instead of recursion:
 *   - No function call overhead
 *   - Compiler can keep loop variables in registers
 *   - Outer XOR results are reused across inner iterations
 *     (e.g. m1 = x ^ (1<<bits[a]) is computed once, reused for all b,c,d)
 * ============================================================ */

static int score(uint32_t x, const uint8_t bits[K], int ntc, const uint8_t *ba) {
    int c = 0;
    if (ntc == 1) {
        for (int a = 0; a < K; a++)
            c += BA_GET(ba, x ^ (1u << bits[a]));
    } else if (ntc == 2) {
        for (int a = 0; a < K-1; a++) {
            uint32_t m1 = x ^ (1u << bits[a]);
            for (int b = a+1; b < K; b++)
                c += BA_GET(ba, m1 ^ (1u << bits[b]));
        }
    } else if (ntc == 3) {
        for (int a = 0; a < K-2; a++) {
            uint32_t m1 = x ^ (1u << bits[a]);
            for (int b = a+1; b < K-1; b++) {
                uint32_t m2 = m1 ^ (1u << bits[b]);
                for (int cc = b+1; cc < K; cc++)
                    c += BA_GET(ba, m2 ^ (1u << bits[cc]));
            }
        }
    } else if (ntc == 4) {
        for (int a = 0; a < K-3; a++) {
            uint32_t m1 = x ^ (1u << bits[a]);
            for (int b = a+1; b < K-2; b++) {
                uint32_t m2 = m1 ^ (1u << bits[b]);
                for (int cc = b+1; cc < K-1; cc++) {
                    uint32_t m3 = m2 ^ (1u << bits[cc]);
                    for (int d = cc+1; d < K; d++)
                        c += BA_GET(ba, m3 ^ (1u << bits[d]));
                }
            }
        }
    }
    return c;
}

/* Clear covered submasks from bitarray, return count cleared */
static int clear_covered(uint32_t x, const uint8_t bits[K], int ntc, uint8_t *ba) {
    int c = 0;
    if (ntc == 1) {
        for (int a = 0; a < K; a++) {
            uint32_t s = x ^ (1u << bits[a]);
            if (BA_GET(ba, s)) { BA_CLR(ba, s); c++; }
        }
    } else if (ntc == 2) {
        for (int a = 0; a < K-1; a++) {
            uint32_t m1 = x ^ (1u << bits[a]);
            for (int b = a+1; b < K; b++) {
                uint32_t s = m1 ^ (1u << bits[b]);
                if (BA_GET(ba, s)) { BA_CLR(ba, s); c++; }
            }
        }
    } else if (ntc == 3) {
        for (int a = 0; a < K-2; a++) {
            uint32_t m1 = x ^ (1u << bits[a]);
            for (int b = a+1; b < K-1; b++) {
                uint32_t m2 = m1 ^ (1u << bits[b]);
                for (int cc = b+1; cc < K; cc++) {
                    uint32_t s = m2 ^ (1u << bits[cc]);
                    if (BA_GET(ba, s)) { BA_CLR(ba, s); c++; }
                }
            }
        }
    } else if (ntc == 4) {
        for (int a = 0; a < K-3; a++) {
            uint32_t m1 = x ^ (1u << bits[a]);
            for (int b = a+1; b < K-2; b++) {
                uint32_t m2 = m1 ^ (1u << bits[b]);
                for (int cc = b+1; cc < K-1; cc++) {
                    uint32_t m3 = m2 ^ (1u << bits[cc]);
                    for (int d = cc+1; d < K; d++) {
                        uint32_t s = m3 ^ (1u << bits[d]);
                        if (BA_GET(ba, s)) { BA_CLR(ba, s); c++; }
                    }
                }
            }
        }
    }
    return c;
}

/* ============================================================
 * BINARY MIN-HEAP (negated scores = max-heap)
 * ============================================================ */
typedef struct { int neg_score; int idx; } HNode;
static HNode *heap;
static int heap_sz;

static void heap_init(int cap) {
    heap = (HNode *)malloc(cap * sizeof(HNode));
    heap_sz = 0;
}

static void heap_push(int nscore, int idx) {
    int i = heap_sz++;
    heap[i].neg_score = nscore;
    heap[i].idx = idx;
    while (i > 0) {
        int p = (i - 1) / 2;
        if (heap[i].neg_score < heap[p].neg_score) {
            HNode t = heap[i]; heap[i] = heap[p]; heap[p] = t;
            i = p;
        } else break;
    }
}

static HNode heap_pop(void) {
    HNode top = heap[0];
    heap[0] = heap[--heap_sz];
    int i = 0;
    for (;;) {
        int l = 2*i+1, r = 2*i+2, s = i;
        if (l < heap_sz && heap[l].neg_score < heap[s].neg_score) s = l;
        if (r < heap_sz && heap[r].neg_score < heap[s].neg_score) s = r;
        if (s == i) break;
        HNode t = heap[i]; heap[i] = heap[s]; heap[s] = t;
        i = s;
    }
    return top;
}

/* ============================================================
 * PRINT HELPERS
 * ============================================================ */
static void print_set(uint32_t mask) {
    printf("    {");
    int first = 1;
    for (int i = 0; i < N; i++) {
        if (mask & (1u << i)) {
            if (!first) printf(", ");
            printf("%d", i + 1);
            first = 0;
        }
    }
    printf("}\n");
}

static double elapsed_sec(clock_t start) {
    return (double)(clock() - start) / CLOCKS_PER_SEC;
}

/* ============================================================
 * GREEDY SET COVER
 * ============================================================ */
static void greedy_cover(uint32_t *s15, uint8_t (*s15_bits)[K],
                         int s15_count, int target_size)
{
    int ntc = K - target_size;
    long long cps = C[K][target_size];
    long long total_targets = C[N][target_size];
    long long lower_bound = (total_targets + cps - 1) / cps;
    int prog_num = K + 1 - target_size;

    printf("\n============================================================\n");
    printf("  PROGRAMA %d - Cobertura de %d elementos (C)\n", prog_num, target_size);
    printf("============================================================\n");
    printf("  |S_%d| = C(25,%d) = %lld alvos\n", target_size, target_size, total_targets);
    printf("  Cada X cobre C(15,%d) = %lld alvos\n", target_size, cps);
    printf("  Limite inferior: ceil(%lld/%lld) = %lld\n", total_targets, cps, lower_bound);

    /* Allocate bitarray for uncovered targets */
    uint8_t *ba = (uint8_t *)calloc(BA_BYTES, 1);
    if (!ba) { printf("  ERRO: sem memoria para bitarray!\n"); return; }

    clock_t t0 = clock();
    printf("  Gerando alvos...");
    fflush(stdout);
    int total = gen_to_bitarray(N, target_size, ba);
    printf(" OK (%.1fs)\n", elapsed_sec(t0));

    /* Initialize heap: all candidates start with optimistic score = C(15,p) */
    printf("  Inicializando heap (%d candidatos)...\n", s15_count);
    heap_init(s15_count + 100);
    for (int i = 0; i < s15_count; i++)
        heap_push(-(int)cps, i);

    printf("  Selecao gulosa...\n\n");

    /* Store solution masks for output */
    int sol_cap = (int)lower_bound * 4 + 1000;
    uint32_t *solution = (uint32_t *)malloc(sol_cap * sizeof(uint32_t));
    int sol_count = 0;
    int uncovered = total;
    long long rescores = 0;
    clock_t t_greedy = clock();
    int report_interval = (int)(lower_bound / 10);
    if (report_interval < 1) report_interval = 1;

    while (uncovered > 0 && heap_sz > 0) {
        int selected = 0;
        int best_idx = -1;

        while (heap_sz > 0) {
            HNode node = heap_pop();
            int est = -node.neg_score;
            if (est <= 0) { heap_sz = 0; break; }

            int actual = score(s15[node.idx], s15_bits[node.idx], ntc, ba);
            rescores++;

            if (actual == est) {
                best_idx = node.idx;
                selected = 1;
                break;
            } else if (actual > 0) {
                heap_push(-actual, node.idx);
            }
        }

        if (!selected) break;

        /* Select this candidate */
        if (sol_count < sol_cap)
            solution[sol_count] = s15[best_idx];
        sol_count++;

        int cleared = clear_covered(s15[best_idx], s15_bits[best_idx], ntc, ba);
        uncovered -= cleared;

        if (sol_count % report_interval == 0 || uncovered <= 0) {
            double pct = (1.0 - (double)uncovered / total) * 100.0;
            printf("    |SB|=%8d | cobertos=%6.2f%% | rescores=%12lld | t=%.0fs\n",
                   sol_count, pct, rescores, elapsed_sec(t_greedy));
        }
    }

    double total_time = elapsed_sec(t0);

    printf("\n  --------------------------------------------------\n");
    printf("  RESULTADO - Programa %d (cobertura de %d):\n", prog_num, target_size);
    printf("    |SB_{15,%d}|       = %d\n", target_size, sol_count);
    printf("    Limite inferior    = %lld\n", lower_bound);
    printf("    Razao SB/LB        = %.2fx\n", (double)sol_count / lower_bound);
    printf("    Cobertos           = %d/%d\n", total - uncovered, total);
    printf("    Total de rescores  = %lld\n", rescores);
    printf("    Tempo total        = %.1fs\n", total_time);
    printf("  --------------------------------------------------\n");

    /* Verify */
    printf("  Verificando...");
    fflush(stdout);
    if (uncovered == 0) {
        printf(" CORRETO - todas as %d combinacoes cobertas!\n", total);
    } else {
        printf(" INCORRETO - %d faltando!\n", uncovered);
    }

    /* Print first 3 solutions */
    printf("\n  Amostra (primeiros 3):\n");
    int show = sol_count < 3 ? sol_count : 3;
    for (int i = 0; i < show; i++)
        print_set(solution[i]);
    printf("\n");

    free(ba);
    free(solution);
    free(heap);
}

/* ============================================================
 * MAIN
 * ============================================================ */
int main(int argc, char *argv[]) {
    init_comb();

    /* Parse target sizes from args (default: all) */
    int targets[4] = {14, 13, 12, 11};
    int ntargets = 4;
    if (argc > 1) {
        ntargets = argc - 1;
        if (ntargets > 4) ntargets = 4;
        for (int i = 0; i < ntargets; i++)
            targets[i] = atoi(argv[i + 1]);
    }

    /* PROGRAMA 1 — Generate S15 */
    printf("============================================================\n");
    printf("  PROGRAMA 1 - Geracao de S15\n");
    printf("============================================================\n");

    uint32_t *s15 = (uint32_t *)malloc(S15_MAX * sizeof(uint32_t));
    if (!s15) { printf("ERRO: sem memoria para S15!\n"); return 1; }

    clock_t t = clock();
    int s15_count = gen_masks(N, K, s15);
    printf("  |S15| = %d combinacoes (%.1fs)\n", s15_count, elapsed_sec(t));

    /* Pre-extract bit positions for all S15 masks */
    printf("  Pre-computando bits...");
    fflush(stdout);
    t = clock();
    uint8_t (*s15_bits)[K] = (uint8_t (*)[K])malloc(s15_count * K);
    if (!s15_bits) { printf("ERRO: sem memoria para bits!\n"); return 1; }
    for (int i = 0; i < s15_count; i++)
        extract_bits(s15[i], s15_bits[i]);
    printf(" OK (%.1fs)\n", elapsed_sec(t));

    /* Run Programs 2-5 */
    for (int i = 0; i < ntargets; i++)
        greedy_cover(s15, s15_bits, s15_count, targets[i]);

    printf("============================================================\n");
    printf("  CONCLUIDO\n");
    printf("============================================================\n");

    free(s15);
    free(s15_bits);
    return 0;
}