/*
 * TRABALHO AVALIATIVO - RA03 | Complexidade de Algoritmos | PUCPR
 * =================================================================
 * Problema: Set Cover (Cobertura de Conjuntos)
 *
 * Universo U = {1, 2, ..., 25}
 * S15 = todos os subconjuntos de 15 elementos de U
 *
 * Para p em {14, 13, 12, 11}:
 *   Encontrar SB ⊆ S15 tal que para todo Y em Sp, existe X em SB com Y ⊆ X
 *
 * Estrategia: Algoritmo Guloso (Greedy Set Cover) com Lazy Heap
 * Representacao: Bitmasks de 25 bits (1 uint32_t por combinacao)
 *
 * Versao C deste trabalho, traduzida da versao Python original.
 * Como C nao possui 'set' ou 'heapq' nativos, foram implementados:
 *   - HashSet de inteiros (open addressing, linear probing, tombstones)
 *   - Max-Heap binario sobre vetor (array based)
 *
 * Compilacao:
 *   gcc -O2 -Wall -o trabalho_ra03 trabalho_ra03.c -lm
 *
 * Uso:
 *   ./trabalho_ra03              -> roda todos (14, 13, 12, 11)
 *   ./trabalho_ra03 14           -> roda so cobertura de 14
 *   ./trabalho_ra03 14 13        -> roda cobertura de 14 e 13
 *
 * Parametros do universo (N_UNIVERSE, K_LARGE) podem ser sobrescritos
 * em tempo de compilacao para testes em escala reduzida, por exemplo:
 *   gcc -DN_UNIVERSE=8 -DK_LARGE=5 -O2 -o teste trabalho_ra03.c -lm
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#ifndef N_UNIVERSE
#define N_UNIVERSE 25
#endif
#ifndef K_LARGE
#define K_LARGE 15
#endif

typedef uint32_t mask_t;

/* ============================================================
 * UTILITARIOS
 * ============================================================ */

static double now_seconds(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double) ts.tv_sec + (double) ts.tv_nsec / 1e9;
}

/* Formata um inteiro com separador de milhar (',') em buf. */
static void format_thousands(unsigned long long n, char *buf, size_t bufsize) {
    char tmp[32];
    snprintf(tmp, sizeof(tmp), "%llu", n);
    int len = (int) strlen(tmp);
    int commas = (len - 1) / 3;
    int newlen = len + commas;
    if ((size_t) newlen + 1 > bufsize) newlen = (int) bufsize - 1;
    buf[newlen] = '\0';
    int ti = len - 1, bi = newlen - 1, cnt = 0;
    while (ti >= 0 && bi >= 0) {
        buf[bi--] = tmp[ti--];
        cnt++;
        if (cnt % 3 == 0 && ti >= 0 && bi >= 0) buf[bi--] = ',';
    }
}

static void print_line(char c, int n) {
    for (int i = 0; i < n; i++) putchar(c);
    putchar('\n');
}

/* C(n,k) calculado com a formula multiplicativa segura
 * (cada passo intermediario eh sempre inteiro). */
static unsigned long long n_choose_k(int n, int k) {
    if (k < 0 || k > n) return 0;
    if (k > n - k) k = n - k;
    unsigned long long result = 1;
    for (int i = 1; i <= k; i++) {
        result = result * (unsigned long long) (n - k + i) / (unsigned long long) i;
    }
    return result;
}

static size_t next_pow2(size_t x) {
    size_t p = 1;
    while (p < x) p <<= 1;
    return p;
}

/* ============================================================
 * REPRESENTACAO POR BITMASKS
 * ============================================================
 * Cada subconjunto de {1,...,N} vira um inteiro de 25 bits.
 * Elemento i (1-indexed) -> bit (i-1).
 *   Ex: {1, 3, 5} -> bit 0 + bit 2 + bit 4 -> 0b10101 = 21
 * ============================================================ */

/* Gera todas as C(n,k) combinacoes como bitmasks, armazenando em 'out'
 * (que deve ter capacidade n_choose_k(n,k)). */
static void generate_bitmasks_rec(int n, int k, int start, int depth,
                                   mask_t cur, mask_t *out, size_t *count) {
    if (depth == k) {
        out[(*count)++] = cur;
        return;
    }
    for (int i = start; i <= n - (k - depth); i++) {
        generate_bitmasks_rec(n, k, i + 1, depth + 1, cur | (1u << i), out, count);
    }
}

static mask_t *generate_bitmasks(int n, int k, size_t *out_count) {
    unsigned long long total = n_choose_k(n, k);
    mask_t *out = malloc(sizeof(mask_t) * (size_t) total);
    if (!out) { fprintf(stderr, "Falha ao alocar memoria para combinacoes.\n"); exit(1); }
    size_t count = 0;
    generate_bitmasks_rec(n, k, 0, 0, 0, out, &count);
    *out_count = count;
    return out;
}

/* Converte bitmask -> conjunto legivel {1, 2, ...}, imprime direto. */
static void print_bitmask_as_set(mask_t mask, int n) {
    int first = 1;
    printf("[");
    for (int i = 0; i < n; i++) {
        if (mask & (1u << i)) {
            if (!first) printf(", ");
            printf("%d", i + 1);
            first = 0;
        }
    }
    printf("]");
}

/* Retorna posicoes dos bits setados (0-indexed) em 'out'; devolve quantidade. */
static int get_set_bits(mask_t mask, int n, uint8_t *out) {
    int count = 0;
    for (int i = 0; i < n; i++) {
        if (mask & (1u << i)) out[count++] = (uint8_t) i;
    }
    return count;
}

/* ============================================================
 * HASH SET DE INTEIROS (open addressing, linear probing)
 * ============================================================
 * Substitui o 'set' nativo do Python para armazenar os alvos
 * ainda nao cobertos (uncovered). Suporta insercao, busca e
 * remocao (com tombstones) em tempo esperado O(1).
 * ============================================================ */

#define HS_EMPTY    0
#define HS_OCCUPIED 1
#define HS_DELETED  2

typedef struct {
    mask_t *keys;
    uint8_t *state;
    size_t capacity;   /* sempre potencia de 2 */
    size_t size;       /* elementos ocupados (sem contar tombstones) */
} HashSet;

static inline uint64_t hash_u32(uint32_t x) {
    uint64_t h = x;
    h *= 11400714819323198485ULL; /* constante da razao aurea (Fibonacci hashing) */
    return h;
}

static HashSet *hashset_create(size_t capacity_pow2) {
    HashSet *hs = malloc(sizeof(HashSet));
    hs->capacity = capacity_pow2;
    hs->size = 0;
    hs->keys = malloc(sizeof(mask_t) * capacity_pow2);
    hs->state = calloc(capacity_pow2, sizeof(uint8_t));
    if (!hs->keys || !hs->state) { fprintf(stderr, "Falha ao alocar HashSet.\n"); exit(1); }
    return hs;
}

static void hashset_insert(HashSet *hs, mask_t key) {
    size_t mask = hs->capacity - 1;
    size_t idx = (size_t) (hash_u32(key) & mask);
    while (hs->state[idx] == HS_OCCUPIED) {
        if (hs->keys[idx] == key) return;
        idx = (idx + 1) & mask;
    }
    hs->keys[idx] = key;
    hs->state[idx] = HS_OCCUPIED;
    hs->size++;
}

static int hashset_contains(const HashSet *hs, mask_t key) {
    size_t mask = hs->capacity - 1;
    size_t idx = (size_t) (hash_u32(key) & mask);
    while (hs->state[idx] != HS_EMPTY) {
        if (hs->state[idx] == HS_OCCUPIED && hs->keys[idx] == key) return 1;
        idx = (idx + 1) & mask;
    }
    return 0;
}

static void hashset_remove(HashSet *hs, mask_t key) {
    size_t mask = hs->capacity - 1;
    size_t idx = (size_t) (hash_u32(key) & mask);
    while (hs->state[idx] != HS_EMPTY) {
        if (hs->state[idx] == HS_OCCUPIED && hs->keys[idx] == key) {
            hs->state[idx] = HS_DELETED;
            hs->size--;
            return;
        }
        idx = (idx + 1) & mask;
    }
}

static void hashset_free(HashSet *hs) {
    free(hs->keys);
    free(hs->state);
    free(hs);
}

/* Gera C(n,k) combinacoes e insere diretamente no hash set, sem
 * passar por um vetor intermediario (economiza memoria). */
static void generate_into_hashset_rec(int n, int k, int start, int depth,
                                       mask_t cur, HashSet *hs) {
    if (depth == k) {
        hashset_insert(hs, cur);
        return;
    }
    for (int i = start; i <= n - (k - depth); i++) {
        generate_into_hashset_rec(n, k, i + 1, depth + 1, cur | (1u << i), hs);
    }
}

static void generate_into_hashset(int n, int k, HashSet *hs) {
    generate_into_hashset_rec(n, k, 0, 0, 0, hs);
}

/* ============================================================
 * SCORING OTIMIZADO VIA BIT-CLEARING (XOR)
 * ============================================================
 * Em vez de construir submascaras do zero, partimos da mascara
 * completa X e desligamos (15-p) bits via XOR:
 *
 *   submascara = X xor (1<<bit_a) xor (1<<bit_b) xor ...
 *
 * Para p=14: desligar 1 bit  -> C(15,1) = 15 submascaras
 * Para p=13: desligar 2 bits -> C(15,2) = 105
 * Para p=12: desligar 3 bits -> C(15,3) = 455
 * Para p=11: desligar 4 bits -> C(15,4) = 1365
 * ============================================================ */

/* Conta quantas submascaras de x_mask (removendo num_to_clear bits)
 * ainda estao em 'uncovered'. Complexidade: Theta(C(num_bits, num_to_clear)) */
static long fast_score_rec(const uint8_t *bits, int num_bits, int num_to_clear,
                            int start, int depth, mask_t cur_mask, const HashSet *uncovered) {
    if (depth == num_to_clear) {
        return hashset_contains(uncovered, cur_mask) ? 1 : 0;
    }
    long count = 0;
    for (int i = start; i <= num_bits - (num_to_clear - depth); i++) {
        mask_t new_mask = cur_mask ^ (1u << bits[i]);
        count += fast_score_rec(bits, num_bits, num_to_clear, i + 1, depth + 1, new_mask, uncovered);
    }
    return count;
}

static long fast_score(mask_t x_mask, const uint8_t *bits, int num_bits,
                        int num_to_clear, const HashSet *uncovered) {
    return fast_score_rec(bits, num_bits, num_to_clear, 0, 0, x_mask, uncovered);
}

/* Coleta em 'out' as submascaras de x_mask presentes em 'uncovered'.
 * 'out' deve ter capacidade >= C(num_bits, num_to_clear). */
static void fast_get_covered_rec(const uint8_t *bits, int num_bits, int num_to_clear,
                                  int start, int depth, mask_t cur_mask,
                                  const HashSet *uncovered, mask_t *out, int *out_count) {
    if (depth == num_to_clear) {
        if (hashset_contains(uncovered, cur_mask)) {
            out[(*out_count)++] = cur_mask;
        }
        return;
    }
    for (int i = start; i <= num_bits - (num_to_clear - depth); i++) {
        mask_t new_mask = cur_mask ^ (1u << bits[i]);
        fast_get_covered_rec(bits, num_bits, num_to_clear, i + 1, depth + 1, new_mask,
                              uncovered, out, out_count);
    }
}

static int fast_get_covered(mask_t x_mask, const uint8_t *bits, int num_bits,
                             int num_to_clear, const HashSet *uncovered, mask_t *out) {
    int out_count = 0;
    fast_get_covered_rec(bits, num_bits, num_to_clear, 0, 0, x_mask, uncovered, out, &out_count);
    return out_count;
}

/* ============================================================
 * MAX-HEAP BINARIO (array based)
 * ============================================================
 * Substitui o heapq (min-heap) do Python. Aqui usamos um max-heap
 * de verdade sobre a estimativa (sem necessidade de negar valores).
 * ============================================================ */

typedef struct {
    int32_t est;
    uint32_t idx;
} HeapNode;

typedef struct {
    HeapNode *data;
    size_t size;
    size_t capacity;
} MaxHeap;

static MaxHeap *heap_create(size_t capacity) {
    MaxHeap *h = malloc(sizeof(MaxHeap));
    h->capacity = capacity > 0 ? capacity : 1;
    h->size = 0;
    h->data = malloc(sizeof(HeapNode) * h->capacity);
    if (!h->data) { fprintf(stderr, "Falha ao alocar heap.\n"); exit(1); }
    return h;
}

static void heap_ensure_capacity(MaxHeap *h, size_t needed) {
    if (needed > h->capacity) {
        size_t newcap = h->capacity * 2 > needed ? h->capacity * 2 : needed;
        h->data = realloc(h->data, sizeof(HeapNode) * newcap);
        if (!h->data) { fprintf(stderr, "Falha ao realocar heap.\n"); exit(1); }
        h->capacity = newcap;
    }
}

static void heap_sift_up(MaxHeap *h, size_t i) {
    while (i > 0) {
        size_t parent = (i - 1) / 2;
        if (h->data[parent].est < h->data[i].est) {
            HeapNode tmp = h->data[parent];
            h->data[parent] = h->data[i];
            h->data[i] = tmp;
            i = parent;
        } else break;
    }
}

static void heap_sift_down(MaxHeap *h, size_t i) {
    for (;;) {
        size_t l = 2 * i + 1, r = 2 * i + 2, largest = i;
        if (l < h->size && h->data[l].est > h->data[largest].est) largest = l;
        if (r < h->size && h->data[r].est > h->data[largest].est) largest = r;
        if (largest == i) break;
        HeapNode tmp = h->data[i];
        h->data[i] = h->data[largest];
        h->data[largest] = tmp;
        i = largest;
    }
}

static void heap_push(MaxHeap *h, HeapNode node) {
    heap_ensure_capacity(h, h->size + 1);
    h->data[h->size] = node;
    heap_sift_up(h, h->size);
    h->size++;
}

static HeapNode heap_pop(MaxHeap *h) {
    HeapNode top = h->data[0];
    h->size--;
    h->data[0] = h->data[h->size];
    heap_sift_down(h, 0);
    return top;
}

/* Constroi o heap em O(n) a partir de h->data[0..size-1] ja preenchido. */
static void heap_heapify(MaxHeap *h) {
    if (h->size < 2) return;
    for (size_t i = h->size / 2; i-- > 0;) {
        heap_sift_down(h, i);
        if (i == 0) break;
    }
}

static void heap_free(MaxHeap *h) {
    free(h->data);
    free(h);
}

/* ============================================================
 * VETOR DINAMICO (substitui list.append do Python para a solucao)
 * ============================================================ */

typedef struct {
    mask_t *data;
    size_t size;
    size_t capacity;
} DynArray;

static void dynarray_init(DynArray *a) {
    a->data = NULL;
    a->size = 0;
    a->capacity = 0;
}

static void dynarray_push(DynArray *a, mask_t v) {
    if (a->size == a->capacity) {
        a->capacity = a->capacity ? a->capacity * 2 : 1024;
        a->data = realloc(a->data, sizeof(mask_t) * a->capacity);
        if (!a->data) { fprintf(stderr, "Falha ao realocar solucao.\n"); exit(1); }
    }
    a->data[a->size++] = v;
}

/* ============================================================
 * PROGRAMA 1: Geracao das Combinacoes (demonstracao / timing)
 * Mantido por fidelidade ao script original; nao eh chamado a
 * partir de main(), assim como na versao Python.
 * ============================================================ */

static void programa1(int n) {
    print_line('=', 60);
    printf("  PROGRAMA 1 -- Geracao das Combinacoes\n");
    print_line('=', 60);

    int ks[5] = {15, 14, 13, 12, 11};
    for (int i = 0; i < 5; i++) {
        int k = ks[i];
        double t = now_seconds();
        unsigned long long expected = n_choose_k(n, k);
        char buf[40];
        format_thousands(expected, buf, sizeof(buf));
        printf("  S%d: C(%d,%d) = %10s...", k, n, k, buf);
        fflush(stdout);
        size_t count;
        mask_t *masks = generate_bitmasks(n, k, &count);
        printf(" (%.1fs)\n", now_seconds() - t);
        free(masks);
    }
}

/* ============================================================
 * PROGRAMAS 2-5: Greedy Set Cover com Lazy Heap
 * ============================================================
 * IDEIA DO ALGORITMO GULOSO:
 *   A cada passo, selecionar o conjunto X em S15 que cobre o MAIOR
 *   numero de alvos ainda nao cobertos. Repetir ate cobrir tudo.
 *
 *   Garantia teorica: |SB_greedy| <= H(c) * |SB_otimo|
 *   onde H(c) = 1 + 1/2 + ... + 1/c (numero harmonico)
 *   e c = C(15, p) = max cobertura por conjunto.
 *
 * OTIMIZACAO COM LAZY HEAP:
 *   1. Inicializa todos com estimativa otimista = C(15,p)
 *   2. Pop do heap -> recalcula score real do candidato
 *   3. Se score real == estimativa -> e o melhor, seleciona
 *   4. Se score real < estimativa  -> push de volta com valor corrigido
 *   5. Se score real == 0          -> descarta
 * ============================================================ */

static DynArray greedy_set_cover(const mask_t *s15, const uint8_t *s15_bits,
                                  size_t s15_count, int target_size, int n) {
    int k_large = K_LARGE;
    int num_to_clear = k_large - target_size;
    unsigned long long c_per_set = n_choose_k(k_large, target_size);
    unsigned long long total_targets = n_choose_k(n, target_size);
    unsigned long long lower_bound = (total_targets + c_per_set - 1) / c_per_set;

    int prog_num;
    switch (target_size) {
        case 14: prog_num = 2; break;
        case 13: prog_num = 3; break;
        case 12: prog_num = 4; break;
        case 11: prog_num = 5; break;
        default: prog_num = 0; break;
    }

    char buf1[40], buf2[40], buf3[40];
    format_thousands(total_targets, buf1, sizeof(buf1));
    format_thousands(lower_bound, buf2, sizeof(buf2));

    printf("\n");
    print_line('=', 60);
    printf("  PROGRAMA %d -- Cobertura de %d elementos\n", prog_num, target_size);
    print_line('=', 60);
    printf("  |S_%d| = C(25,%d) = %s alvos\n", target_size, target_size, buf1);
    printf("  Cada X em S15 cobre C(15,%d) = %llu alvos\n", target_size, c_per_set);
    printf("  Limite inferior teorico: ceil(%s/%llu) = %s\n", buf1, c_per_set, buf2);
    printf("  Bits desligados por submascara: %d\n", num_to_clear);

    /* Gerar conjunto de alvos nao cobertos */
    double t0 = now_seconds();
    printf("  Gerando alvos... ");
    fflush(stdout);
    size_t hs_capacity = next_pow2((size_t) (total_targets * 2));
    HashSet *uncovered = hashset_create(hs_capacity);
    generate_into_hashset(n, target_size, uncovered);
    unsigned long long total = uncovered->size;
    printf("OK (%.1fs)\n", now_seconds() - t0);

    format_thousands((unsigned long long) s15_count, buf3, sizeof(buf3));
    printf("  Inicializando heap (%s candidatos)...\n", buf3);
    MaxHeap *heap = heap_create(s15_count);
    for (size_t i = 0; i < s15_count; i++) {
        heap->data[i].est = (int32_t) c_per_set;
        heap->data[i].idx = (uint32_t) i;
    }
    heap->size = s15_count;
    heap_heapify(heap);

    DynArray solution;
    dynarray_init(&solution);
    unsigned long long rescore_count = 0;
    double t_greedy = now_seconds();
    unsigned long long report_interval = lower_bound / 10;
    if (report_interval < 1) report_interval = 1;

    printf("  Selecao gulosa...\n\n");

    /* Buffer para submascaras cobertas; C(15,4)=1365 eh o maior caso (p=11) */
    mask_t covered_buf[2048];

    while (uncovered->size > 0 && heap->size > 0) {
        int selected = 0;
        uint32_t sel_idx = 0;

        while (heap->size > 0) {
            HeapNode top = heap_pop(heap);
            if (top.est <= 0) {
                heap->size = 0;
                break;
            }

            long actual = fast_score(s15[top.idx], &s15_bits[(size_t) top.idx * k_large],
                                      k_large, num_to_clear, uncovered);
            rescore_count++;

            if (actual == top.est) {
                selected = 1;
                sel_idx = top.idx;
                break;
            } else if (actual > 0) {
                HeapNode newnode = { (int32_t) actual, top.idx };
                heap_push(heap, newnode);
            }
            /* actual == 0: descarta (nao reinsere) */
        }

        if (!selected) break;

        mask_t x = s15[sel_idx];
        dynarray_push(&solution, x);

        int cov_count = fast_get_covered(x, &s15_bits[(size_t) sel_idx * k_large],
                                          k_large, num_to_clear, uncovered, covered_buf);
        for (int ci = 0; ci < cov_count; ci++) {
            hashset_remove(uncovered, covered_buf[ci]);
        }

        if (solution.size % report_interval == 0 || uncovered->size == 0) {
            double elapsed = now_seconds() - t_greedy;
            double pct = (1.0 - (double) uncovered->size / (double) total) * 100.0;
            char sbuf[40], rbuf[40];
            format_thousands((unsigned long long) solution.size, sbuf, sizeof(sbuf));
            format_thousands(rescore_count, rbuf, sizeof(rbuf));
            printf("    |SB|=%10s | cobertos=%6.2f%% | rescores=%14s | t=%.0fs\n",
                   sbuf, pct, rbuf, elapsed);
        }
    }

    double elapsed_total = now_seconds() - t0;

    char sol_buf[40], lb_buf[40], cov_buf[40], tot_buf[40], rc_buf[40];
    format_thousands((unsigned long long) solution.size, sol_buf, sizeof(sol_buf));
    format_thousands(lower_bound, lb_buf, sizeof(lb_buf));
    format_thousands(total - uncovered->size, cov_buf, sizeof(cov_buf));
    format_thousands(total, tot_buf, sizeof(tot_buf));
    format_thousands(rescore_count, rc_buf, sizeof(rc_buf));

    printf("\n  --------------------------------------------------\n");
    printf("  RESULTADO -- Programa %d (cobertura de %d):\n", prog_num, target_size);
    printf("    |SB_{15,%d}|       = %s\n", target_size, sol_buf);
    printf("    Limite inferior    = %s\n", lb_buf);
    printf("    Razao SB/LB        = %.2fx\n", (double) solution.size / (double) lower_bound);
    printf("    Cobertos           = %s/%s\n", cov_buf, tot_buf);
    printf("    Total de rescores  = %s\n", rc_buf);
    printf("    Tempo total        = %.1fs\n", elapsed_total);
    printf("  --------------------------------------------------\n");

    hashset_free(uncovered);
    heap_free(heap);

    return solution;
}

/* ============================================================
 * VERIFICACAO
 * ============================================================ */

static int popcount32(mask_t x) {
    int c = 0;
    while (x) { c += (int) (x & 1u); x >>= 1; }
    return c;
}

static void verify_insert_rec(const uint8_t *bits, int num_bits, int num_to_clear,
                               int start, int depth, mask_t cur_mask, HashSet *covered) {
    if (depth == num_to_clear) {
        hashset_insert(covered, cur_mask);
        return;
    }
    for (int i = start; i <= num_bits - (num_to_clear - depth); i++) {
        mask_t new_mask = cur_mask ^ (1u << bits[i]);
        verify_insert_rec(bits, num_bits, num_to_clear, i + 1, depth + 1, new_mask, covered);
    }
}

/* Verifica se TODAS as combinacoes de target_size foram cobertas. */
static int verify(const mask_t *solution, size_t solution_count, int target_size, int n) {
    printf("  Verificando... ");
    fflush(stdout);

    unsigned long long total_targets = n_choose_k(n, target_size);
    size_t cap = next_pow2((size_t) (total_targets * 2));

    HashSet *all_targets = hashset_create(cap);
    generate_into_hashset(n, target_size, all_targets);

    HashSet *covered = hashset_create(cap);

    if (solution_count == 0) {
        printf("INCORRETO -- solucao vazia!\n");
        hashset_free(all_targets);
        hashset_free(covered);
        return 0;
    }

    int k_large = popcount32(solution[0]);
    int num_to_clear = k_large - target_size;

    uint8_t bits[N_UNIVERSE];
    for (size_t s = 0; s < solution_count; s++) {
        mask_t x = solution[s];
        int nb = get_set_bits(x, n, bits);
        verify_insert_rec(bits, nb, num_to_clear, 0, 0, x, covered);
    }

    unsigned long long missing = 0;
    for (size_t i = 0; i < all_targets->capacity; i++) {
        if (all_targets->state[i] == HS_OCCUPIED) {
            if (!hashset_contains(covered, all_targets->keys[i])) missing++;
        }
    }

    char buf[40];
    if (missing == 0) {
        format_thousands(total_targets, buf, sizeof(buf));
        printf("OK -- todas as %s combinacoes cobertas!\n", buf);
    } else {
        format_thousands(missing, buf, sizeof(buf));
        printf("INCORRETO -- %s combinacoes faltando!\n", buf);
    }

    hashset_free(all_targets);
    hashset_free(covered);
    return missing == 0;
}

/* ============================================================
 * MAIN
 * ============================================================ */

int main(int argc, char **argv) {
    /* Forca stdout em modo linha-a-linha mesmo quando redirecionado para
     * arquivo/pipe, para que o progresso seja visivel em tempo real
     * (equivalente ao uso de flush=True no script Python original). */
    setvbuf(stdout, NULL, _IOLBF, 0);

    int n = N_UNIVERSE;
    int k = K_LARGE;

    int targets[64];
    int num_targets;

    if (argc > 1) {
        num_targets = argc - 1;
        if (num_targets > 64) num_targets = 64;
        for (int i = 0; i < num_targets; i++) targets[i] = atoi(argv[i + 1]);
    } else {
        int defaults[4] = {14, 13, 12, 11};
        num_targets = 4;
        memcpy(targets, defaults, sizeof(defaults));
    }

    print_line('=', 60);
    printf("  PROGRAMA 1 -- Geracao de S%d\n", k);
    print_line('=', 60);

    double t = now_seconds();
    size_t s15_count;
    mask_t *s15 = generate_bitmasks(n, k, &s15_count);
    char cbuf[40];
    format_thousands((unsigned long long) s15_count, cbuf, sizeof(cbuf));
    printf("  |S%d| = %s combinacoes (%.1fs)\n", k, cbuf, now_seconds() - t);

    printf("  Pre-computando cache de bits... ");
    fflush(stdout);
    t = now_seconds();
    uint8_t *s15_bits = malloc(sizeof(uint8_t) * s15_count * (size_t) k);
    if (!s15_bits) { fprintf(stderr, "Falha ao alocar cache de bits.\n"); return 1; }
    for (size_t i = 0; i < s15_count; i++) {
        get_set_bits(s15[i], n, &s15_bits[i * (size_t) k]);
    }
    printf("OK (%.1fs)\n", now_seconds() - t);

    for (int ti = 0; ti < num_targets; ti++) {
        int p = targets[ti];
        DynArray sol = greedy_set_cover(s15, s15_bits, s15_count, p, n);
        verify(sol.data, sol.size, p, n);

        printf("\n  Amostra (primeiros 3 conjuntos):\n");
        size_t lim = sol.size < 3 ? sol.size : 3;
        for (size_t i = 0; i < lim; i++) {
            printf("    ");
            print_bitmask_as_set(sol.data[i], n);
            printf("\n");
        }
        printf("\n");

        free(sol.data);
    }

    free(s15);
    free(s15_bits);

    print_line('=', 60);
    printf("  CONCLUIDO\n");
    print_line('=', 60);

    /* programa1(n); -- disponivel, mas nao chamada por padrao (ver Python original) */

    return 0;
}
