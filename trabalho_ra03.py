from itertools import combinations

# Geração das combinações
def gerar_combinacoes(universo, numElementos):
    return list(combinations(range(1, universo + 1), numElementos))

# Cobertura de n elementos
def cobertura(fonte, alvoCobertura): # alvoCobertura = s14, s13, s12 ou s11
    # Greedy set cover: choose fonte-sets that cover the most yet-uncovered alvoCobertura elements
    from collections import defaultdict
    import heapq

    s_solucao = []

    if not alvoCobertura:
        return s_solucao

    # normalize to tuple keys (they already are tuples from combinations)
    alvo_set = set(alvoCobertura)
    target_size = len(next(iter(alvo_set)))

    fonte_list = list(fonte)

    # For each fonte index, store which target tuples it covers
    fonte_covers = [set() for _ in range(len(fonte_list))]

    # For each target tuple, store list of fonte indices that contain it
    target_to_fontes = defaultdict(list)

    # Build the coverage relations. For a fonte set f (size m) it covers all
    # combinations of f of size target_size; that number is small when m-target_size is small.
    for i, f in enumerate(fonte_list):
        # f is a tuple; generate all target-size subsets of f
        for sub in combinations(f, target_size):
            if sub in alvo_set:
                fonte_covers[i].add(sub)
                target_to_fontes[sub].append(i)

    # remaining count of uncovered targets each fonte can cover
    remaining = [len(s) for s in fonte_covers]

    # max-heap of (-(remaining_count), fonte_index). We use lazy updates.
    heap = []
    for i, cnt in enumerate(remaining):
        if cnt > 0:
            heapq.heappush(heap, (-cnt, i))

    uncovered = set(alvo_set)

    while uncovered and heap:
        negcnt, idx = heapq.heappop(heap)
        cnt = -negcnt
        # skip stale entries
        if remaining[idx] != cnt:
            continue
        if cnt == 0:
            break

        # choose this fonte
        s_solucao.append(fonte_list[idx])

        # determine which targets are covered now
        covered_now = fonte_covers[idx] & uncovered
        if not covered_now:
            # nothing new covered by this selection, continue
            remaining[idx] = 0
            continue

        # For each newly covered target, decrement remaining counts of fontes that could cover it
        for t in covered_now:
            for fi in target_to_fontes[t]:
                if remaining[fi] > 0:
                    remaining[fi] -= 1
                    # push updated count to heap for lazy update
                    if remaining[fi] > 0:
                        heapq.heappush(heap, (-remaining[fi], fi))

        # remove covered targets from uncovered
        uncovered -= covered_now

    return s_solucao

if __name__ == "__main__":
    print("Gerando combinações")

    s15 = gerar_combinacoes(25, 15)

    s14 = gerar_combinacoes(25, 14)
    s13 = gerar_combinacoes(25, 13)
    s12 = gerar_combinacoes(25, 12)
    s11 = gerar_combinacoes(25, 11)

    print("Cobertura de 14")
    solucao_14 = cobertura(s15, s14)

    print("Cobertura de 13")
    solucao_13 = cobertura(s15, s13)

    print("Cobertura de 12")
    solucao_12 = cobertura(s15, s12)

    print("Cobertura de 11")
    solucao_11 = cobertura(s15, s11)
