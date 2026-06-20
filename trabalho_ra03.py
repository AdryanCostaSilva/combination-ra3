from itertools import combinations

# Geração das combinações
def gerar_combinacoes(universo, numElementos):
    return list(combinations(range(1, universo + 1), numElementos))

# Cobertura de n elementos
def cobertura(fonte, alvoCobertura): # alvoCobertura = s14, s13, s12 ou s11
    s_solucao = []
    return

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
