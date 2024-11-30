valores = [1,2,3]

def getIndice(valor):

    index = -1
    i = 0

    while i < len(valores):
        if valores[i] == valor:
            index = i
            break
        i += 1
    
    indice = index

    return indice


def main():
    print(getIndice(1)) 

if __name__ == "__main__":
    main()