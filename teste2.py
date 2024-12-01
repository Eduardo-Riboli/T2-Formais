class Conjunto:
    def __init__(self, elementos):
        self.elementos = elementos
        self.quantidade = len(elementos)

    def obter_indice(self, elemento):
        """Obtém o índice do elemento no conjunto."""
        try:
            return self.elementos.index(elemento)
        except ValueError:
            return -1

    def remover(self, elemento):
        """Remove um elemento do conjunto."""
        removido = False

        # conteudo_inicial = self.elementos.copy()

        indice_para_remover = self.obter_indice(elemento)

        if indice_para_remover == -1:
            # Elemento não encontrado
            return removido

        novos_elementos = [0] * (len(self.elementos) - 1)
        index_atual = 0
        index_copia = 0

        while index_atual < self.quantidade and index_copia < len(novos_elementos):
            if indice_para_remover != index_atual:
                novos_elementos[index_copia] = self.elementos[index_atual]
                index_copia += 1
            index_atual += 1

        removido = True
        self.elementos = novos_elementos
        self.quantidade -= 1

        return removido


# Exemplo de uso
conjunto = Conjunto([1, 2, 3, 4, 5])
print("Antes:", conjunto.elementos)
removido = conjunto.remover(3)
print("Removido:", removido)
print("Depois:", conjunto.elementos)
