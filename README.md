# Implementação do Tipo Abstrato de Dados "Conjunto" em Dafny

**Descrição**  
Este projeto consiste na implementação do tipo abstrato de dados **Conjunto** utilizando arrays na linguagem Dafny, com verificação formal e especificação de pré-condições, pós-condições, invariantes e variantes.

---

## Funcionalidades Implementadas

- **Construtor**: Instancia um conjunto vazio.  
- **Adicionar Elemento**: Adiciona um novo elemento ao conjunto.  
- **Remover Elemento**: Remove um elemento específico do conjunto.  
- **Verificar Elemento**: Verifica se um determinado elemento pertence ao conjunto.  
- **Número de Elementos**: Retorna o número de elementos no conjunto.  
- **Verificar Vazio**: Confere se o conjunto está vazio.  
- **União de Conjuntos**: Realiza a união de dois conjuntos, retornando um novo conjunto sem alterar os originais.  
- **Interseção de Conjuntos**: Realiza a interseção entre dois conjuntos, retornando um novo conjunto sem modificar os originais.  

---

## Pré-requisitos

- **Dafny** deve estar instalado.  
  Para mais informações, acesse: [Instalação do Dafny](https://dafny.org/dafny)  

---

## Estrutura do Projeto

```markdown
📦 projeto-conjunto-dafny
├── 📄 conjunto.dfy         # Implementação da classe Conjunto e métodos
├── 📄 main.dfy             # Método principal para testes e verificação
└── 📄 README.md            # Documentação do projeto
