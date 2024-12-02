class Conjunto
{
    // ghost var Conteudo é um conjunto que representa o conteúdo do conjunto, utilizado para facilitar a verificação de propriedades
    ghost var Conteudo: seq<int>

    // Array de elementos do conjunto
    var elementos: array<int> 
    // Quantidade de elementos no conjunto
    var quantidade: nat 

    // Valid() que valida a cada iteração do loop ou ver que é valido o conjunto
    ghost predicate Valid()
        reads this, elementos
    {
        0 <= quantidade <= elementos.Length
        && (forall i, j :: 0 <= i < quantidade && 0 <= j < quantidade && i != j ==> elementos[i] != elementos[j])
        && Conteudo == elementos[0..quantidade]
        && elementos.Length == |Conteudo|
    }
    
    // Obter conjunto a partir de sequência
    ghost function toSet(s: seq<int>): set<int>
    {
        set x | x in s
    }

    // Verifica se o elemento está no conjunto
    function possui_elemento(e: int): bool
        reads this, elementos
    {
        exists i :: 0 <= i < elementos.Length && elementos[i] == e
    }

    lemma ConcatenandoDuasSequenciasUnicas(s1: seq<int>, s2: seq<int>)
        requires (forall i, j :: 0 <= i < |s1| && 0 <= j < |s1| && i != j ==> s1[i] != s1[j])
        requires (forall i, j :: 0 <= i < |s2| && 0 <= j < |s2| && i != j ==> s2[i] != s2[j])
        requires (forall i :: 0 <= i < |s1| ==> (forall j :: 0 <= j < |s2| ==> s1[i] != s2[j]))
        ensures (forall i, j :: 0 <= i < |s1 + s2| && 0 <= j < |s1 + s2| && i != j ==> (s1 + s2)[i] != (s1 + s2)[j])
    {
        // dafny consegue explicitamente resolver isso, serve mesmo para provar que as duas sequencias sao unicas
    }

    // Construtor do conjunto
    constructor()
        ensures Valid()
        ensures Conteudo == []
    {
        elementos := new int[0];
        quantidade := 0;
        Conteudo := [];
    }

    // Adicionar um elemento ao conjunto
    method Adicionar(elemento: int)
        requires Valid()
        modifies this
        ensures Valid() 
        ensures exists i :: 0 <= i < quantidade && elementos[i] == elemento 
        ensures forall i :: i in old(Conteudo) ==> i in Conteudo 
        ensures forall i, j :: 0 <= i < j < quantidade ==> elementos[i] != elementos[j]
        ensures old(!possui_elemento(elemento)) <==> Conteudo == old(Conteudo) + [elemento]
        ensures old(!possui_elemento(elemento)) <==> quantidade == old(quantidade) + 1
        ensures old(possui_elemento(elemento)) <==> Conteudo == old(Conteudo) 
        ensures old(possui_elemento(elemento)) <==> quantidade == old(quantidade)
        ensures elemento in Conteudo
    {
        if possui_elemento(elemento) {
            // Garante que nada mudou quando o elemento já existe
            assert Conteudo == old(Conteudo);
            assert quantidade == old(quantidade);
            return;
        }

        var novoElementos := new int[elementos.Length + 1];
        var i := 0;

        while i < elementos.Length
            invariant 0 <= i <= elementos.Length
            invariant novoElementos.Length == elementos.Length + 1
            invariant forall x :: 0 <= x < i ==> novoElementos[x] == elementos[x]
            invariant Conteudo == old(Conteudo)
            invariant Valid()
        {
            novoElementos[i] := elementos[i];
            i := i + 1;
        }

        novoElementos[elementos.Length] := elemento;
        quantidade := quantidade + 1;
        elementos := novoElementos;
        Conteudo := Conteudo + [elemento];

        assert Conteudo == old(Conteudo) + [elemento];
    }

    // Verificar se o conjunto contém um determinado elemento
    method Contem(elemento: int) returns (existe: bool)
        requires Valid()
        ensures Valid()
        ensures existe == (elemento in toSet(Conteudo))
        ensures !existe == !(elemento in toSet(Conteudo))
    {
        var i := 0;
        existe := false;

        while i < quantidade
            invariant 0 <= i <= quantidade
            invariant Valid()
            invariant existe == (exists j :: 0 <= j < i && elementos[j] == elemento)
            decreases quantidade - i
        {
            if elementos[i] == elemento {
                existe := true;
                break;
            }

            i := i + 1;
        }
    }

    // Verificar a quantidade de elementos do conjunto
    method QuantidadeElementos() returns (tamanho: nat)
        requires Valid()
        ensures tamanho == |Conteudo|
        ensures Valid()
    {
        tamanho := quantidade;
    }

    // verificar se o conjunto é vazio
    method EhVazio() returns (vazio: bool)
        requires Valid()
        ensures vazio == (quantidade == 0)
        ensures Valid()
    {
        vazio := quantidade == 0;
    }

    // obter o indice de um elemento
    method obterIndice(elemento:int) returns (indice:int)
        requires Valid()
        ensures Valid()
        ensures -1 <= indice < quantidade
        ensures indice != -1 <==> elemento in Conteudo
        ensures indice == -1 ==> elemento !in Conteudo
        ensures indice != -1 ==> elementos[indice] == elemento
        {
            var index := -1;
            var i:=0;

            while i < quantidade
                invariant 0 <= i <= quantidade
                invariant index == -1 ==> forall j :: 0 <= j < i ==> elementos[j] != elemento
                invariant index != -1 ==> 0 <= index < quantidade && elementos[index] == elemento
                decreases quantidade - i
                invariant Valid()
                invariant forall j :: 0 <= j < i ==> elementos[j] != elemento
            {
                if elementos[i] == elemento {
                    index := i;
                    break;
                }
                i := i + 1;
            }

            indice := index;
            assert indice == index;
            assert indice == -1 ==> !possui_elemento(elemento);
            assert indice != -1 ==> possui_elemento(elemento);
            assert Valid();
        }

    method Remover(elemento: int)
        requires Valid()
        modifies this
        ensures Valid()
        ensures old(possui_elemento(elemento)) ==> quantidade == old(quantidade) - 1
        ensures old(possui_elemento(elemento)) ==> !possui_elemento(elemento)
        ensures forall i :: i in old(Conteudo) && i != elemento ==> i in Conteudo
        ensures forall i :: i !in old(Conteudo) ==> i !in Conteudo
    {
        if !possui_elemento(elemento) {
            return;
        }

        var indiceParaRemover := obterIndice(elemento);
        assert indiceParaRemover != -1;

        var primeiraParte := elementos[0..indiceParaRemover];
        var segundaParte := elementos[indiceParaRemover + 1..quantidade];

        var novoConteudo := primeiraParte + segundaParte;
        var novoTamanhoLength := |novoConteudo|;

        // Usando lema para provar que a concatenação de sequências únicas é única
        ConcatenandoDuasSequenciasUnicas(primeiraParte, segundaParte);

        var novoElementos := new int[novoTamanhoLength];
        var k := 0;
        while k < novoTamanhoLength
            invariant 0 <= k <= novoTamanhoLength
            invariant forall i :: 0 <= i < k ==> novoElementos[i] == novoConteudo[i]
        {
            novoElementos[k] := novoConteudo[k];
            k := k + 1;
        }

        elementos := novoElementos;
        quantidade := novoTamanhoLength;
        Conteudo := novoConteudo;
    }

    // A união entre dois conjuntos
    method Uniao(other: Conjunto) returns (result: Conjunto)
        requires Valid()
        requires other.Valid()
        ensures result.Valid()
        ensures forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) || x in toSet(other.Conteudo)
        ensures toSet(result.Conteudo) == toSet(Conteudo) + toSet(other.Conteudo)
        ensures fresh(result)
    {
        result := new Conjunto();

        // Adicionar elementos do conjunto atual
        var i := 0;
        while i < quantidade
            decreases quantidade - i
            invariant 0 <= i <= quantidade
            invariant result.Valid()
            invariant Valid()
            invariant result.quantidade <= i
            invariant result.quantidade <= quantidade
            invariant forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo)
            invariant forall j :: 0 <= j < i ==> elementos[j] in toSet(result.Conteudo)
        {
            if !result.possui_elemento(elementos[i]) {
                result.Adicionar(elementos[i]);
            }

            i := i + 1;
        }

        // Adicionar elementos do outro conjunto
        i := 0;
        while i < other.quantidade
            decreases other.quantidade - i
            invariant 0 <= i <= other.quantidade
            invariant result.Valid()
            invariant other.Valid()
            invariant Valid()
            invariant forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) || x in toSet(other.Conteudo)
            invariant forall j :: 0 <= j < i ==> other.elementos[j] in toSet(result.Conteudo)
            invariant forall x :: x in toSet(Conteudo) ==> x in toSet(result.Conteudo)
        {
            var elemento := other.elementos[i];
            
            if !result.possui_elemento(elemento) {
                result.Adicionar(elemento);
            }
            
            i := i + 1;
        }
    }

    // A interseção entre dois conjuntos
    method Interseccao(other: Conjunto) returns (result: Conjunto)
        requires Valid()
        requires other.Valid()
        requires other.quantidade > 0
        requires quantidade > 0
        ensures forall x :: x in toSet(result.Conteudo) <==> x in toSet(Conteudo) && x in toSet(other.Conteudo)
        ensures result.Valid()
        ensures toSet(result.Conteudo) == toSet(Conteudo) * toSet(other.Conteudo)
        ensures Valid()
        ensures fresh(result)
    {
        result := new Conjunto();

        var i := 0;
        while i < quantidade
            decreases quantidade - i
            invariant 0 <= i <= quantidade
            invariant result.Valid()
            invariant Valid()
            invariant other.Valid()
            invariant forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) && x in toSet(other.Conteudo)
            invariant forall x :: 0 <= x < i && !result.possui_elemento(elementos[x]) && other.possui_elemento(elementos[x]) && possui_elemento(elementos[x]) ==> elementos[x] in toSet(result.Conteudo)
        {
            var elemento := elementos[i];

            // Adiciona o elemento à interseção se ele estiver nesse conjunto e no outro conjunto
            if other.possui_elemento(elemento) && possui_elemento(elemento) {
                if !result.possui_elemento(elemento) {
                    result.Adicionar(elemento);
                }
            }

            i := i + 1;
        }
    }

    // Métodos com todos os testes
    method TestAdicionar()
    {
        var c1 := new Conjunto();
        c1.Adicionar(1);
        c1.Adicionar(2);
        c1.Adicionar(3);
        assert c1.Valid();
        assert c1.Conteudo == [1, 2, 3];
        assert toSet(c1.Conteudo) == {1, 2, 3};

        var c2 := new Conjunto();
        c2.Adicionar(4);
        c2.Adicionar(5);
        c2.Adicionar(6);
        assert c2.Valid();
        assert c2.Conteudo == [4, 5, 6];
        assert toSet(c2.Conteudo) == {4, 5, 6};
    }

    method TestRemover() {
        var c1 := new Conjunto();
        c1.Adicionar(1);
        c1.Adicionar(2);
        assert c1.Valid();
        assert c1.Conteudo == [1, 2];
        var index := c1.obterIndice(1);
        assert c1.Valid();
        var temOuNao := c1.Contem(1);
        assert temOuNao == true;
        var posicao := c1.obterIndice(1);
        assert posicao != -1;
        assert posicao == 0;
        assert toSet(c1.Conteudo) == {1, 2};
        var posicao2 := c1.obterIndice(5);
        assert posicao2 == -1;
        var posicao3 := c1.obterIndice(2);
        assert posicao3 == 1;

        c1.Remover(1);
        assert c1.Valid();
        assert c1.Conteudo == [2];
    }

    method TestContem()
    {
        var c1 := new Conjunto();
        c1.Adicionar(1);
        c1.Adicionar(2);
        c1.Adicionar(3);

        var contem := c1.Contem(1);
        assert contem == true;

        var contem2 := c1.Contem(5);
        assert contem2 == false;
    }

    method TestQuantidadeElementos()
    {
        var c1 := new Conjunto();
        var tamanho := c1.QuantidadeElementos();
        assert tamanho == 0;

        c1.Adicionar(1);
        c1.Adicionar(2);
        c1.Adicionar(3);
        tamanho := c1.QuantidadeElementos();
        assert tamanho == 3;

        c1.Adicionar(1); // Tentando adicionar elemento duplicado
        assert c1.Valid();
        tamanho := c1.QuantidadeElementos();
        assert tamanho == 3; // Quantidade deve permanecer 3
    }

    method TestEhVazio()
    {
        var c1 := new Conjunto();
        var vazio := c1.EhVazio();
        assert vazio == true;

        c1.Adicionar(1);
        vazio := c1.EhVazio();
        assert vazio == false;

        c1.Adicionar(2);
        vazio := c1.EhVazio();
        assert vazio == false;
    }

    method TestUniao()
    {
        var c1 := new Conjunto();
        c1.Adicionar(1);
        c1.Adicionar(2);
        c1.Adicionar(3);

        var c2 := new Conjunto();
        c2.Adicionar(4);
        c2.Adicionar(5);
        c2.Adicionar(6);

        var c3 := c1.Uniao(c2);
        assert c3.Valid();
        var expectedUnion := {1, 2, 3, 4, 5, 6};
        assert toSet(c3.Conteudo) == expectedUnion;

        var c4 := new Conjunto();
        c4.Adicionar(7);
        c4.Adicionar(8);

        var c5 := c3.Uniao(c4);
        assert toSet(c5.Conteudo) == {1, 2, 3, 4, 5, 6, 7, 8};
    }

    method TestInterseccao()
    {
        var c1 := new Conjunto();
        c1.Adicionar(1);
        c1.Adicionar(2);
        c1.Adicionar(3);

        var c2 := new Conjunto();
        c2.Adicionar(2);
        c2.Adicionar(3);
        c2.Adicionar(4);

        var c3 := c1.Interseccao(c2);
        var expectedIntersection := {2, 3};
        assert toSet(c3.Conteudo) == expectedIntersection;
    }
}
