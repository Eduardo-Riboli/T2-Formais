class Conjunto
{
    ghost var Conteudo: seq<int>

    var elementos: array<int>
    var quantidade: nat

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

    function possui_elemento(e: int): bool
        reads this, elementos
    {
        exists i :: 0 <= i < elementos.Length && elementos[i] == e
    }

    constructor()
        ensures Valid()
        ensures Conteudo == []
    {
        elementos := new int[0];
        quantidade := 0;
        Conteudo := [];
    }

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
    }

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

    method QuantidadeElementos() returns (tamanho: nat)
        requires Valid()
        ensures tamanho == |Conteudo|
        ensures Valid()
    {
        tamanho := quantidade;
    }

    method EhVazio() returns (vazio: bool)
        requires Valid()
        ensures vazio == (quantidade == 0)
        ensures Valid()
    {
        vazio := quantidade == 0;
    }

    method Remover(elemento: int) returns (removido:bool)
        requires Valid()
        requires |Conteudo| > 0
        modifies this, elementos
        requires elemento in Conteudo
        ensures removido ==> forall x :: x in Conteudo <==> x in old(Conteudo) && x != elemento

    {
        removido := false;
        // Encontrar a posição do elemento no array
        ghost var ConteudoInicial := old(Conteudo);
        assert Conteudo == ConteudoInicial;

        var indice := -1;
            for i := 0 to quantidade - 1
            invariant 0 <= i <= quantidade
            invariant Valid()
            invariant Conteudo == ConteudoInicial
            invariant forall j :: 0 <= j < i ==> elementos[j] != elemento
            invariant (indice == -1 ==> forall j :: 0 <= j < i ==> elementos[j] != elemento) // Antes de encontrar o elemento
            invariant (indice != -1 ==> (0 <= indice < quantidade && elementos[indice] == elemento)) // Depois de encontrar o elemento
            invariant exists k :: 0 <= k < quantidade && elementos[k] == elemento // Garante que o elemento existe
        {
            if elementos[i] == elemento {
                assert i != -1;
                indice := i;
                assert i == indice;
                assert indice != -1;
                break;
            }
        }

        if indice == -1 
        {
            assert Conteudo == ConteudoInicial;
            return;
        }

        assert indice != -1; // Ensure we found the element

        Conteudo := Conteudo[0..indice] + Conteudo[indice + 1..];
        assert Conteudo == old(Conteudo)[0..indice] + old(Conteudo)[indice + 1..];

        // Shift elements in the array
        forall i | indice <= i < quantidade - 1 {
            elementos[i] := elementos[i + 1];
        }

        // Update quantity
        quantidade := quantidade - 1;

        // Reduz tamanho do array, se necessário
        if quantidade < elementos.Length / 4 && elementos.Length > 10 {
            var novoTamanho := elementos.Length / 2;
            var novoArray := new int[novoTamanho];

            forall i | 0 <= i < quantidade {
                novoArray[i] := elementos[i];
            }

            var old_elementos := elementos;
            elementos := novoArray;
        }
            // assert Valid();
            // Atualiza o conjunto
            var old_elementos := elementos;

            removido := true;

            // Garante que o conjunto continua válido
            // assert Valid();
    }

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

    method Main()
    {
        TestAdicionar();
        TestContem();
        TestQuantidadeElementos();
        TestEhVazio();
        TestUniao();
        TestInterseccao();
    }

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