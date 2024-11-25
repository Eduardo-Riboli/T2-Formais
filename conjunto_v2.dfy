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
        ensures possui_elemento(elemento)
        ensures exists i :: 0 <= i < quantidade && elementos[i] == elemento
        ensures Conteudo == old(Conteudo) || Conteudo == old(Conteudo) + [elemento]
        ensures forall i :: i in old(Conteudo) ==> i in Conteudo
        ensures forall i, j :: 0 <= i < j < quantidade ==> elementos[i] != elementos[j]
        ensures old(!possui_elemento(elemento)) <==> Conteudo == old(Conteudo) + [elemento]
        ensures old(!possui_elemento(elemento)) <==> quantidade == old(quantidade) + 1
        ensures old(possui_elemento(elemento)) <==> Conteudo == old(Conteudo)
        ensures old(possui_elemento(elemento)) <==> quantidade == old(quantidade)
    {
        if possui_elemento(elemento) {
            // Garante que nada mudou quando o elemento já existe
            assert Conteudo == old(Conteudo);
            assert quantidade == old(quantidade);
            return;
        }

        var novoArranjo := new int[elementos.Length + 1];
        var i := 0;

        while i < elementos.Length
            invariant 0 <= i <= elementos.Length
            invariant novoArranjo.Length == elementos.Length + 1
            invariant forall k :: 0 <= k < i ==> novoArranjo[k] == elementos[k]
            invariant Conteudo == old(Conteudo)
            invariant Valid()
            invariant forall j :: 0 <= j < elementos.Length ==> elementos[j] == Conteudo[j]
        {
            novoArranjo[i] := elementos[i];
            i := i + 1;
        }

        novoArranjo[elementos.Length] := elemento;
        Conteudo := Conteudo + [elemento];
        quantidade := quantidade + 1;
        elementos := novoArranjo;
    }

    method Contem(elemento: int) returns (existe: bool)
        requires Valid()
        ensures Valid()
        ensures existe == (elemento in toSet(Conteudo))
        ensures !existe == !(elemento in toSet(Conteudo))
    {
        existe := possui_elemento(elemento);
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

    method Uniao(other: Conjunto) returns (result: Conjunto)
        requires Valid()
        requires other.Valid()
        ensures result.Valid()
        ensures forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) || x in toSet(other.Conteudo)
        ensures 0 <= result.quantidade <= quantidade + other.quantidade
        ensures forall x :: x in toSet(Conteudo) ==> x in toSet(result.Conteudo)
        ensures forall x :: x in toSet(other.Conteudo) ==> x in toSet(result.Conteudo)
        ensures fresh(result)
    {
        result := new Conjunto();
        assert result.Valid();

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
            invariant Valid()
            invariant result.quantidade <= quantidade + i
            invariant forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) || x in toSet(other.Conteudo)
            invariant forall j :: 0 <= j < i ==> other.elementos[j] in toSet(result.Conteudo)
            invariant forall x :: x in toSet(Conteudo) ==> x in toSet(result.Conteudo)
            invariant result.quantidade <= quantidade + other.quantidade
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
        ensures result.Valid()
        ensures forall x :: x in toSet(result.Conteudo) <==> x in toSet(Conteudo) && x in toSet(other.Conteudo)
        ensures fresh(result)
    {
        result := new Conjunto(); 

        var i := 0;
        while i < quantidade
            decreases quantidade - i
            invariant 0 <= i <= quantidade
            invariant result.Valid()
            invariant forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) && x in toSet(other.Conteudo)
            invariant forall j :: 0 <= j < i ==> (elementos[j] in toSet(result.Conteudo) <==> elementos[j] in toSet(other.Conteudo))
        {
            var elemento := elementos[i];
            if other.possui_elemento(elemento) {
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

        c1.Adicionar(2); // Tentando adicionar elemento duplicado
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

        assert toSet(c1.Conteudo) == {1, 2, 3};
        assert toSet(c2.Conteudo) == {4, 5, 6};

        c1.Adicionar(7);
        assert toSet(c1.Conteudo) == {1, 2, 3, 7};

        c1.Adicionar(3);
        assert toSet(c1.Conteudo) == {1, 2, 3, 7};

        assert |toSet(c1.Conteudo)| == 4;

        var c4 := new Conjunto();
        c4.Adicionar(7);
        c4.Adicionar(8);
        var c5 := c1.Uniao(c4);

        assert toSet(c5.Conteudo) == {1, 2, 3, 7, 8};
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
        assert c3.Valid();
        var expectedIntersection := {2, 3};
        assert toSet(c3.Conteudo) == expectedIntersection;

        // Testar interseção com nenhum elemento em comum
        var c4 := new Conjunto();
        c4.Adicionar(5);
        c4.Adicionar(6);

        var c5 := c1.Interseccao(c4);
        assert c5.Valid();
        assert toSet(c5.Conteudo) == {};

        // Testar interseção consigo mesmo
        var c6 := c1.Interseccao(c1);
        assert c6.Valid();
        assert toSet(c6.Conteudo) == toSet(c1.Conteudo);
    }
}