class Conjunto
{
    ghost var Conteudo: seq<int>

    var elementos: array<int>
    var quantidade: nat

    ghost predicate Valid()
        reads this, elementos
    {
        && 0 <= quantidade <= elementos.Length
        && (forall i, j :: 0 <= i < quantidade && 0 <= j < quantidade && i != j ==> elementos[i] != elementos[j])
        && Conteudo == elementos[0..quantidade]
    }

    // Obter conjunto a partir de sequência
    ghost function toSet(s: seq<int>): set<int>
    {
        set x | x in s
    }

    // Obter conjunto a partir de sequência até uma posição
    ghost function toSetPos(s: seq<int>, posicao: nat): set<int>
    {
        set i | 0 <= i < posicao < |s| :: s[i]
    }

    // Obter um elemento qualquer de um conjunto
    ghost function umElementoDo(s: set<nat>): (x: nat)
        requires |s| != 0
        ensures x in s
    {
        var x :| x in s;
        x
    }

    constructor()
        ensures Valid()
        ensures Conteudo == []
    {
        elementos := new int[10];
        quantidade := 0;
        Conteudo := [];
    }

    // Método para adicionar
    method Adicionar(elemento: int)
        requires Valid()
        requires elemento !in toSet(Conteudo)
        modifies this, elementos
        ensures Conteudo == old(Conteudo) + [elemento]
        ensures Valid()
    {
        // Redimensiona o array se necessário
        if quantidade == elementos.Length {
            var novoTamanho := if elementos.Length == 0 then 1 else elementos.Length * 2;
            var novoArray := new int[novoTamanho];

            forall i | 0 <= i < quantidade {
                novoArray[i] := elementos[i];
            }

            elementos := novoArray;
        }

        elementos[quantidade] := elemento;
        quantidade := quantidade + 1;
        Conteudo := Conteudo + [elemento];
    }

    // Método que verifica se o elemento contém ou não no conjunto
    method Contem(elemento: int) returns (existe: bool)
        requires Valid()
        ensures Valid()
        ensures existe == (elemento in toSet(Conteudo))
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

    // Método que diz a quantidade de elementos
    method QuantidadeElementos() returns (tamanho: nat)
        requires Valid()
        ensures tamanho == |Conteudo|
        ensures Valid()
    {
        tamanho := quantidade;
    }

    // Método que verifica se o conjunto está vazio
    method EhVazio() returns (vazio: bool)
        requires Valid()
        ensures vazio == (quantidade == 0)
        ensures Valid()
    {
        vazio := quantidade == 0;
    }

    // Método para remover
    method Remover(elemento: int) returns (removido: bool)
        requires Valid()
        requires |Conteudo| > 0
        requires elemento in Conteudo
        modifies this, elementos
        ensures removido ==> forall x :: x in Conteudo <==> x in old(Conteudo) && x != elemento
        ensures Valid()
    {
        removido := false;

        var indice := -1;
        for i := 0 to quantidade - 1
            invariant 0 <= i <= quantidade
            invariant Valid()
            invariant forall j :: 0 <= j < i ==> elementos[j] != elemento
        {
            if elementos[i] == elemento {
                indice := i;
                break;
            }
        }

        if indice == -1 {
            return;
        }

        // Atualizar Conteudo explicitamente
        Conteudo := Conteudo[0..indice] + Conteudo[indice + 1..];

        // Deslocar os elementos no array
        forall i | indice <= i < quantidade - 1 {
            elementos[i] := elementos[i + 1];
        }

        // Atualizar quantidade
        quantidade := quantidade - 1;
        removido := true;

        assert Valid();
    }

    // Método para unir dois conjuntos
    method Uniao(other: Conjunto) returns (result: Conjunto)
        requires Valid()
        requires other.Valid()
        ensures result.Valid()
        ensures forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) || x in toSet(other.Conteudo)
        ensures forall x :: x in toSet(Conteudo) ==> x in toSet(result.Conteudo)
        ensures forall x :: x in toSet(other.Conteudo) ==> x in toSet(result.Conteudo)
        ensures |toSet(result.Conteudo)| == |toSet(Conteudo) + toSet(other.Conteudo)|
        ensures Valid()
    {
        result := new Conjunto();
        var i := 0;

        while i < quantidade
            decreases quantidade - i
            invariant 0 <= i <= quantidade
            invariant result.Valid()
            invariant forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo)
            invariant forall j :: 0 <= j < i ==> elementos[j] in toSet(result.Conteudo)
        {
            assert result.Valid();
            assert elementos[i] !in toSet(result.Conteudo);
            //result.Adicionar(elementos[i]);
            i := i + 1;
        }

        i := 0;
        while i < other.quantidade
            decreases other.quantidade - i
            invariant 0 <= i <= other.quantidade
            invariant result.Valid()
            invariant forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) || x in toSet(other.Conteudo)
            invariant forall j :: 0 <= j < i ==> other.elementos[j] in toSet(result.Conteudo)
        {
            var elemento := other.elementos[i];
            if !(elemento in toSet(result.Conteudo)) {
                assert elemento !in toSet(result.Conteudo);
                // result.Adicionar(elemento);
            }
            i := i + 1;
        }
    }
}
