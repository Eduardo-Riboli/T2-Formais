class Conjunto
{
    ghost var Conteudo: seq<int>
    ghost var Repr: set<object>

    var elementos: array<int>
    var quantidade: nat

    ghost predicate Valid()
        reads this, Repr
    {
        && this in Repr
        && elementos in Repr
        && 0 <= quantidade <= elementos.Length
        && (forall i, j :: 0 <= i < quantidade && 0 <= j < quantidade && i != j ==> elementos[i] != elementos[j])
        && Conteudo == elementos[0..quantidade]
    }

    // obter conjunto a partir de sequencia
    ghost function toSet(s:seq<int>) : set<int>
    {
        set x | x in s
    }

    // obter conjunto a partir de sequencia até uma posição
    ghost function toSetPos(s:seq<int>, posicao:nat): set<int>
    {
        set i | 0 <= i < posicao < |s| :: s[i]
    }

    // obter um elemento qualquer de um conjunto
    ghost function umElementoDo(s:set<nat>):(x:nat)
        requires |s| != 0
        ensures x in s
    {
        var x :| x in s; // atribuir tal que expressão para true
        x
    }

    constructor ()
        ensures Valid() && fresh(Repr)
        ensures Conteudo == []
    {
        elementos := new int[10];
        quantidade := 0;
        Conteudo := [];
        Repr := {this, elementos};
    }

    method Adicionar (elemento: int)
        requires Valid()
        requires elemento !in toSet(Conteudo)
        modifies Repr
        ensures Conteudo == old(Conteudo) + [elemento]
        ensures Valid() && fresh(Repr - old(Repr))
    {
        // Redimensiona o array se necessário
        if quantidade == elementos.Length {
            var novoTamanho := if elementos.Length == 0 then 1 else elementos.Length * 2;
            var novoArray := new int[novoTamanho];

            forall i | 0 <= i < quantidade {
                novoArray[i] := elementos[i];
            }   

            var old_elementos := elementos;
            elementos := novoArray;
            Repr := (Repr - {old_elementos}) + {elementos};
        }

        elementos[quantidade] := elemento;
        quantidade := quantidade + 1;
        Conteudo := Conteudo + [elemento];
    }
}