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

    // Método para adicionar
    method Adicionar (elemento: int)
        requires Valid()
        requires elemento !in toSet(Conteudo)
        modifies this, elementos
        ensures Conteudo == old(Conteudo) + [elemento]
        ensures Valid() 
        ensures fresh(Repr - old(Repr))
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

    // Metodo para remover
    method Remover(elemento: int) returns (removido: bool)
        requires Valid()
        requires |Conteudo| > 0
        modifies Repr
        requires elemento in Conteudo
        ensures removido ==> forall x :: x in Conteudo <==> x in old(Conteudo) && x != elemento
        ensures Valid() && fresh(Repr - old(Repr))

    {
        removido := false;
        // Encontrar a posição do elemento no array
        ghost var ConteudoInicial := old(Conteudo);
        assert Conteudo == ConteudoInicial;

        var indice := -1;
            for i := 0 to quantidade - 1
            invariant 0 <= i <= quantidade
            invariant Valid()
            invariant forall j :: 0 <= j < i ==> elementos[j] != elemento
            invariant (indice == -1 ==> forall j :: 0 <= j < i ==> elementos[j] != elemento) // Antes de encontrar o elemento
            invariant (indice != -1 ==> (0 <= indice < quantidade && elementos[indice] == elemento)) // Depois de encontrar o elemento
            invariant exists k :: 0 <= k < quantidade && elementos[k] == elemento // Garante que o elemento existe
            invariant Conteudo == ConteudoInicial

        {
            if elementos[i] == elemento {
                assert i != -1;
                indice := i;
                assert i == indice;
                assert indice != -1;
                break;
            }
            
        }

        if indice == -1 {
            assert Conteudo == ConteudoInicial;
            return;
        }

        assert indice != -1; // Ensure we found the element

        // Update Conteudo explicitly
        Conteudo := Conteudo[0..indice] + Conteudo[indice + 1..];
        assert Conteudo == old(Conteudo)[0..indice] + old(Conteudo)[indice + 1..];

        // Shift elements in the array
        forall i | indice <= i < quantidade - 1 {
            elementos[i] := elementos[i + 1];
        }

        // Update quantity
        quantidade := quantidade - 1;

        removido := true;
        // Ensure Valid() holds
        assert Valid();
    }

    // Método para unir dois conjuntos
    method Uniao(other: Conjunto) returns (result: Conjunto)
        requires Valid()
        requires other.Valid()
        ensures result.Valid()
        ensures fresh(result)
        ensures forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) || x in toSet(other.Conteudo)
        ensures forall x :: x in toSet(Conteudo) ==> x in toSet(result.Conteudo)
        ensures forall x :: x in toSet(other.Conteudo) ==> x in toSet(result.Conteudo)
        ensures |toSet(result.Conteudo)| == |toSet(Conteudo) + toSet(other.Conteudo)|
    {
        result := new Conjunto(); // Criação local de result
        var i := 0;

        // Adicionar elementos do conjunto atual
        while i < quantidade
            decreases quantidade - i
            invariant 0 <= i <= quantidade
            invariant result.Valid() // Garante que result permanece válido
            invariant forall x :: x in toSet(result.Conteudo) ==> x in toSet(Conteudo) // Elementos de result estão em Conteudo
            invariant forall j :: 0 <= j < i ==> elementos[j] in toSet(result.Conteudo) // Elementos até índice i estão em result
        {
            assert result.Valid(); // Confirma que result é válido antes de Adicionar
            assert elementos[i] !in toSet(result.Conteudo); // Confirma pré-condição de Adicionar
            // result.Adicionar(elementos[i]); // Chamada ao método Adicionar
            i := i + 1;
        }


        // Adicionar elementos do outro conjunto
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


    // Método para intersecção
    // method Interseccao(other: Conjunto) returns (result: Conjunto)
    //     requires Valid()
    //     requires other.Valid()
    //     requires other.elementos.Length > 0
    //     requires elementos.Length > 0
    //     ensures result.Valid()
    //     ensures fresh(result)
    //     ensures Valid()
    //     ensures forall x :: x in toSet(result.Conteudo) <==> x in toSet(Conteudo) && x in toSet(other.Conteudo)
    // {
    //     result := new Conjunto();

    //     var i := 0;
    //     while i < elementos.Length
    //         invariant 0 <= i <= elementos.Length
    //         invariant result.Valid()
    //         invariant Valid()
    //         invariant other.Valid()
    // }


    // Método Main para testar a classe Conjunto
    method Main()
    {
        var conjunto := new Conjunto();

        // Teste do método Adicionar
        conjunto.Adicionar(10);
        conjunto.Adicionar(20);
        conjunto.Adicionar(30);

        var elementos := conjunto.QuantidadeElementos();
        assert elementos == 3;

        // Tentar adicionar um elemento já existente
        // Deverá falhar devido à pré-condição (elemento não está em Conteudo)
        // Portanto, devemos verificar se o elemento existe antes
        var existe := conjunto.Contem(20);
        if !existe {
            conjunto.Adicionar(20);
        } else {
            // Não adiciona, pois já existe
        }
        elementos := conjunto.QuantidadeElementos();
        assert elementos == 3;

        // Teste do método Contem
        existe := conjunto.Contem(20);
        assert existe == true;

        existe := conjunto.Contem(40);
        assert existe == false;

        // Teste do método EhVazio
        var vazio := conjunto.EhVazio();
        assert vazio == false;

        // Teste do método Remover
        // conjunto.Remover(20);
        // elementos := conjunto.QuantidadeElementos();
        // assert elementos == 2;
        // existe := conjunto.Contem(20);
        // assert existe == false;

        // Remover elementos restantes
        // conjunto.Remover(10);
        // conjunto.Remover(30);
        // assert conjunto.EhVazio() == true;

        // Teste de remover de um conjunto vazio
        // Como a pré-condição exige que o elemento esteja no conjunto, precisamos verificar

        // var vinte := conjunto.Remover(20);
        // assert vinte == true;

        var conjunto2 := new Conjunto();
        conjunto2.Adicionar(10);
        conjunto2.Adicionar(20);
        conjunto2.Adicionar(30);

        var tamanhoConjunto := conjunto.QuantidadeElementos();
        var tamanhoConjunto2 := conjunto2.QuantidadeElementos();
        assert tamanhoConjunto == tamanhoConjunto2;
        // assert conjunto.EhVazio() == true;

        // Adicionar novamente elementos
        // conjunto.Adicionar(50);
        // conjunto.Adicionar(60);
        // assert conjunto.QuantidadeElementos() == 2;

        // Teste finalizado
    }
}