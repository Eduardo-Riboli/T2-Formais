class Conjunto {

  var arranjo : array<int>
  var tamanho : int

  ghost var Conteudo : seq<int>
  ghost var Repr : set<object>


  // ✅ "invariável da classe"
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {

    // Código padrão, peguei da doc
    this in Repr && null !in Repr
    && (arranjo != null ==> arranjo in Repr)

    // garantindo o "espelho" entre o arranjo e a sequência Conteudo que representa os valores do arranjo
    && arranjo.Length == |Conteudo|
    && forall i :: 0 <= i < arranjo.Length ==> arranjo[i] == Conteudo[i]
  }

  // ✅ Construtor aqui cria tudo zerado
  constructor()
    ensures Valid() && fresh(Repr)
    ensures Conteudo == []
    ensures arranjo.Length == 0
    ensures tamanho == 0
  {

    arranjo := new int[0];
    tamanho := 0;
    Conteudo := [];
    Repr := {this, arranjo};
  }

  // ✅
  method AdicionarElemento(x: int)
    requires Valid()
    requires x !in Conteudo
    modifies Repr
    ensures arranjo.Length == old(arranjo).Length + 1
    ensures Conteudo == old(Conteudo) + [x]
    ensures arranjo[old(arranjo).Length] == x
    ensures |Conteudo| == |old(Conteudo)| + 1
    ensures Valid()
    ensures this.Valid()

  {
    // Verifique se o elemento já está no conjunto
    var isIn := Pertence(x);
    if isIn {
      return;
    }


    var novoArranjo := new int[arranjo.Length + 1];

    var i := 0;
    while i < arranjo.Length
      invariant 0 <= i <= arranjo.Length
      invariant novoArranjo.Length == arranjo.Length + 1
      invariant Conteudo == old(Conteudo)
      invariant forall k :: 0 <= k < i ==> novoArranjo[k] == arranjo[k]
      invariant forall i :: 0 <= i < arranjo.Length ==> arranjo[i] == Conteudo[i]
      invariant Valid()
    {
      novoArranjo[i] := arranjo[i];
      i := i + 1;
    }

    novoArranjo[arranjo.Length] := x;
    Conteudo := Conteudo + [x];
    Repr := Repr - {arranjo} + {novoArranjo};
    Repr := Repr - {old(arranjo)} + {arranjo};
    arranjo := novoArranjo;

  }

  // ✅
  method Pertence(x: int) returns (r : bool)
    requires Valid()
    ensures r == (x in Conteudo)
    ensures r == (exists i :: 0 <= i < arranjo.Length && arranjo[i] == x)  // Corrigido para arranjo.Length
    ensures Valid()
  {
    var i := 0;
    while i < arranjo.Length
      invariant 0 <= i <= arranjo.Length
      invariant forall j :: 0 <= j < i ==> arranjo[j] != x
    {
      if arranjo[i] == x {
        return true;
      }
      i := i + 1;
    }
    return false;
  }

  // ✅
  method TamanhoConjunto() returns (count: int)
    requires Valid()
    ensures count == arranjo.Length
    ensures Valid()
  {
    return arranjo.Length;
  }

  // ✅
  method EhVazio() returns (result: bool)
    requires Valid()
    ensures result == (arranjo.Length == 0)
    ensures Valid()
  {
    result := (arranjo.Length == 0);
  }

  // ❌
  method uniao(c1: Conjunto, c2: Conjunto) returns (c3 : Conjunto)


  function Possui(e: int): bool
    reads this, arranjo
  {
    exists i :: 0 <= i < arranjo.Length && arranjo[i] == e
  }

  method Intersecao(c1: Conjunto, c2: Conjunto) returns (c3: Conjunto)
  //   requires Valid()
  //   requires c1.Valid()
  //   requires c2.Valid()
  //   modifies set x: object | x in {this, c1, c2}
  //   ensures Valid()
  //   ensures c1.Valid()
  //   ensures c2.Valid()
  //   ensures c3.Valid()
  //   ensures fresh (c3)
  //   ensures forall x :: x in c3.Conteudo <==> x in c1.Conteudo && x in c2.Conteudo
  //   ensures forall x :: x in c3.Conteudo <==> x in c1.Conteudo && x in c2.Conteudo
  // {
  //   c3 := new Conjunto();
  //   assert c3.Valid();

  //   var i := 0;
  //   while i < c1.arranjo.Length
  //     invariant 0 <= i <= c1.arranjo.Length
  //     // invariant forall j :: 0 <= j < i ==> c1.arranjo[j] in c1.Conteudo
  //     // invariant c_intersecao.Valid()
  //     // invariant Valid()
  //     // invariant c1.Valid()
  //     // invariant c2.Valid()
  //     // invariant forall x :: x in c_intersecao.Conteudo ==> x in c1.Conteudo && x in c2.Conteudo
  //   {
  //     // var pertence := c2.Possui(c1.arranjo[i]);
  //     if c2.Possui(c1.arranjo[i]) {
  //       c3.AdicionarElemento(c1.arranjo[i]);
  //     }
  //     i := i + 1;
  //   }

  // }

  ghost function Contem(e: int): bool
    reads this

  {
    e in Conteudo
  }

}



method Main()
  modifies set x: object | true
{
  var conjunto := new Conjunto();

  var isEmpty := conjunto.EhVazio();
  assert isEmpty == true;

  var size := conjunto.TamanhoConjunto();
  assert size == 0;

  conjunto.AdicionarElemento(14);

  var size2 := conjunto.TamanhoConjunto();
  assert size2 == 1;

  conjunto.AdicionarElemento(14);

  var pertence1 := conjunto.Pertence(14);
  assert pertence1 == true;

  var isEmpty2 := conjunto.EhVazio();
  assert isEmpty2 == false;

  conjunto.AdicionarElemento(2);

  conjunto.AdicionarElemento(3);

  var pertence2 := conjunto.Pertence(1);
  assert pertence2 == false;

  assert conjunto.Conteudo == [14,2,3];

  assert !conjunto.Contem(1);

  var c_dafny := {14,2,3};

  assert (set n : int | n in conjunto.Conteudo) == c_dafny;

}