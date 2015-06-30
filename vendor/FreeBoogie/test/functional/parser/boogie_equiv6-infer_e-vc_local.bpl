// equiv6.bpl

var Heap : [ref, name]int;
const FIELD : name;
var x : int, y : int, z : int;

procedure M(this : ref)
  modifies x, y, z;
{
  start:
    x := Heap[this, FIELD];
    y := Heap[this, FIELD];
    goto then,StartCheck,else;
  StartCheck:
    assert x == y && x == Heap[this, FIELD];
    return;

  then:
    y := 3;
    z := x;
    goto join,ThenCheck;
  ThenCheck:
    assert 3 == y && x == z && x == Heap[this, FIELD];
    return;

  else:
    z := Heap[this, FIELD];
    goto ElseCheck,join;
  ElseCheck:
    assert x == y && y == z && x == Heap[this, FIELD];
    return;

  join:
    // should not find: y==3 or: x==y or: x==z or: z==y
    assume x == z && x == Heap[this, FIELD];
    return;
}

procedure M0(this : ref)
  modifies x, y, z;
{
  start:
    x := Heap[this, FIELD];
    y := Heap[this, FIELD];
    goto then,else;
  then:
    y := 3;
    z := x;
    goto join;
  else:
    z := Heap[this, FIELD];
    goto join;
  join:
    // should not find: y==3 or: x==y or: x==z or: z==y
    assert y==3; // error
    return;
}

procedure M1(this : ref)
  modifies x, y, z;
{
  start:
    x := Heap[this, FIELD];
    y := Heap[this, FIELD];
    goto then,else;
  then:
    y := 3;
    z := x;
    goto join;
  else:
    z := Heap[this, FIELD];
    goto join;
  join:
    // should not find: y==3 or: x==y or: x==z or: z==y
    assert x==y; // error
    return;
}

procedure M2(this : ref)
  modifies x, y, z;
{
  start:
    x := Heap[this, FIELD];
    y := Heap[this, FIELD];
    goto then,else;
  then:
    y := 3;
    z := x;
    goto join;
  else:
    z := Heap[this, FIELD];
    goto join;
  join:
    // should not find: y==3 or: x==y or: x==z or: z==y
    assert x==z; // error
    return;
}

procedure M3(this : ref)
  modifies x, y, z;
{
  start:
    x := Heap[this, FIELD];
    y := Heap[this, FIELD];
    goto then,else;
  then:
    y := 3;
    z := x;
    goto join;
  else:
    z := Heap[this, FIELD];
    goto join;
  join:
    // should not find: y==3 or: x==y or: x==z or: z==y
    assert z==y; // error
    return;
}
