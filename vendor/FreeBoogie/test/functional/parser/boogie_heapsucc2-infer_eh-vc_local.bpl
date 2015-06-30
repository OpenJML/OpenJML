// heapsucc2.bpl

var Heap : [ref, name]int;
const FIELD : name;
const OTHERFIELD : name;
var x : int, y : int, z : int;

procedure M(this : ref)
  modifies x, y, Heap;
{
  start:
    x := Heap[this, FIELD];
    goto StartCheck, then, else;

  StartCheck:
    assert x == Heap[this,FIELD];
    return;

  then:
    y := x;
    Heap[this, OTHERFIELD] := 2;
    goto ThenCheck, join;

  ThenCheck:
    assert y == x && x == Heap[this,FIELD] && Heap[this,OTHERFIELD] == 2;
    return;

  else:
    y := Heap[this, FIELD];
    goto ElseCheck,join;

  ElseCheck:
    assert y == x && x == Heap[this,FIELD];
    return;

  join:
    goto JoinCheck;

  JoinCheck:
    assert y == x && x == Heap[this,FIELD];
    return;
}
