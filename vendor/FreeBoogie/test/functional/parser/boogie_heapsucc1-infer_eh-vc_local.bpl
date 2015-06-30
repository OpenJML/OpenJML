// heapsucc1.bpl

var Heap : [ref, name]int;
const FIELD : name;
const OTHERFIELD : name;
var x : int, y : int, z : int;

procedure M(this : ref, that : ref)
  modifies y, z, Heap;
{
  start:
    y := Heap[this, FIELD];
    Heap[that, FIELD] := x;
    z := Heap[this, FIELD];
    goto StartCheck;

  StartCheck:
    assert x == Heap[that,FIELD] && z == Heap[this,FIELD];
    return;
}
