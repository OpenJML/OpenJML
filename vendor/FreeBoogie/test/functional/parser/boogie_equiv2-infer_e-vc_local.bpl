// equiv2.bpl

var Heap : [ref, name]int;
const FIELD : name;
var x : int, y : int, z : int;

procedure M(this : ref)
  modifies y, z;
{
  start:
    y := Heap[this, FIELD];
    z := Heap[this, FIELD];
    goto StartCheck, Return;
  StartCheck:
    assert y == Heap[this, FIELD] && z == y;
    return;

  Return:
    return;
}
