// equiv1.bpl

var x : int, y : int, z : int;

procedure M(this : ref)
  modifies y, z;
{
  start:
    y := x + 3;
    z := x + 3;
    goto CheckStart, Return;
  CheckStart:
    assert y == x + 3 && z == y;
    return;

  Return:
    return;
}
