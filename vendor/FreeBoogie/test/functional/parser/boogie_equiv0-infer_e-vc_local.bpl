// Initial test for equivalences

var x : int, y : int, z : int;

procedure M(this : ref)
  modifies x, y, z;
{
  start:
    x := 3;
    y := x;
    z := x;
    goto CheckStart, Return;
  CheckStart:
    assert x == 3 && y == 3 && z == 3;
    return;

  Return:
    return;
}
