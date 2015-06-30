// equiv4.bpl

function $f (int) returns (int);
var x : int, y : int;

procedure M(this : ref)
  modifies x, y;
{
  start:
    x := 3;
    goto StartCheck, then, else;
  StartCheck:
    assert x == 3;
    return;

  then:
    y := 3;
    goto ThenCheck, join;
  ThenCheck:
    assert x == 3 && y == 3;
    return;

  else:
    y := x;
    goto ElseCheck, join;
  ElseCheck:
    assert x == 3 && y == 3;
    return;

  join:
    assert x == 3 && y == 3;
    return;
}
