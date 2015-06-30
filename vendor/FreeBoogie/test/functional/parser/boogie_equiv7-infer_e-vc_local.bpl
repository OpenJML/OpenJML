// equiv7.bpl
//
// Test congruence closure.

function $f (int) returns (int);
var x : int, y : int, z : int;

procedure M(this : ref)
  modifies z;
{
  start:
    z := $f(x);
    z := $f(y);
    z := 3;
    assume x == y;
    assume z == $f(x);
    goto StartCheck, Return;
  StartCheck:
    assert y == x && z == 3 && z == $f(y);
    return;

  Return:
    return;
}
