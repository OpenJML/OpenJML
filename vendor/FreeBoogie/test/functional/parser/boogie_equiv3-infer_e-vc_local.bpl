// equiv3.bpl

function $f (int) returns (int);
var x : int, y : int;

procedure M(this : ref)
{
  start:
    goto then, else;

  then:
    assume x == $f(x);
    goto ThenCheck, join;
  ThenCheck:
    assert x == $f(x);
    return;

  else:
    assume x == $f($f(x));
    goto ElseCheck, join;
  ElseCheck:
    assert x == $f($f(x));
    return;

  join:
    // should find: x == $f($f(x));
    goto JoinCheck, Return;
  JoinCheck:
    assert x == $f($f(x));
    return;

  Return:
    return;
}
