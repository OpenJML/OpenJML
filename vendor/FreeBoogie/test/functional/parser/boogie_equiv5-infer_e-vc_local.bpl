// equiv5.bpl

function $f (int) returns (int);
var x : int, y : int;

procedure M(this : ref)
  modifies x;
{
  start:
    x := 3;
    goto StartCheck, then, else;
  StartCheck:
    assert x == 3;
    return;

  then:
    x := $f(x);
    assume x == 3;
    goto ThenCheck, join;
  ThenCheck:
    assert x == 3 && x == $f(3);
    return;

  else:
    x := $f($f(x));
    assume x == 3;
    goto join, ElseCheck;
  ElseCheck:
    assert x == 3 && x == $f($f(3));
    return;

  join:
    // should find: x == $f($f(x)), but not: x == $f(x)
    assert x == 3 && x == $f($f(x));
    return;
}

procedure MPrime(this : ref)
  modifies x;
{
  start:
    x := 3;
    goto StartCheck, then, else;
  StartCheck:
    assert x == 3;
    return;

  then:
    x := $f(x);
    assume x == 3;
    goto ThenCheck, join;
  ThenCheck:
    assert x == 3 && x == $f(3);
    return;

  else:
    x := $f($f(x));
    assume x == 3;
    goto join, ElseCheck;
  ElseCheck:
    assert x == 3 && x == $f($f(3));
    return;

  join:
    // should find: x == $f($f(x)), but not: x == $f(x)
    assert x == $f(x);  // error
    return;
}
