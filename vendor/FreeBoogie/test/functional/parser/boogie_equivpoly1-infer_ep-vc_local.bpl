// equivpoly1.bpl

function $f (int) returns (int);

procedure M()
{
  var i : int, n : int;

  start:
    i := 0;
    goto StartCheck,body;

  StartCheck:
    assert i == 0;
    return;

  body:
    assume i <= $f(n);
    goto BodyCheck,join;

  BodyCheck:
    assert i <= $f(n) && 0 <= i;
    return;

  join:
    i := i + 1;
    goto JoinCheck,body;

  JoinCheck:
    assert i <= $f(n) + 1 && 1 <= i;
    return;
}
