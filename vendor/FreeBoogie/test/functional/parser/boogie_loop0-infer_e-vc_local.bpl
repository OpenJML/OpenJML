// loop0.bpl  -- well, it's not really a loop

function $f (int) returns (int);
var x : int, y : int;

procedure M(this : ref)
{
  start:
    assume x == $f(x);
    goto StartCheck,head;
  StartCheck:
    assert x == $f(x);
    return;

  head:
    goto HeadCheck,body, end;
  HeadCheck:
    assert x == $f(x);
    return;

  body:
    goto BodyCheck,head;
  BodyCheck:
    assert x == $f(x);
    return;

  end:
    // should find: x == $f(x);
    assert x == $f(x);
    return;
}
