// heapaware0.bpl

var Heap : [ref, name]int;
const N : name;

procedure M(this : ref)
{
  var i : int, m : int;

  start:
    assume 0 <= Heap[this, N];
    i := 0;
    m := 0;
    goto StartCheck, body, end;

  StartCheck:
    assert 0 <= Heap[this, N] && i == 0 && m == 0;
    return;

  body:
    assume i < Heap[this, N];
    goto BodyCheck, then, else;
    then:
      m := i;
      goto ThenCheck,join;
    else:
      goto ElseCheck,join;
    join:
      i := i + 1;
      goto JoinCheck,body, end;

  BodyCheck:
    assert i < Heap[this,N] && 0 <= m && 0 <= i;
    return;
  ThenCheck:
    assert i < Heap[this,N] && 0 <= i && i == m;
    return;
  ElseCheck:
    assert i < Heap[this,N] && 0 <= m && 0 <= i;
    return;
  JoinCheck:
    assert i <= Heap[this,N] && 0 <= m && 1 <= i;
    return;

  end:
    return;
}
