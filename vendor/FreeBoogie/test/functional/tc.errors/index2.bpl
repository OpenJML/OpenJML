var heap : [ref, <x>name]x;
var r : ref;
var f : <ref>name;
var f' : <ref>name;

procedure a() returns (x : int)
{
  b1:
    x := heap[heap[r,f],f'];
    return;
}

