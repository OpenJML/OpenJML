var heap : [ref, <x>name]x;
var r : ref;
var f : <ref>name;

procedure a(x : int) returns (res : int)
  modifies heap, r;
//  requires x + 7;
  ensures x + 7;
{
  b1:
    return;
}

