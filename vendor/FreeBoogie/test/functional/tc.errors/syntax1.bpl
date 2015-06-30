var heap : [ref, <x>name]x;
var r : ref;
var f : name;

procedure a() returns (x : int);
{
  b1:
    x := 7;
    return;
}

}

procedure b() returns (x : int);
{
  b1:
    // call x := a();
    x := a();
    return;
}

