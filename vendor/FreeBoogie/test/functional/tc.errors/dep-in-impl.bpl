procedure p(x: int where x >= 0) returns (bool, int, rr : ref)
  requires x >= 0; // same as the dep type above
  ensures rr != null;

implementation p(y: int where y > 0) returns (bool, int, rr : ref)
{
  b1:
    rr := null;
    return;
}
