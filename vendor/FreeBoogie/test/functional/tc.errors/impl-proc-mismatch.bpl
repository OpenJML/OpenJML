procedure p(x: int) returns (bool, int, rr : ref)
  requires x >= 0;
  ensures rr != null;

implementation p() returns (bool, int, rr : ref)
{
  b1:
    rr := null;
    return;
}
