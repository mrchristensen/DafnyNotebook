method Max(a: int, b:int) returns (c: int)
  ensures c >= a
  ensures c >= b
{
  if a > b
  { return a; }
  return b;
}