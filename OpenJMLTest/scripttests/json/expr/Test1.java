class Test1 {
  int x1 = 4 + 6;
  int x2 = -x1;
  int x3 = true ? x1 : x2;
  int x4 = java.lang.Math.abs(x3);
  Object o = (java.lang.String)(((Integer)x1).toString());
  boolean b = o instanceof String;
  int z = switch (x1) { case 0 -> 5; default -> 10; };
}
