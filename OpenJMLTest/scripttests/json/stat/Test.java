public class Test {
  public int m(boolean b) {
    int i = 0;
    i += 8;
    if (b) i = 7; else i = 9;
    while (b) {
        if (i == 0) continue;
        if (i < 0) break;
    }
    ;
//    try {} catch (Exception e) {}
    return i;
  }
}
