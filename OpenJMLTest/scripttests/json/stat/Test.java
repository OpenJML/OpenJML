public class Test {
  //@ public invariant I: true;
  public int m(boolean b) {
    int i = 0;
    i += 8;
    if (b) i = 7; else i = 9;
    if (!b) i = 17; // No else statement
    while (b) {
        if (i == 0) continue;
        if (i < 0) break;
    }
    ;
    assert true: "Always";
    assert false;
    try {} catch (Exception e) {}
    try (var r = new PrintStream();) {} finally {}
    synchronized (this) {}
    //@ loop_decreases 10-i;
    for (int i=0; i<10; i++) {}
    int[] a;
    for (var e: a) {}
    while (i<10) { i++; }
    do { i++; } while (i<20);
    //@ ghost \bigint j = 0;
    switch (5) { case 0: break; default: break;}
    Object o = (Integer)9;
    switch (o) { case String s when i > 0: break; default: }
    try {} catch (Exception e) {}
    @Nullable Object o = null;
    //@ havoc i, a;
    class CCC {}
    return i;
  }
  
}
