// The .jml initializer of j overflows (reported under --spec-math=safe) but still has a value,
// so RAC also compares that value with j and reports the mismatch (#774). ESC assumes the
// overflow away after reporting it, so it reports only the overflow.
public class A {
    int i = 11;
    int j = i + 5;
    public A() {}
    public static void main(String... a) { new A(); System.out.println("END"); }
}
