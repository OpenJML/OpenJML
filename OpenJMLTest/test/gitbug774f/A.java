// The .jml initializer of j overflows (reported under --spec-math=safe) but still has a value,
// so ESC and RAC also compare that value with j and report the mismatch (#774)
public class A {
    int i = 11;
    int j = i + 5;
    public A() {}
    public static void main(String... a) { new A(); System.out.println("END"); }
}
