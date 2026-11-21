// A .jml initializer gives the field's value at the end of initialization and must be pure;
// 'i - 1' states what 'i++' leaves in j (#774). Also guards against a spurious
// 'illegal forward reference' for 'int j = i - 1;' in A.jml.
public class A {
    static int si = 5;
    static int sj = si++;
    int i = 10;
    int j = i++;
    int k;
    { k = j + 1; }
    public A() { i = 0; } // runs after the comparison point
    public static void main(String... a) { new A(); System.out.println("END"); }
}
