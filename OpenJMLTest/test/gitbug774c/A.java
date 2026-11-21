// A .jml initializer is checked like any JML expression: here it divides by zero (#774)
public class A {
    int i = 11;
    int j = 0;
    public A() {}
    public static void main(String... a) { new A(); System.out.println("END"); }
}
