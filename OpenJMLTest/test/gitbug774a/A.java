// The .jml initializer of j disagrees with the value j has after initialization (#774)
public class A {
    int i = 10;
    int j = i++;
    public A() {}
    public static void main(String... a) { new A(); System.out.println("END"); }
}
