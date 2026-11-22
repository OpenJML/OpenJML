// A .jml initializer must be pure (#774)
public class A {
    int i = 10;
    int j = i++;
    public A() {}
}
