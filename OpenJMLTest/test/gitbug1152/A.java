// RAC reports an exception thrown by static initialization, from a field initializer or a static block (#1152)
public class A {
  public static void main(String... args) {
    try {
      System.out.println(B.I);
    } catch (ExceptionInInitializerError e) {
      System.out.println("B: " + e.getCause());
    }
    try {
      System.out.println(C.k);
    } catch (ExceptionInInitializerError e) {
      System.out.println("C: " + e.getCause());
    }
    System.out.println(D.I);
  }
}

class B {
  static int z = 0;
  public final static int I = 10 / z;
}

class C {
  static int[] a = new int[2];
  static int k;
  static { k = a[5]; }
}

class D {
  static int z = 2;
  public final static int I = 10 / z;
}
