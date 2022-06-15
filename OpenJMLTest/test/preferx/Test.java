public class Test {

  public void m(A a) {
    a.f = 0;
    a.g = 0; // g is defined in A.class, not A.java
    a.h = 0; // h is defined in A.java, not A.class
  }
}
