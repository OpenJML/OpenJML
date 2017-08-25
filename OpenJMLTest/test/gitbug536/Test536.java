// Fails with rac - gitbug536 - this fails to compile (AssertionError) when run outside of Eclipse
public class Test536 {

  //@requires \forall int i; 0 <= i && i < array.length-1; array[i] <= array[i+1];
  public static void doesNothingButRequiresSorted(int[] array) {
  }

  public static void main(String[] args) {
    int[] array0 = {0,1,2,3};
    int[] array1 = {0,1,2,-3};

    // Succeeds
    doesNothingButRequiresSorted(array0);
    // Fails
    doesNothingButRequiresSorted(array1);
  }
}
