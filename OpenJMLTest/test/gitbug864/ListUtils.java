public class ListUtils {
    //@ requires lst != null && lst.size() > 0;
    //@ ensures (\forall int i; 0 <= i && i < lst.size(); \result <= lst.get(i).size());
    //@ ensures (\exists int i; 0 <= i && i < lst.size(); \result == lst.get(i).size());
    public static int findMinLength(java.util.List<java.util.List<Integer>> lst) {
        if (lst == null || lst.isEmpty()) {
            throw new IllegalArgumentException("Input list must not be null or empty.");
        }
        int minLength = lst.get(0).size();
        for (int i = 1; i < lst.size(); i++) {
            int currentSize = lst.get(i).size();
            if (currentSize < minLength) {
                minLength = currentSize;
            }
        }
        return minLength;
    }

    public static void main(String... args) {
      var a = new java.util.ArrayList<java.util.List<Integer>>();
      var b = new java.util.ArrayList<Integer>();
      b.add(1); b.add(2);
      a.add(b);
      b = new java.util.ArrayList<Integer>();
      b.add(1);
      a.add(b);
      b = new java.util.ArrayList<Integer>();
      b.add(1); b.add(2); b.add(3);
      a.add(b);
      System.out.println(findMinLength(a));
    }
}
