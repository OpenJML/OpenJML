public class TestSets {
    public static void main(String[] args) {
        java.util.Set<Integer> seen = new java.util.HashSet<>();

        seen.add(10);
        seen.add(20);

        if (!seen.isEmpty()) {
            java.util.Iterator<Integer> iter = seen.iterator();
            //@ loop_modifies iter.*;
            while (iter.hasNext()) {
                int y = iter.next();
                java.util.Set<Integer> sMinusY = new java.util.HashSet<>(seen);
                sMinusY.remove(y);
            }
        }
    }
}
