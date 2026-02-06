import java.util.*;
public /*@ nullable_by_default @*/ class BinaryTree {

    Node root;

    private class Node { // FIXME - original problem: crashes when this class is not static
        Node left;
        Node right;
        int key;

        //logically in class Node, but cannot because Node can be null.
        /*@ pure @*/ static int size(Node n) {
            if(n==null) return 0;
            return(size(n.left)+1+size(n.right));
        }

        // Set of all keys that appear in the subtree below n.
        /*@ spec_pure non_null @*/ static TreeSet<Integer> ks(Node n) {
            if (n == null) return new TreeSet<Integer>();
            TreeSet<Integer> r = new TreeSet<Integer>();    //<Integer>(new Integer[]{(Integer)});
            r.add(n.key);
            r.addAll(ks(n.left));
            r.addAll(ks(n.right));
            return r;
        }
    }


    // invariant: a BinaryTree should be acyclic
    //@ model public \set<Integer> keyset;
    // represents keyset = this.keySet(); // no type conversion

    // Set of all keys that appear in the BinaryTree.
    public /*@ spec_pure non_null @*/
    TreeSet<Integer> keySet() {
        return Node.ks(root);
    }

    // Empty Binary Tree
    //@ pure
    BinaryTree() {
        root = null; //by default anyway
    }

    //Single-Node Binary Tree
    //@ pure
    BinaryTree(int r) {
        root = new Node();
        root.key = r; //left, right are null
    }

    //Usual constructor for Binary Tree: adds 1 node above existing ones.
    //@ pure
    BinaryTree(/*@ non_null @*/ BinaryTree left, /*@ non_null @*/ BinaryTree right, int r) {
        root = new Node();
        root.key = r;
        root.left = left.root;
        root.right = right.root;
    }

    /*@ requires depth >= 0;
@ measured_by depth;
@ also normal_behaviour
@ requires n == null;
@ ensures \result == (depth <= 1);
@ also normal_behaviour
@ requires n != null;
@ requires depth>0;
@ ensures \result == (allNullAtOrPred(n.left,depth-1)&&
allNullAtOrPred(n.right,depth-1));
@ also normal_behaviour
@ requires n != null;
@ requires depth == 0;
@ ensures \result == false;
pure @*/
    boolean allNullAtOrPred(Node n, int depth) {
        if (n == null) return (depth <= 1);
        else if (depth > 0)
            return allNullAtOrPred(n.left, depth - 1) &&
                    allNullAtOrPred(n.right, depth - 1);
        else return false;
    }

    /*@ ensures \result == (\exists int n;  n >= 0;
                         allNullAtOrPred(root,n));
        pure
      @*/
    boolean allNullAtNearlySameLevel() // l'argument est implicite dans la classe BinaryTree
    {
        return depthOfNull(root).size() <= 1;
    }

    ;

    private
    class Interval {
        /*@ spec_public */ int min;
        /*@ spec_public */ int max;

        //@ public normal_behavior
        //@   requires i <= j;
        //@   ensures min == i & max == j;
        //@ pure
        public Interval(int i, int j) {
            min = i;
            max = j;
        }
        // min > max means an empty interval. We suggest to normalize it to 1,0.
        //@ pure

        public int size() {
            if (max >= min) return max - min + 1;
            return 0;
        }

    } // end of class Interval -- henceforth nullable by default

    // returns the minimal interval of depth of occurrence of null pointers in the tree
    /*@ ensures \fresh(\result);
      @ ensures 0 <= \result.min <= \result.max;
      @ pure
        non_null */
    Interval depthOfNull(Node n) {
        if (n == null) return new Interval(0, 0);
        /*@ non_null */Interval ileft = depthOfNull(n.left);
        /*@ non_null */Interval iright = depthOfNull(n.right);
        return new Interval(1 + Math.min(ileft.min, iright.min), 1 + Math.max(ileft.max, iright.max));
    }

    public int size() {
        return Node.size(root);
    }


    public Object[] toArray() {
        return this.keySet().toArray();
    }

    /*@ requires a <= b;
      @ ensures Set.of(\result).equals(this.keySet().subSet(a,false,b,false));
        pure */
    public int[] between(int a, int b) {
        return btw(root, a, b);
    }


    Integer[] btwT(Node n, int a, int b) {
        return Node.ks(n).subSet(a,false,b,false).toArray(new Integer[0]);
    }
    /*@ requires a <= b;
      @ ensures Set.of(\result).equals(Node.ks(n).subSet(a,false,b,false));
        spec_pure @*/
    int[] btw(Node n, int a, int b) {
        if (n == null) return new int[0];
        if (a <= n.key && b <= n.key) return btw(n.left, a, b);
        if (a >= n.key && b >= n.key) return btw(n.right, a, b);
        // else the root key is in the interval
        int[] r1 = btw(n.left, a, b);
        int[] r2 = btw(n.right, a, b);
        int[] r = Arrays.copyOf(r1, r1.length + 1 + r2.length);
        r[r1.length] = n.key;
        for (int i = 0; i < r2.length; i++)
            r[r1.length + 1 + i] = r2[i];
        return r;
    }
}
