import org.jmlspecs.annotation.*;
public /*@ nullable_by_default @*/ class BinaryTree {

    Node root;

    private  class Node {
        Node left;
        Node right;
        int val;
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
        root.val = r; //left, right are null
    }

    //Usual constructor for Binary Tree: adds 1 node above existing ones.
    //@ pure
    BinaryTree(@NonNull BinaryTree left, @NonNull BinaryTree right, int r) {
        root = new Node();
        root.val = r;
        root.left = left.root;
        root.right = right.root;
    }
    /*@ 
      @ normal_behaviour
      @ requires depth >= 0;
      @ measured_by depth;
      @ requires n == null;
      @ ensures \result == (depth <= 1);
      @ also
      @ normal_behaviour
      @ requires n != null;
      @ requires depth>0;
      @ ensures \result == (allNullAtOrPred(n.left,depth-1)&& allNullAtOrPred(n.right,depth-1));
      @ also
      @ normal_behaviour
      @ requires n != null;
      @ requires depth == 0;
      @ ensures \result == false;
    pure @*/
    boolean allNullAtOrPred(Node n, int depth) {
        if(n == null) return (depth <= 1);
        else if(depth>0)
            return allNullAtOrPred(n.left,depth-1)&&
                    allNullAtOrPred(n.right,depth-1);
        else return false;
    }

    /*@ ensures \result == (\exists int n;  n >= 0;
                         allNullAtOrPred(root,n));
        pure
      @*/
    boolean allNullAtNearlySameLevel() 
    {return depthOfNull(root).size() <= 1;};

    private @NonNullByDefault
    class Interval {
        //@ public invariant min <= max + 1;
        /*@ spec_public */ int min;
        /*@ spec_public */ int max;

        //@ public normal_behavior
        //@   requires i <= j+1;
        //@   ensures min == i & max == j;
        //@ pure
        public Interval(int i, int j) {
            min = i;
            max = j;
        }
        // min > max means an empty interval. We suggest to normalize it to 1,0.
        //@ pure
        public int size() {
            if(max >= min) return max-min+1;
            return 0;
        }
    }
    /*@ pure
     */ @NonNull
    Interval depthOfNull(Node n) {
        if(n==null) return new Interval(0,0);
        Interval ileft = depthOfNull(n.left);
        Interval iright = depthOfNull(n.right);
        return new Interval(1+Math.min(ileft.min, iright.min),1+Math.max(ileft.max, iright.max));
    }
}
