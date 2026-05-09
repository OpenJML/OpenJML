import org.jmlspecs.annotation.CodeBigintMath;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.NullableByDefault;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.annotation.SpecPure;
import org.jmlspecs.annotation.SpecBigintMath;

public class WFFBug {

    @SpecBigintMath @CodeBigintMath @NullableByDefault
    static class Node  {
        // Implememnts a simple singly-linked list, which ends when next_ is null
        // There is always one node (so is the length never 0? or is the payload of the first node ignored?)
        
        public @NonNull Object owner_;
        public @NonNull Object payload_; 
        public Node next_; 

        /*@ public normal_behavior 
        ensures owner_ == owner;
        ensures payload_ == payload;
        ensures next_ == next;
        */ 
        @Pure public Node(@NonNull Object owner, @NonNull Object payload, Node next) {
            owner_ = owner;
            payload_ = payload;
            next_ = next;
        }

        /*@ public normal_behavior 
            requires 0<=n;  

            assignable \nothing;
            ensures 0==n ==> \result==this;
            ensures 0<n && (\exists int i; 0 <= i < n; getf(i)==null) ==> \result == null;

            // BUG: This condition triggers a problem with \old(getf(n)) (error because of inability to parse AST).
            // Other attempts, e.g. to use a universal quantifier, or an existential in the antecedent
            // similarly trigger the error. << THis is fixed, but getf(n+1) violates the measured_by clause
            // and does not contibute anything because of the ensures clause above
//            ensures 0<n && \result == null ==> getf(n+1)==null;

            ensures 0<n && getf(n-1)!=null ==> \result == getf(n-1).next_;

            measured_by n;
        @*/
        @SpecPure
        public Node getf(final int n) {
            // Returns n'th node of list, or null if n is larger than length of list
            int i = 0;
            Node o = this;
	        /*@
                ghost Node prev=null;
          
                loop_invariant 0<=i; 
                loop_invariant i<=n; 
                loop_invariant n==0 ==> o == this;
                loop_invariant i< n ==> o==getf(i);
                loop_invariant 0<i ==> prev==getf(i-1);
                loop_invariant 0<i ==> prev!=null;
                loop_invariant 0<i ==> o==prev.next_;  

                decreases n-i;
            */
            while (i<n && o!=null) {
                //@ set prev = o;
                o=o.next_;
                i++;
            }
            
            return o;
        }

        // Just checking that \old is syntactically OK though semntically unnecessary
        /*@ public normal_behavior
            requires 0<=i;
            ensures getf(i)== \old(getf(i));
        */
        @SpecPure
        public void lemma_getf_wff(int i) {
        }

        // If i'th node is null, then if i<=j, j'th node is null 
        /*@ public normal_behavior
            requires 0<=i<=j;
            requires getf(i)==null;
            ensures getf(j)==null;
            measured_by j;
        */
        @SpecPure
        public void lemma_getf_aux(int i, int j) {
            if (i < j && 0 < j) {
                //@ assert getf(i) == null;
                lemma_getf_aux(i, j-1);
            }
        }
    }
}
