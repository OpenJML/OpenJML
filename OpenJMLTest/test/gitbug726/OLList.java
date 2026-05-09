import org.jmlspecs.annotation.CodeBigintMath;
import org.jmlspecs.annotation.Helper;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.NullableByDefault;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.annotation.SpecPure;
import org.jmlspecs.annotation.SpecBigintMath;

public class OLList {

 /**
  * Comments to help people understand the proofs below. I had a lot of
  * difficulty getting things to work. The OpenJML reference manual needs work.
  * Various JML features are not (yet) implemented. (See pdf in docs directory.)
  * Crucially, for the current task (proving properties of linked list
  * structures), dynamic frames are not available. Thus it is not possible to
  * define a location set based on a reachability predicate (e.g. all Nodes
  * accessible via next fields). To be clear JML provides several mechanisms --
  * reachability predicates, map operations for locaiton sets, ownership types.
  * OpenJML does not currently implement these mechanisms.
  * 
  * This makes it is very easy to get openjml to generate large formulas to send
  * out to Z3 which can take an unbounded amount of time to process. (I have had
  * Z3 server crashes after a few hours ...). Ming Kawaguchi pointed me to some
  * nice papers by Rustan on the "butterfly effect" -- these appear to be
  * re-workings in this context of 40 year old (at least) issues of control in
  * logic....
  * 
  * Ultimately I was able to settle on a methodology that should work in practice
  * for most programmers. It relies, for now, on working through the proofs
  * essentially manually. Try to use simple unquantified formulas in the
  * specification of code. You may use quantifiers in lemmas, here too it helps
  * to work with unquantified versions where possible. Procedure definitions
  * effectively provide an "open" definition since they can be "instantiated" for
  * any value of their parameters. The drawback is you have to specify values for
  * these parameters at point of use. Of course inference to automatically derive
  * these values (cf Scala implicits) would be great. Also good would be to
  * implement a proper programming model for managing proofs and proof search,
  * not quite Coq but like, say in Imandra.
  * 
  * Below, several proof lines are written with a space after the //, as in // @
  * <proof line>. These are comments. The lines that start with //@ are actual
  * parts of the proof for OpenJML. I do this to record the full proof (remove
  * the spaces to include the commented lines in the proof)
  * 
  * The idioms below are based loosely on the paper: "Specifying linked data
  * structures in JML for combining formal verification and testing", by
  * Christoph Gladisch and Shmuel Tyszberowicz, Science of Computer Programming,
  * Feb 2015.
  */
 @SpecBigintMath
 @CodeBigintMath
 @NullableByDefault
 static class Node {

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
      ensures owner_ == owner;
      ensures payload_ == payload;
      ensures next_ == null;
    */ 
    @Pure public Node(@NonNull Object owner, @NonNull Object payload) {
        owner_ = owner;
        payload_ = payload;
        next_ = null;
    }

    /**
     * See also agetf for a version that works wit toSeq() generated arrays. Found
     * it easier to work with agetf when establishng the size of suffixes of a given
     * list, after modification of an element. There should be some nice way of
     * combning the two forms.
     */
    // ok 4/7
    /*@ public normal_behavior 
        requires 0<=n;  

        assignable \nothing;
        ensures 0==n ==> \result==this;
        ensures 0<n && getf(n-1)==null ==> \result==null;
        ensures 0<n && \result==null ==> getf(n+1)==null;  // stability of null. See 
        ensures 0<n && getf(n-1)!=null ==> \result==getf(n-1).next_;
        measured_by(n);
    @*/
    @SpecPure
    public Node getf(final int n) {
      int i = 0;
      Node o = this;
	    /*@
          ghost Node prev=null;
          
          loop_invariant 0<=i; 
          loop_invariant i<=n; 
          loop_invariant o==getf(i);
          loop_invariant 0<i ==> prev==getf(i-1);
          loop_invariant 0<i ==> prev!=null;
          loop_invariant 0<i ==> o==prev.next_;  
          // loop_invariant (\forall int j;0<=j<i; getf(j)!=null); 
          loop_invariant o==null ==> i>0;
          decreases n-i;
         */
      while (i < n && o != null) {
          //@ set prev = o;
        o = o.next_;
        i++;
      }
       
      // This is the missing gap.
      // @ assert o==null ==> getf(n-1)==null;
      // @ assert i<n ==> getf(i) == null;
      if (i < n)
        lemma_getf_aux(i, n);
      // @ assert i<n ==> (\forall int j; i<=j<=n; getf(j)==null);
      // @ assert 0<n && getf(n-1)!=null ==> o == getf(n-1).next_;
      return o;
    }
    /**
     * This checks whether getf can be used in \old. With the 
     * current implenentation of OpenJML this gives a parsing(?!@$) 
     * error. See bug report on \old, #725.
     * error: ESC could not be attempted because of a failure in typechecking or AST transformation: lemma_getf_wff
     * @param i
     */
    /* public normal_behavior
      requires 0<=i;
      ensures getf(i)== \old(getf(i));
    
    @Pure public void lemma_getf_wff(int i){}
    */

    //ok 4/7
    /*@ public normal_behavior
        requires 0<=i;
        // This formulation is critical, solver will use contrapositive forms as appropriate.
        //e.g. getf(i) or getf(j) could be non-null, it will conclude j<i as well.
        ensures i<=j ==> getf(i)==null ==> getf(j)==null; 
    */
    @SpecPure
    public void lemma_getf_aux(int i, int j) {
       //if (i<j && getf(i)==null) {
          lemma_getf_aux(i, j-1);
       // }
    }


    /*@ public normal_behavior
      ensures getf(1) == next_;
      */
     @Pure
     public void lemma_getf_basics() {}


    //ok 4/7
    /**
     * An interesting example of how a complex inductive proof can be 
     * specified by the OpenJML programmer. 
     * Note the termination caveat, though. (See OpenJML issue #724)
     * @param i
     * @param j
     */
    /*@ public normal_behavior
      requires 0<=i;
      requires 0<=j;
      requires getf(i)!= null;
      ensures  getf(i+j)==getf(i).getf(j);  
      */
    @Pure
    public void lemma_getf_sum(int i, int j) {
      if (getf(i) == null) {
        lemma_getf_aux(i, i + j);
      }
      if (0<i && getf(i) != null) {
        lemma_getf_aux(1, i);
        lemma_getf_sum(1, i - 1);
         //@ assert getf(i) == getf(1).getf(i-1);
         //@ assert getf(i).getf(j) == getf(1).getf(i-1).getf(j);
          getf(1).lemma_getf_sum(i-1,j);
         //@ assert getf(1).getf(i-1).getf(j) == getf(1).getf(i+j-1);
         lemma_getf_sum(1, i+j-1);
         //@ assert getf(1).getf(i+j-1) == getf(i+j);
      }    
    }

    //ok 4/7
    /*@ public normal_behavior 
      ensures (\forall int i; 0<=i; getf(i)==(i==0?this:next_==null?null:next_.getf(i-1)));
    */
    @Pure public void lemma_getf_ind() {
        //@ assert (\forall int i; 1<=i;getf(i)==alt_getf(i));
    }

    /**
     * As long as i is in bounds, get will not return null.
     * @param i -- the desired element in the list.
     */
    /*@ public normal_behavior
      requires 0<=i<size();
      ensures  getf(i)!=null;
    */
    @Pure public void lemma_getf_nonnull(int i){
      //@ assert i<size();
      //@ assert getf(size()-1)!=null;
      lemma_getf_aux(i, size()-1);
    }

    /**
     * An alternate specification easier to use in places where induction is needed.
     * @param i -- the desired element in the list.
     */
    //ok, ~2s 
    /*@ public normal_behavior 
        requires 0<=n;  
        ensures (\forall int i; 1<=i;alt_getf(i)==(next_==null?null:next_.alt_getf(i-1)));
        ensures (\forall int i;0<=i; alt_getf(i)==getf(i)); 
    @*/
    @SpecPure public Node alt_getf(final int n) {
        if (n==0) return this;
        if (next_==null) return null;
        return next_.getf(n-1);
    }

    /**
     * Return the size of this list.
     * Note: Lack of termination detectionin OpenJML, Issue #724.
     * @return size of the list.
     * 
     * Interesting lemmas:
     *   ensures \result == 1 + (next_==null? 0: next_.size());             // 3 lemma_size_ind new 3/28
         ensures (\forall int j; 0<=j<\result; \result==j+getf(j).size());  // 4 lemma_getf_size new 3/28
     */
        /*@ public normal_behavior 
        //requires (\exists int i; 0<i && getf(i-1)!=null && getf(i)==null);
         ensures 0<\result;
        ensures getf(\result-1)!=null; //1-simple
        ensures getf(\result)==null;  //2
        @*/
    @SpecPure public int size() {
        // TODO: There is no guarantee of termination. This needs an extra assumption.
        int i=1;
        /*@ 
          loop_invariant 1<=i; 
          loop_invariant (\forall int ii; (1<=ii && ii<i); getf(ii) != null);
          //loop_invariant size()==i-1+getf(i-1).size();
         */
        while (getf(i) != null)
            i++;
        return i;
    } 

      /*@ public normal_behavior 
         ensures \result == size();   
      */
      @Pure
      public int alt_size() {
        int i=1;
        @Nullable Node next = next_;
        /*@
            ghost Node prev=this;
            loop_invariant 1<=i; 
            loop_invariant next == getf(i);
            loop_invariant 0<i ==> prev==getf(i-1);
            loop_invariant 0<i ==> prev!=null;
           // loop_invariant size() == i + (next==null?0:next.size());
        */
        while (next != null) {
          i++;
          //@ set prev = next;
          next = next.next_;
        }
        //@ assert getf(i-1)!=null;
        //@ assert getf(i)==null;
        lemma_size_iff(i);
        return i;
      } 

    
    /**
     * states a uniqueness property: Any n s.t. getf(n-1) is not null and getf(n)
     * is null must be equal to the length.
     */
    // ok, ~2s
    /*@ public normal_behavior
      requires 0<i;
      ensures (getf(i-1)!=null && getf(i)==null) ==>  size()==i;
    */
    @Pure public void lemma_size_iff(int i){
      if (getf(i-1) !=null && getf(i)==null) {
      // @ assert getf(size()-1) !=null;
      // @ assert getf(size()) == null;
      lemma_getf_aux(i,size()-1);
      // @ assert size()-1<i;
      lemma_getf_aux(size(), i-1);
       // @ assert i-1<size();
       // @ assert i-1<size()<i+1;
       // @ assert i==size();
    }
    }
    
     
     // ok, ~2s
    /*@ public normal_behavior
      requires 0<=j<size();
      ensures getf(j).getf(size()-j-1)!=null && getf(j).getf(size()-j)==null;
     */
    @Pure public void lemma_suffix_size(int j){
        lemma_getf_nonnull(j);
        lemma_getf_sum(j, size()-j-1);
        // @ assert getf(j).getf(size()-j-1)==getf(size()-1);
        // @ assert getf(j).getf(size()-j-1) != null;
        lemma_getf_sum(j, size()-j);
        // @ assert getf(j).getf(size()-j)==getf(size());
         // @ assert getf(j).getf(size()-j)==null;
    }
    
    /**
     * Key lemma. Asserts the the size of getf(j) (where j is bounded by size()) is just
     * size()-j.
     * @param j
     */
    // ok, ~10s 4/3
    /*@ public normal_behavior
       requires 0<=j<size();
       ensures  getf(j).size()==size()-j;
    */
    @Pure public void lemma_getf_size(int j){
        lemma_getf_basics();
        lemma_getf_nonnull(j);
        lemma_suffix_size(j);
        int z = size()-j;
        //@ assert getf(j).getf(z-1)!=null;
        //@ assert getf(j).getf(z)==null;
        getf(j).lemma_size_iff(z);
       
    }

    // ok, ~2s 
    /*@ public normal_behavior
       ensures size()==(1+(next_==null?0:next_.size()));
    */
    @Pure public void lemma_size_ind(){
        //@ assert size()==alt_size();
        lemma_getf_basics();
        if (next_ != null) {
            lemma_getf_size(1);
            //@assert size()==1+next_.size();
        } else {
          lemma_size_iff(1);
        }
    }

    // ok, ~4s
    /*@ public normal_behavior 
        ensures \result.length==items.length+1;
        ensures \result[0]==getf(0);
        ensures (\forall int i; 1<=i<items.length+1; \result[i]==items[i-1]);
    */
   @Pure public @NonNull Node @NonNull [] append(@NonNull Node @NonNull [] items) {
       @NonNull Node @NonNull [] result = new Node[items.length+1];
        result[0]=this;
        //@ assert items.length >= 0;
        //@ assert result.length == items.length + 1;
        //@ assert result != null;
        System.arraycopy(items, 0, result, 1, items.length);
        return result;
    }

      // ok
    /*@ public normal_behavior 
        ensures \result.length==prefix.length+suffix.length;
        ensures (\forall int i; 0<=i<prefix.length; \result[i]==prefix[i]);
        ensures (\forall int i; prefix.length<=i<prefix.length+suffix.length; \result[i]==suffix[i-prefix.length]);
    */
    @Pure
    public static @NonNull Node[] concat(@NonNull Node[] prefix, @NonNull Node[] suffix) {
        final @NonNull Node[] result = new Node[prefix.length + suffix.length];
        System.arraycopy(prefix, 0, result, 0, prefix.length);
        System.arraycopy(suffix, 0, result, prefix.length, suffix.length);
        return result;
    }
   
    // ok, quick proof (~2s)
    // With getf(1,2,4):
    // Note that we need the longer form of the body because we now need to
    // add lemma_getf_ind() in the right places, since it is not ensured by
    // getf but established separately. 

    // 4/4 The code below represents anattempt to merge in reasoning about size when a ghost array is
    // available. I have since found it clearer to separate out this capability into agetf. 
    // TODO: Remove the last ensure.
    /**
     * @param size
     * @return array a (a.length==size).
     */
     /*@ public normal_behavior
      requires 0<=z<=size(); 
      ensures \result.length==z;
      ensures (\forall int i; 0<=i<z;\result[i]==getf(i));
      ensures (\forall Node[] e; e.length==z&&(\forall int i; 1<=i<z; e[i]==\result[i]);
                   (\forall int i; 1<=i<z;\result[i]==\result[1].getf(i-1))); // new 04/04 for insert
    */
    @Pure public @NonNull Node[] prefixToSeq(int z) {
        // Note, this looks pretty, but keeping the expanded out version 
        // since that was critical to debugging the proof.
        //return (size==0) ? new Node[0] : append(next_==null ? new Node[size - 1] : next_.prefixToSeq(size - 1));
        
        if (z==0)
            return new Node[0];
        if (next_ == null) {
            Node[] r = append(new Node[z-1]);
            lemma_getf_ind();
            return r;
        }
        //@assert next_ != null;
        lemma_size_ind();
        //@assert next_.size()==size()-1;
        // @assert z-1<=next_.size();
        Node[] r = next_.prefixToSeq(z-1);
        lemma_getf_ind(); 
        return append(r);
        
    }

    // ok, ~2s
    // 13s with getf (1,2,4) and size(1,2,3,4)
    // got rid of clause that requires an i s.t. getf(i-1)!=null && getf(i)==null.
    // Helps to have the version with a single occurrence of size()
    // 9s with getf (1,2,4) and size(1-simple, 2)
    /*@ public normal_behavior
      ensures \result.length==size();
      ensures (\forall int i; 0<=i<size(); \result[i]==getf(i));
      ensures (\forall Node[] e; e.length==size()&&(\forall int i; 1<=i<size(); e[i]==\result[i]);
                   (\forall int i; 1<=i<size();\result[i]==\result[1].getf(i-1))); // new 04/04 for insert
       
    */
    @Pure public @NonNull Node[] toSeq() {
       return prefixToSeq(size());
    }

     // ok, ~3s
    /*@ public normal_behavior
      requires toSeq()==seq;
      requires 0<=i<seq.length;
      ensures  seq[i] !=null;
    */
    @Pure public void lemma_seq_nonnull(Node[] seq, int i){
        lemma_getf_nonnull(i);
        //@ assert seq[i]==getf(i);
      }

      /**
       * Set this.next_ to the given instance.
       * Needs just a single line of code to run, but a whole framework for reasoning!
       * Since we do not have dynamic frames avaialable, we need to manually establish that
       * no other Node object is mutated by this assignment. e.g. we need to establish that
       * all Node objects in the new tail are exactly the same as the old objects (except for the 
       * new one inserted).
       * 
       * Our task is substantially complicated because openjml does not implement \old(_) in some
       * circumstances. In particular \old(_) does not work for getf(_), size() etc. (Apparently because 
       * they have uq ensures/requires.) So we have to supply our own "old" state. We use "ghost" variables 
       * for this, via toSeq() generating a list
       * of all elements. Unfortunately, my current implementation is not quite ghostly, need to understand
       * who to do this right (so there is no runtime overhead).
       * 
       * 
       * @param t
       * @param olde
       * @param z
       */
     /*@ public normal_behavior
      assignable this.next_;

      requires z==toSeq().length;
      requires z==olde.length;
      requires (\forall int i; 0<=i<z; olde[i]==toSeq()[i]); 

      requires (\forall int i,j; 0<=i<z&&0<=j<z&&i!=j; olde[i] !=olde[j]); //all_diff
      requires 1<z ==> t.next_==olde[1];
      requires 1==z ==> t.next_ == null;
     
      requires (\forall int i; 0<i<olde.length; olde[i] !=this);
      requires t!=this;
      
      ensures next_ ==t;
      ensures size()==1+t.size();
      ensures (\forall int i; 1<=i<z; olde[i] ==\old(olde[i]));
      ensures t==\old(t);
      ensures size()==1+z;
    */
    public void set_tail(@NonNull Node t, /*ghost*/ @NonNull Node[] olde, int z) {
        // @ assert this == olde[0];                                       // from toSeq() == olde
      
        // @ assert 1<=z;                                                  // from toSeq() == olde
        //@ assert (\forall int i; 0<=i<z; getf(i)==olde[i]);             // from toSeq() == olde
        //@ assert 1<z ==> getf(1) != null;                               // from toSeq() == olde
        //@ assert (\forall int i; 1<=i<z-1; getf(1).getf(i)==olde[i+1]);   // getf(1).getf(i-1)==getf(i)==olde[i]
        //@ assert (\forall int i; 1<=i<z-1; olde[1].getf(i)==olde[i+1]);   // getf(1) == olde[1]
        // @ assert olde[z-1].next_==null;
        // @ assert (\forall int i; 1<=i<z; olde[i] !=this);               // from all_diff
        /*if (1<z) {
            lemma_getf_size(1);
            //@ assert size() == 1 + getf(1).size();
            //@ assert getf(1)==olde[1];
            lemma_getf_size(1);
            //@ assert z==1+olde[1].size();
        }*/
      this.next_=t;
      lemma_size_ind();
        //@ assert size() == 1+t.size();
        // @ assert this.next_==t;
        // @ assert (\forall int i; 1<=i<z-1; olde[i].next_ ==olde[i+1]);   // from all_diff
        // @ assert 1<z ==> olde[z-1].next_==null;
        if (1<z) {
            t.lemma_size_ind();
            //@ assert t.size() == 1+olde[1].size();
            lemma_seq_size(1, olde, z);
            //@ assert z == 1+olde[1].size();
            // @ assert size() == 1+z;
        }
        if (1==z) {
            //@ assert t.next_==null;
            t.lemma_size_ind();
            //@ assert t.size()==1;
            // @ assert size()==1+z;
        }
        // @ assert size()== 1+z;
     
    }

    /*@ public normal_behavior
      ensures \result != null;
      ensures \result.owner_ ==o;
      ensures \result.payload_ ==p;
      ensures \result.next_ ==t;
      ensures \result != this;
      ensures t==null ==> \result.size()==1;
      ensures t!=null ==> \result.size()==1+t.size();
    */
    public @Pure Node make(@NonNull Object o, @NonNull Object p, Node t, @NonNull Node[] olde) {
        Node n = new Node(o, p, t);
        n.lemma_size_ind();
        return n;
      }
 
      //TODO: Change so that this takes the index x, and the seq for the entire list not just the suffix. 
      // We will need to establish that the prefix has not changed.
      // We will also need theframe axiom that all nodes whose owner is not the given owner will be
      // unchanged.
    /*@ normal_behavior
      assignable next_;
      
      requires z==toSeq().length;
      requires z==olde.length;
      requires (\forall int i; 0<=i<z; olde[i]==toSeq()[i]); 

      requires (\forall int i,j; 0<=i<olde.length&&0<=j<olde.length&&i!=j; olde[i] !=olde[j]); // all distinct
      
      ensures next_ != null;
      ensures next_.owner_ == owner;
      ensures next_.payload_ == payload;
      ensures next_.next_ == \old(next_);
      ensures size() == 1+z;
      ensures (\forall int i; 1<=i<olde.length; olde[i] ==\old(olde[i]));
    */ 
    void insert_(@NonNull Object owner, @NonNull Object payload,  /*ghost*/ @NonNull Node[] olde, int z) {
        // @ assert size()==z;
        Node o = next_;
        lemma_size_ind();
        // @ assert o==null ==> size()==1;
        // @ assert o==null ==> z==1;
        // @ assert o!=null ==> size()==1+o.size();
        // @ assert o!=null ==> z==1+o.size();
        Node n = make(owner, payload, o, olde);
        // @ assert n!= this;
        // @ assert n.size()==z;
        // @ assert olde.length > 1 ==> o==olde[1];
       
        set_tail(n, olde, z);
        
        // @ assert size()==1+n.size();
        // @ assert size()==1+z;
      }
  
      /**
       * Array based getf. Of critical use in proving that after the x'th node in a list has been mutated the
       * structure of other nodes is not changed and we can continue to reason about them. Effectively part of our 
       * manual implementation of dynamic frames for this particular problem.
       * 
       * We choose here to copy the code for getf, and its proof, augmenting it with the toSeq() array as well.
       * @param x
       * @param n
       * @param seq
       * @param z
       * @return
       */

       /*@ public normal_behavior 
       
        requires z==seq.length;
        requires 0<=n && 0<=x && x+n<z;
        requires (\forall int j; x<=j<z; seq[j] !=null);
        requires (\forall int j; x<=j<z; seq[j].next_==(j==z-1? null: seq[j+1]));
        requires (\forall int j,k; x<=j<z && x<=k<z&&j!= k; seq[j]!=seq[k]);
        requires this==seq[x];

        assignable \nothing;
        ensures \result==seq[x].getf(n);
        ensures \result==seq[x+n];
    @*/
    @SpecPure public Node agetf(final int x, int n,  @NonNull Node[] seq, int z) {
        int i=0;
        Node o=this;
       
	    /*@
          ghost Node prev=null;
          loop_invariant 0<=i; 
          loop_invariant i<=n; 
          loop_invariant o==getf(i);
          loop_invariant o==seq[x+i];               // this is the key new property.
          loop_invariant 0<i ==> prev==getf(i-1);
          loop_invariant 0<i ==> prev!=null;
          loop_invariant 0<i ==> o==getf(i-1).next_;
          loop_invariant (\forall int j;0<=j<i; getf(j)!=null); 
          loop_invariant o==null ==> i>0;
          decreases n-i;
         */
        while (i<n && o!=null) {
            //@ set prev = o;
            o=o.next_;
            i++;
        }
        return o;
    }
      /*@ public normal_behavior 
       requires z==seq.length;
       requires 0<=x<z;
       requires (\forall int j; x<=j<z; seq[j] !=null);
       requires (\forall int j; x<=j<z; seq[j].next_==(j==z-1? null: seq[j+1]));
       requires (\forall int j,k; x<=j<z && x<=k<z&&j!= k; seq[j]!=seq[k]);

       ensures seq[x].size() == z-x;

      */
      @Pure public void lemma_seq_size(int x, @NonNull Node[] seq, int z){
          Node me = seq[x];
          //@assert me.agetf(x, z-x-1, seq, z) !=null;
          //@assert me.getf(z-x-1) !=null;
          //@assert me.agetf(x, z-x-1, seq, z).next_==null;

          me.getf(z-x-1).lemma_getf_basics();
          //@assert me.getf(z-x-1).next_==null;

          //@assert me.getf(z-x-1).getf(1)==null;
          me.lemma_getf_sum(z-x-1,1);
          //@assert me.getf(z-x) ==null;
          me.lemma_size_iff(z-x);
        
      }

      // To be finished.
      /* 
      @ public normal_behavior
      assignable next_;
      requires z==size();

      ensures size() == 1+z;
      ensures (\forall Node[] seq; seq==toSeq();
            (\forall int i; 1<=i<x-1; seq[i] ==olde[i]) &&
            seq[x].owner==owner&& seq[x].payload_==payload && seq[x].next_==(x+1==z+1?null:seq[x+1]) &&
             (\forall int i; x+1<=i<1+z; seq[i] ==olde[i-1]));
    
    public void insert(int x, @NonNull Object owner, @NonNull Object payload, 
        // ghost
        Node[] olde, int z) {
      Node n = getf(x-1);
      n.insert_(owner, payload, n.toSeq(), n.size());
     
    }
    */

   
}

}
