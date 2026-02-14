import java.util.stream.*;
import java.util.*;

public class ImplicitIterationDemo {

   boolean allTrue = true;

   //@ assignable allTrue;
   //@ ensures allTrue == (\old(allTrue) && v);
   void check(boolean v) { allTrue =  allTrue && v; } // FIXME - problem is the implicit unboxing

   void test() {
       Boolean bb =  true;
       boolean bbb = bb && bb;
       allTrue = true;
       Stream<Boolean> s = Stream.<Boolean>of(true, false, true);
       List<Boolean> ls = Arrays.asList(new Boolean[] { true, false, true});
//      Stream<Boolean> ss = Stream.of(true, true, true, true);

      // @ loop_invariant allTrue==(\forall int j; 0<=j && j <\count; s.values[j]);
      // @ loop_modifies allTrue;

       var local = this;
       
       // @ loop_invariant 0 <= \count <= s.values.length;
       // @ decreases s.values.length - \count;
       //@ loop_assigns local.allTrue;
       //@ inlined_loop;
       s.forEachOrdered(b->check(b));

      
      
      
      
      //      //@ assert allTrue==(\forall int j; 0<=j && j <s.count(); s.values[j]);
//      //@ assert !allTrue;

//       java.util.Iterator<Boolean> itt = s.iterator();
//       //@ loop_assigns itt.*, allTrue;
//       for (; itt.hasNext(); ) { var ss = itt.next(); this.check(ss); }
       
//       //@ loop_assigns allTrue;
//       //@ inlined_loop;
//       ls.forEach(b->check(b));
       
      
      
//	  allTrue = true;
//      //@ loop_invariant allTrue==(\forall int j; 0<=j && j <\count; ss.values[j]);
//      //@ loop_modifies allTrue;
//      //@ inlined_loop;
//      ss.forEachOrdered(b->check(b));
//      //@ assert allTrue==(\forall int j; 0<=j && j <ss.count(); ss.values[j]);
//      //@ assert allTrue;
//
    }
}
