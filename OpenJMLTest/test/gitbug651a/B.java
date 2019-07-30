// In Map.jml in the Specs repository, class Map has the following invariant:
//    //-RAC@ public invariant content.owner == this;
// I will refer to this invariant as "the Map invariant".
import java.util.Map;

import java.util.Collections;

//@ non_null_by_default
public final class B {
    //@ spec_public
    private final Map<String, String> context;

    //@ public normal_behavior
    //@   requires true;
    //@ pure
    public B(Builder builder) {
        //@ assume \invariant_for(builder.context);
        this.context = builder.context;
    }

    //@ public normal_behavior
    //@   requires true;
    public void testMethodB(Builder builder)
    {
        //@ assume \invariant_for(builder.context);
        // The following assertion fails. The only difference between this
        // assertion and the one in "testMethodA" above is that it's talking
        // about "builder.context" instead of "this.context". So, it seems
        // that OpenJML knows about the Map invariant for "this.context", but
        // not for "builder.context".
        //@ assert builder.context.content.owner == builder.context;
    }

    //@ non_null_by_default
    public static class Builder {
        //@ spec_public
        // Including the following line should not make any difference, since
        // the class is using non_null by default. However, oddly enough, by
        // including the following line, testMethodB reports an infeasible control
        // path.
        //@ non_null
        private Map<String, String> context = Collections.emptyMap();
        
        //@ public behavior
        //@   assignable \everything;
        public Builder() {
        }
    }
}