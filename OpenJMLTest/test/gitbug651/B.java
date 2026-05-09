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
        this.context = builder.context;
        // Here, OpenJML complains it cannot verify the Map invariant.
        // It ought to follow from what's known about this map on entry to this constructor.
        // However, as can be confirmed by including the assertion above, OpenJML doesn't
        // know that the Map invariant holds for parameter "builder".
    }

    //@ public normal_behavior
    //@   requires true;
    public void testMethodA()
    {
        //@ assert context.modelMap == context.modelMap; // OK
    }

    //@ public normal_behavior
    //@   requires true;
    public void testMethodB(Builder builder)
    {
        // The following assertion fails. 
        //@ check this.context == builder.context ==>  builder.context.modelMap == this.context.modelMap; // FAILS
        //@ check builder.context.modelMap == this.context.modelMap; // FAILS
    }

    //@ non_null_by_default
    public static class Builder {
        //@ spec_public
        // Including the following line should not make any difference, since
        // the class is using non_null by default. However, oddly enough, by
        // including the following line, testMethodB reports an infeasible control
        // path.
        //    //@ non_null
        private Map<String, String> context = Collections.emptyMap();
        
        //@ public behavior
        //@   ensures this.context.isEmpty();
        //@ pure
        public Builder() {
        }
    }
}
