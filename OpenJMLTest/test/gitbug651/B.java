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
        //  @ assume \invariant_for(builder.context);
        //    //@ assert builder.context.content.owner == builder.context;
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
        // The following assertion is verified, as expected. In other words,
        // OpenJML knows that the Map invariant holds for "this.context".
        //@ assert this.context.content.owner == this.context;
    }

    //@ public normal_behavior
    //@   requires true;
    public void testMethodB(Builder builder)
    {
        // The following assertion fails. The only difference between this
        // assertion and the one in "testMethodA" above is that it's talking
        // about "builder.context" instead of "this.context". So, it seems
        // that OpenJML knows about the Map invariant for "this.context", but
        // not for "builder.context".
        //@ assert builder.context.content.owner == builder.context;
    }

    //@ public normal_behavior
    //@   requires true;
    public void testMethodC(Builder builder)
    {
        //@ assume \invariant_for(builder.context);
        // The assume above fixes it, but the invariant should be included automatically
        //@ assert builder.context.content.owner == builder.context;
    }

    //@ non_null_by_default
    public static class Builder {
        //@ spec_public
        private Map<String, String> context = Collections.emptyMap();
        
        //@ public behavior
        //@   assignable \everything;
        public Builder() {
        }
    }
}