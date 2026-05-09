public class TinitFinal {
    
    //@ ghost public static final \bigint zint;
    //@ public static final invariant zint == \bigint.zero;
    
    //@ ghost public static final \real zreal;
    //@ public static final invariant zreal == (\real)0;
    
    //@ ghost public static final \string zstring;
    //@ public static final invariant zstring.isEmpty();

    //@ ghost public static final \array<Object> zarray;
    //@ public static final invariant zarray.length == 0;
    
    //@ ghost public static final \seq<Object> zseq;
    //@ public static final invariant zseq.isEmpty();
    
    //@ ghost public static final \set<Object> zset;
    //@ public static final invariant zset.isEmpty();
    
    //@ ghost public static final \map<Object,Integer> zmap;
    //@ public static final invariant zmap.isEmpty();
    
    //@ ghost public static final \range zrange;
    //@ public static final invariant zrange.isEmpty();
    
    //@ public normal_behavior
    //@ ensures zint == \bigint.zero;
    //@ ensures zreal == (\real)0;
    //@ static_initializer
    
    // FIXME - add in TYPE
    
    //@ no_state
    public static void main(String ... args) {
        //@ check zint == 0;
        //@ check zreal == 0;
        //@ check zstring.isEmpty();
        //@ check zarray.length == 0;
        //@ check zseq.isEmpty();
        //@ check zset.isEmpty();
        //@ check zmap.isEmpty();
        //@ check zrange.isEmpty();
    }
}
