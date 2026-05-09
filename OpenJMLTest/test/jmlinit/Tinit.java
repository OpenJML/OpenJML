public class Tinit {
    
    //@ ghost public static \bigint zint;
    //@ public static invariant zint == \bigint.zero;
    
    //@ ghost public static \real zreal;
    //@ public static invariant zreal == (\real)0;
    
    //@ ghost public static \string zstring;
    //@ public static invariant zstring.isEmpty();

    //@ ghost public static \array<Object> zarray;
    //@ public static invariant zarray.length == 0;
    
    //@ ghost public static \seq<Object> zseq;
    //@ public static invariant zseq.isEmpty();
    
    //@ ghost public static \set<Object> zset;
    //@ public static invariant zset.isEmpty();
    
    //@ ghost public static \map<Object,Integer> zmap;
    //@ public static invariant zmap.isEmpty();
    
    //@ ghost public static \range zrange;
    //@ public static invariant zrange.isEmpty();
    
    // FIXME - add in TYPE
    
    public static void main(String ... args) {
        //@ check zint == 0;
        //@ check zreal == 0;
        //@ check zstring.isEmpty();
        //@ check zarray.length == 0;
        //@ check zseq.isEmpty();
        //@ check zset.isEmpty();
        //@ check zmap.isEmpty();
        //@ check zrange.isEmpty();
        TinitFinal.main(args);
    }
}
