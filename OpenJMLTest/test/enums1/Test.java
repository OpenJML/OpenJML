enum EEE {
    
    AA, BB, CC, DD;
}

public class Test {
    
    public void m1() {
        //@ assert EEE.AA instanceof EEE;
        //@ assert \type(EEE) <: \type(Enum<EEE>);  // FIXME - needs work
        //@ assert EEE.class <: Enum.class;
    }
    
    //@ pure
    public void m2a() {
        //@ assert EEE.AA.toString().equals("AA");  // Needs work on strings
    }
    
    //@ pure
    public void m2c() {
        //@ assert EEE.AA.name().equals("AA");  // Needs work on strings
    }
    
    //@ pure
    public void m5d(EEE e) {
        EEE[] ev = EEE.values();
        //@ assert  (\exists \bigint i; 0<=i && i<ev.length; ev[i] == EEE.BB);
        //@ assert  (\exists \bigint i; 0<=i && i<ev.length; ev[i] == EEE.DD);
        //@ assert  (\forall \bigint i; 0<=i && i<ev.length; ev[i] != null);
        //@ assert ev == EEE._JMLvalues;
        //@ assert ev.length == 4;
        //@ assume (\forall EEE ee; ee != null ==> (\exists \bigint i; 0<=i && i<EEE._JMLvalues.length; EEE._JMLvalues[i] == ee));
        //@ assume (\forall EEE ee; validEnum(ee));
        //@ assert (\forall EEE ee; validEnum(ee)); // FAILS, despite the assumption above
        //@ assert (\forall EEE ee; validEnum(ee) ==> (ee == null || ee == EEE.AA || ee == EEE.BB || ee == EEE.CC || ee == EEE.DD)); // FAILS, despite the assumption above
        //@ assert (\forall EEE ee; validEnum(ee) ==>  ee != null ==> ( ee == EEE.AA || ee == EEE.BB || ee == EEE.CC || ee == EEE.DD)); // FAILS, despite the assumption above
        //@ assume (\forall EEE ee; ee != null ==> isEnum(ee,ev));
        //@ assert (\forall EEE ee; ee != null ==> isEnum(ee,ev));
        //@ assume (\forall EEE ee; ee != null ==> (\exists \bigint i; 0<=i && i<ev.length; ev[i] == ee));
        //@ assert (\forall EEE ee; validEnum(ee) ==> ee != null ==> (\exists \bigint i; 0<=i && i<ev.length; ev[i] == ee)); // FIXME - failing, even though matches the line above
    }
    
    //@ ensures \result <==> (ee == null || ee == EEE.AA || ee == EEE.BB || ee == EEE.CC || ee == EEE.DD);
    //@ model pure public static boolean validEnum(nullable  EEE ee);
    
    //@ ensures \result ==(\exists \bigint i; 0<=i && i<ev.length; ev[i] == ee);
    //@ model pure public static boolean isEnum( non_null  EEE ee, EEE[] ev);
    
}