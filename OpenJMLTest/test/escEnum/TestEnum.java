public class TestEnum {
    
    static public enum EE {
        AA, BB
    }
}

// FIXME - this works OK when -smt=out.smt2 is set, but the TestEnum() constructor fails feasibility without it??????