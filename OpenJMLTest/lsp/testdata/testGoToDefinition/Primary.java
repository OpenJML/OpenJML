public class Primary {
    public Helper helper = new Helper();
    //@ ghost public int pGhostField = 0;
    //@ model public int pModelField;
    public int pJavaField = 0;
    //@ model public class PModelClass {}
    //@ ghost public PModelClass pModelInst = null;

    //@ requires pJavaField >= 0;
    //@ requires pGhostField >= 0;
    //@ requires pModelField >= 0;
    //@ requires helper.hJavaField >= 0;
    //@ requires helper.hGhostField >= 0;
    //@ requires helper.hModelField >= 0;
    //@ requires pJavaMethod(0) >= 0;
    //@ requires pModelMethod(0) >= 0;
    //@ requires helper.hJavaMethod(0) >= 0;
    //@ requires helper.hModelMethod(0) >= 0;
    //@ requires helper instanceof Helper;
    //@ requires helper instanceof Helper;  // end-of-name cursor test
    public int compute(int x) { return x; }

    //@ requires x >= 0;
    //@ pure
    public int pJavaMethod(int x) { return x; }
    //@ pure model public int pModelMethod(int x) { return x; }

    //@ requires (\forall int i; i >= 0; i < pJavaField);
    //@ requires (\let int letVar = pJavaField; letVar >= 0);
    //@ requires (\exists int qi, qj; qi >= 0 && qj >= 0; qi < qj);
    public int quantified(int n) { return n; }
}
