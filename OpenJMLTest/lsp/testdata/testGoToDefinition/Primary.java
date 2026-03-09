public class Primary {
    public Helper helper = new Helper();
    //@ ghost public int pGhostField = 0;
    //@ model public int pModelField;
    public int pJavaField = 0;

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
    public int compute(int x) { return x; }

    //@ pure
    public int pJavaMethod(int x) { return x; }
    //@ model public int pModelMethod(int x) { return x; }
}
