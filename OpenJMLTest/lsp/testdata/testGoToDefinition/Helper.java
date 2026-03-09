public class Helper {
    //@ ghost public int hGhostField = 0;
    //@ model public int hModelField;
    public int hJavaField = 0;
    //@ model public class HModelClass {}
    //@ ghost public HModelClass hModelInst = null;

    public int hJavaMethod(int x) { return x; }
    //@ model public int hModelMethod(int x) { return x; }
}
