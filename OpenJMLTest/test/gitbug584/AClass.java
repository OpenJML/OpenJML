
public class AClass implements AnInterface {

    int n = 2; //@ in size;
    //@ represents size = n;

    //@ public model int classModel;

    public int getSize() { return n; }

    public int badSize() { return n + 1; }

    static String fields(Class<?> c) {
        String s = "";
        for (java.lang.reflect.Field f: c.getDeclaredFields()) s = s + " " + f.getName();
        return s;
    }

    public static void main(String[] args) {
        System.out.println("AnInterface fields: " + fields(AnInterface.class));
        System.out.println("AClass fields: " + fields(AClass.class));
        AClass a = new AClass();
        System.out.println(a.getSize());
        System.out.println(a.badSize());
    }
}
