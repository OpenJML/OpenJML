public class CircleOperations {

    static public int k;
    
    public int id(int radius) {
        return radius;
    }
    
    //@ pure
    public int idp(int radius) {
        return radius;
    }
    
    //@ assignable \nothing;
    public int idn(int radius) {
        return radius;
    }
    
    //@ assignable \everything;
    public int ide(int radius) {
        return radius;
    }
    
    //@ assignable k, \everything, k;
    public int idee(int radius) {
        return radius;
    }
    
    public static void main(String [] argv) {
        CircleOperations cops = new CircleOperations();
        System.out.println(cops.id(79));
    }

    public static void mn(String [] argv) {
        CircleOperations cops = new CircleOperations();
        System.out.println(cops.idn(79));
    }

    public static void mp(String [] argv) {
        CircleOperations cops = new CircleOperations();
        System.out.println(cops.idp(79));
    }

    public static void me(String [] argv) {
        CircleOperations cops = new CircleOperations();
        System.out.println(cops.ide(79));
    }

    public static void mee(String [] argv) {
        CircleOperations cops = new CircleOperations();
        System.out.println(cops.idee(79));
    }

}
