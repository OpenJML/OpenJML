class Parent {
    
    //@ model int z;              // ERROR: No rep in Parent
    //@ abstract model int y;     // OK - abstract and then has rep in NoModelTest
    //@ abstract model int q;     // ERROR: OK in Parent, but no rep in NoModelTest
    //@ model int x;              // OK - has rep in Parent and in NoModelTest
    //@ model int p;              // OK - has rep in Parent
    //@ represents x = 42;
    //@ represents p = 99;
}

public class NoModelTest extends Parent {
    
    //@ represents y = 11;
    //@ represents x = 43;
    public static void main(String... args) {
        var t = new NoModelTest();
        //@ set System.out.println("Z: " + t.z); // No rep
        //@ set System.out.println("Y: " + t.y);
        //@ set System.out.println("X: " + t.x);
        //@ set System.out.println("P: " + t.p);
        //@ set System.out.println("Q: " + t.q); // No rep
        System.out.println("END");
    }
}