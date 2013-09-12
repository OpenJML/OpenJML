package demo;
import org.jmlspecs.annotation.*;
public class Flowspecs {
    
    
    //
    // Typechecking Tests
    //
    

    /*@ level(PRIVATE) */ private int aa = 3;
    /*@ level(PUBLIC)  */ private int  bb = 3;
    /*@ level(PUBLIC)  */ private int  cc = aa;
    
    
    
    void test1() {
        
        @Level("PRIVATE")
        int a = 3;
         
         
         /*@ level(PUBLIC) */ int b = 0;
    
         // ok
         a = b;
         // not ok
         b = a;
     }  
    
    
    void test2(int c){
        
        /*@ level(PRIVATE) */ int a = 3;
        /*@ level(PUBLIC) */ int b = 0;
   
        // ok
        a = a+a;
        b = b+b;
        
        // also ok
        a = a + b;
        a = b + a;
        a = a*2;
        a = 2*a;
        
        // also ok!
        b = 2*b;
        b = 2;
        b = b*b;
        
        // not ok
        b = b+a;
        b = a+b;
        b = a*2;
        
        // also not ok
        b = (a+a) * (b+b);
        
    }

    // fails
    /*@ level(PUBLIC) */ int test3() {

        /*@ level(PRIVATE) */ int a = 3;
        int b = 0;
        
        return b;
    }
    
    // ok
    /*@ level(PUBLIC) */ int test4() {

        /*@ level(PRIVATE) */ int a = 3;
        /*@ level(PUBLIC)  */ int b = 0;
        
        return b;
    }

    // implicitly ok
    /*@ level(PRIVATE) */ int test5() {

        /*@ level(PRIVATE) */ int a = 3;
        /*@ level(PUBLIC)  */ int b = 0;
        
        return a;
    }

    // not ok
    /*@ level(PUBLIC) */ int test6() {

        /*@ level(PRIVATE) */ int a = 3;
        /*@ level(PUBLIC)  */ int b = 0;
        
        return b*a;
    }

    // Possibly ok?
    /*@ level(PUBLIC) */ int test7() {

        /*@ level(PRIVATE) */ int a = 3;
        
        return 1;
    }

    // Possibly ok?
    /*@ level(PRIVATE) */ int test8() {

        /*@ level(PRIVATE) */ int a = 3;
        
        return 1;
    }

    
    void test9(/*@ level(PRIVATE) */int a, /*@ level(PUBLIC) */int b) {

        a = 3;

        b = 0;

        // ok
        a = a + a;
        b = b + b;

        // also ok
        a = a + b;
        a = b + a;
        a = a * 2;
        a = 2 * a;

        // also ok!
        b = 2 * b;
        b = 2;
        b = b * b;

        // not ok
        b = b + a;
        b = a + b;
        b = a * 2;

        // also not ok
        b = (a + a) * (b + b);

    }
    
    // fails
    /*@ level(PUBLIC) */ int test10(/*@ level(PRIVATE) */ int a) {
        return a;
    }

    // also fails
    /*@ level(PUBLIC) */ int test11(int a) {
        return a;
    }

    // OK
    /*@ level(PUBLIC) */ int test12(/*@ level(PUBLIC) */ int a) {
        return a;
    }

    // Warns
    /*@ level(PRIVATE) */ int test13(/*@ level(PUBLIC) */  int a) {
        return a;
    }
    
    
    void test14(){
        
        /*@ level(PRIVATE) */ int a = 3;
        /*@ level(PUBLIC) */  int b = 44;
        
        // fails
        a = test12(a);
        // ok
        a = test12(b);
        // fails
        b = test12(a);
        // ok
        b = test12(b);
        
        
    }
    
    
    void test15(){
        // ok
        aa = bb;
        // not ok
        bb = aa;
        
        // OK
        aa = bb = cc;
        
        // BUG
        aa = bb = aa;

    }

}

