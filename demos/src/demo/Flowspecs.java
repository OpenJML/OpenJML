package demo;
import org.jmlspecs.annotation.*;
public class Flowspecs {
    
    
    //
    // Typechecking Tests
    //
    

    // ok
    /*@ level(PRIVATE) */ private int aa = 3;
    // ok
    /*@ level(PUBLIC)  */ private int  bb = 3;
    // fails
    /*@ level(PUBLIC)  */ private int  cc = aa;
    // ok
    /*@ level(PRIVATE)  */ private int  dd = bb;
    
    
    // ok
    /*@ level(USERTRUSTS) */ private int foo = 100;
    // fails
    /*@ level(PUBLIC) */     private int a = foo;


    // fails
    /*@ level(PUBLIC) */     private int ad = (bb +foo);

    
    
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
        
        // BUG -- Causes Compiler Crash!
        aa = bb = aa;

    }
    
    // fail
    private void test16(){
        
        @Level("Private")
        int a = 2;
        
        test16Helper1(a);
        
        
        
    }
    
    // ok
    private void test16a(){
        
        @Level("Public")
        int a = 2;
        
        test16Helper1(a);
        
    }

    // ok
    private void test16b(){
        
        @Level("Public")
        int a = 2;
        
        test16Helper2(a);
        
    }

    private void test16Helper1(/*@ level(PUBLIC) */ int a){}
    private void test16Helper2(/*@ level(PRIVATE) */ int a){}

    
private void test17a(){        
        
        @Level("Public")
        int a = 2;
        @Level("Public")
        int b = 2;
        
        test17Helper1(a,b);
        test17Helper1(a,b,b);
        test17Helper1(a,b,b,b,b,b,b,b,b,b,b,b,b,b);
        
    }
    
    private void test17aa(){        
        
        @Level("Public")
        int a = 2;
        @Level("Public")
        int b = 2;
        
        test17Helper2(a,b);
        test17Helper2(a,b,b);
        test17Helper2(a,b,b,b,b,b,b,b,b,b,b,b,b,b);
        
    }
    
    private void test17b(){        
        
        @Level("Public")
        int a = 2;
        @Level("Private")
        int b = 2;
        
        test17Helper1(a,b);
        test17Helper1(a,b,b);
        test17Helper1(a,b,b,b,b,b,b,b,b,b,b,b,b,b);        
    }
    
    private void test17c(){        
        
        @Level("Public")
        int a = 2;
        @Level("Private")
        int b = 2;

        // make sure they don't try to slip something into the args...
        test17Helper1(a,a);
        test17Helper1(a,a,b,a,a,b);
    }

    private void test17Helper1(/*@ level(PUBLIC) */ int a, /*@ level(PUBLIC) */ int ...other){}
    private void test17Helper2(/*@ level(PRIVATE) */ int a, /*@ level(PRIVATE) */ int ...other){}


    //
    // Flow Checks
    //
    void test18(){
      
        @Level("Public")
        int a = 1;
        @Level("Public")
        int c = 3;
        
        @Level("Private")
        int b = 1;
        
        if(b==1){
            a = c; // normally ok, not ok in flow context.
        }
        
        if(b==1){
            b = 2; // ok
        }
        
    }

    void test19(){
        
        @Level("Public")
        int a = 1;
        @Level("Public")
        int c = 3;
        
        @Level("Private")
        int b = 1;
        
        // Tricky!
        if(a==1){
            a = c;  // ok
            b = a ;  // also ok
                    
            if(b==1){
                a = c; // not ok
                b = 2; // ok
                
                if(a==1){
                    a = c; // not ok
                    b = 2; // ok
                }
                
            }
                    
        }
        
    }
}

