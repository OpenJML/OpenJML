package demo;
import org.jmlspecs.annotation.*;
public class Flowspecs {
    
    
    //
    // Typechecking Tests
    //
    
    
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

//    void test3(){}
//    
//    int test3a(){}
//    
//    int test3b(){}
//    
    

}

