package demo;
import org.jmlspecs.annotation.*;
public class Flowspecs {
    
    
    //
    // Typechecking Tests
    //
    
    
    void test1() {
        
         /*@ level(PRIVATE) */ int a = 3;
         
         
         /*@ level(PUBLIC) */ int b = 0;
    
         // ok
         a = b;
         // not ok
         b = a;
     }  
    
    void test2(){
        
        /*@ level(PRIVATE) */ int a = 3;
        
        
        /*@ level(PUBLIC) */ int b = 0;
   
        
        // ok
        a = a+a;
        b = b+b;
        
        // also ok
        a = a + b;
        a = a*2;
        
        // not ok
        b = a+b;
        b = a*2;
        
    }

//    void test3(){}
//    
//    int test3a(){}
//    
//    int test3b(){}
//    
    

}

