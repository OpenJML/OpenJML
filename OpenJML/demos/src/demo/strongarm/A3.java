package demo.strongarm;

/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, fields
 * 
 * @author jls
 *
 */
public class A3 {
    
    int THE_FIELD;
    
    class A3c {
        public int ANOTHER_FIELD;
    }

    //@ requires true;
    public int localTest0(){
        
        int a;
        
        a = 3;
        a = 4;
        a = 5;
        
        return -1;
    }

    //@ requires true;
    public int localTest1(){
        
        int a=0;
        
        if(a > -1){
            a = 3;
            a = 4;
        }
        
        a = 5;
        
        return -1;
    }

    
    // @ requires true;
//    public int localTest(int a, int b){
//        
//        THE_FIELD = 999;
//
//        if(a > -1){
//            return 0;
//        }
//        
//        THE_FIELD = 777;
//        return -1;
//    }
//    
//
//     
//    //@ requires true;
//    public int localTest2(int a, int b, A3c otherClazz){
//        
//        THE_FIELD = 999;
//
//        if(a > -1){
//            return 0;
//        }
//        
//        otherClazz.ANOTHER_FIELD = THE_FIELD*10;
//        
//        THE_FIELD = 777;
//        return -1;
//    }

}

