package demo;

public class A {
   
    //@ requires a > 99;
    public static int cmp(int a, int b) { 
        if(a > b){
            return 1;
        }else{
            if (a < b){
                return -1;
            }
            return 0;
        }
        
    } 
}

