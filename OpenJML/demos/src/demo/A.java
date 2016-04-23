package demo;

public class A {
    //@ requires true;
    public static int cmp(int a, int b) { 
       
        int c = 100;
        a = 100;
        
        if(a > b){
            return 0;
        }else{
            return 1;
        }
        
    } 
}

