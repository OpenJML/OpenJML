package demo;
public class A {
    //@ ghost int i = 0; // No errors

    //@ ensures i == 0;
    void f() {
        int a = 0;
        if(a==0){
            System.out.println("test");
        }
        
    }
}

