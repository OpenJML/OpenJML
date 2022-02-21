class GP {
	int n = 10;
	
	//@ ensures this.n == 10;
	GP() {}
}

class Parent extends GP {
    int n = 20;
    //@ ghost int g = 50;
    
    //@ ensures this.n == 20;
    //@ ensures this.g == 50;
    Parent() {}
}
public class Test extends Parent {
    int n = 30;
    int g = 60;
    
    //@ ensures ((GP)this).n == 10;
    //@ ensures ((Parent)this).n == 20;
    //@ ensures super.n == 20;
    //@ ensures this.n == 30;
    //@ ensures this.g == 60;
    //@ ensures ((Parent)this).g == 50;
    //@ ensures super.g == 50;
    Test() {}
	
}

class GP1 {
	final int n = 10;
	
}

class Parent1 extends GP1 {
    final int n = 20;
    //@ ghost final int g = 50;
    
}

class Test1 extends Parent1 {
    int n = 30;
    int g = 60;
    
    //@ ensures ((GP1)this).n == 10;
    //@ ensures ((Parent1)this).n == 20;
    //@ ensures super.n == 20;
    //@ ensures this.n == 30;
    //@ ensures this.g == 60;
    //@ ensures ((Parent1)this).g == 50;
    //@ ensures super.g == 50;
    Test1() {}
	
}