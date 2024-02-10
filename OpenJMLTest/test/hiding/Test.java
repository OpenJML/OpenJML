class GP {
    int n = 10;
    //@ ghost int g = 40;

    //@ initially n == 10 && g == 40;

    GP() {}
}

class Parent extends GP {
    int n = 20;
    //@ ghost int g = 50;
    
    //@ initially super.n == 10 && super.g == 40 && n == 20 && g == 50;

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
    //@ ensures ((GP)this).g == 40;
    Test() {}

}

// Same hierarchy but with final fields
class GP1 {
    final int n = 10;

    // @ initially n == 10;

}

class Parent1 extends GP1 {
    final int n = 20;
    //@ ghost final int g = 50;

    // @ initially super.n == 10 && n == 20 && g == 50; // FIXME - make this clause a default/inferrred clause
}

class Test1 extends Parent1 {
    final int n = 30;
    final int g = 60;

    //@ ensures ((GP1)this).n == 10;
    //@ ensures ((Parent1)this).n == 20;
    //@ ensures super.n == 20;
    //@ ensures this.n == 30;
    //@ ensures this.g == 60;
    //@ ensures ((Parent1)this).g == 50;
    //@ ensures super.g == 50;
    Test1() {}

}