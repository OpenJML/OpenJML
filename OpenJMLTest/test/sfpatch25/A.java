class A {

	//@ ensures false;
private void test17a(){

        int a = 2;
        int b = 2;

    test17Helper1(a,b);   //OK
    test17Helper1(a,b,b); // Compiler crash
}

private void test17Helper1(int a, int /*@ non_null */ ...other){}

}