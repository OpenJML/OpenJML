public class MyObjectArray {

    public class Address { // bug with this not static
        public int address;
    }

    //@ public invariant addresses.length == 100;
    public Address[] addresses = new Address[100];


    //@ ensures (\forall int i; i >= 0 && i < 100; addresses[i] != null);
    //@ ensures (\forall int j,k; 0<=j && j<100 && 0<=k && k<j; addresses[j] != addresses[k]);
    //@ ensures (\forall int j; 0<=j && j<100; addresses[j].address == j);
    public MyObjectArray(Address a) {
        //@ maintaining i >= 0 && i <= 100;
        //@ loop_invariant (\forall int j; 0<=j && j<i; addresses[j] != null);
        //@ loop_invariant (\forall int j; 0<=j && j<i; \fresh(addresses[j],LoopInit));
        //@ loop_invariant (\forall int j; 0<=j && j<i; (\forall int k; 0<=k && k<j; addresses[j] != addresses[k]));
        //@ decreasing 100 - i;
        for (int i = 0; i < 100; ++i) {
            addresses[i] = new Address();
            //@ assert (\forall int j; 0<=j && j<=i; (\forall int k; 0<=k && k<j; addresses[j] != addresses[k]));
        }

        //@ maintaining i >= 0 && i <= 100;
        //@ loop_invariant (\forall int j; 0<=j && j<i; addresses[j].address == j);
        //@ decreasing 100 - i;
        for (int i = 0; i < 100; ++i) {
            addresses[i].address = i;
        }
    }
}

