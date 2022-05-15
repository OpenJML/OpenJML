public class Test {
    
    static abstract class A1 {
        //@ pure
        abstract public int theInt();
        
        public void test(A1 a) {
          int x = theInt();
          //@ assert theInt() == theInt();
          //@ assert x == theInt();
          int y = theInt();
          //@ assert x == y;
          //@ assert a == this ==> x == a.theInt();
        }
    }

    static abstract class A2 {
        //@ assigns \nothing;
        abstract public int theInt();
        
        public void test(A2 a) {
          int x = theInt();
          int y = theInt();
          //@ assert x == y;
          int z = a.theInt();
          //@ assert a == this ==> x == z;
        }
    }

    static abstract class A3 {
        abstract public int nextInt();
        
        public void test() {
          int x = nextInt();
          int y = nextInt();
          //@ assert x == y; // NOT PROVABLE
        }
    }

    static abstract class A4 {
        //@ spec_public
        private int _theIntA;
        //@ spec_public
        private int _theIntB;
        //@ assigns _theIntA; reads _theIntB;
        abstract public int nextInt();
        //@ reads _theIntB;
        //@ pure
        abstract public int theInt();
        
        public void test() {
          int x = nextInt();
          int j = theInt();
          int y = nextInt();
          int k = theInt();
          //@ assert j == k; // OK
        }
    }

    static abstract class A5 {
        //@ spec_public
        private int _theInt;
        //@ assigns _theInt; reads _theInt;
        abstract public int randomInt();
        
        public void test1() {
          int x = randomInt();
          int y = randomInt();
          //@ assert x == y; // NOT PROVABLE
        }
        public void test2() {
          int x = randomInt();
          int y = randomInt();
          //@ assert x != y; // NOT PROVABLE EITHER
        }
    }

}