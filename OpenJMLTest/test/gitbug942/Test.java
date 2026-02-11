// These tests check the interaction of pure/spec_pure with determinism
public class Test {

//@ ensures \result == (a == b);
//@ no_state
public static boolean Equals(int a, int b) {
    return a == b;
}

//@ requires x != Integer.MIN_VALUE;
//@ assigns \nothing;
//@ ensures \result >= 0;
    public static int abs(int x) {
        if (x < 0) {
            return -x;
        } else {
            return x;
        }
    }

  //@ requires x != Integer.MIN_VALUE;
  //@ assigns \nothing;
  //@ ensures \result >= 0;
      public static int abs2(int x) {
          if (x < 0) {
              return -x;
          } else {
              return x;
          }
      }

    //@ requires x != Integer.MIN_VALUE;
    //@ assigns \nothing;
    //@ ensures \result >= 0;
    //@ spec_pure
        public static int abs3(int x) {
            if (x < 0) {
                return -x;
            } else {
                return x;
            }
        }

// this does not work (incorrectly ? verifies)-- now fixed
// calls abs() two times
//@ requires x != Integer.MIN_VALUE;
//@ model public static void A_test_completeness_0(int x) {
//@     int ret1 = abs(x);
//@     int ret2 = abs(x);
//@     assert Equals(ret1, ret2); // ERROR
//@ }

// this works (fails to verify, as expected)
// calls abs() and abs2()
//@ requires x != Integer.MIN_VALUE;
//@ model public static void B_test_completeness_0(int x) {
//@     int ret1 = abs(x);
//@     int ret2 = abs2(x);
//@     assert Equals(ret1, ret2); // ERROR
//@ }
        
     // this does not work (incorrectly ? verifies)-- now fixed
     // calls abs() two times
     //@ requires x != Integer.MIN_VALUE;
     //@ model public static void C_test_completeness_0(int x) {
     //@     int ret1 = abs3(x);
     //@     int ret2 = abs3(x);
     //@     assert Equals(ret1, ret2); // OK
     //@ }
}
