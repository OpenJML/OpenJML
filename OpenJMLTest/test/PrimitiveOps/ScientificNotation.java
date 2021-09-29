public class ScientificNotation {

  public static void floats(){
    // works
    //@ assert 1.234567e6f == 1234567.0f;
    //@ assert 1.0e6f == 1000000.0f;

    // integer in SMT
    //@ assert 1.2345678e7f == 12345678.0f;
    //@ assert 1.23456789e7f == 12345678.9f;
    // scientific in SMT
    //@ assert 1.2345670e7f == 12345670.0f;
  }

  public static void doubles(){
    // works
    //@ assert 1.234567e6 == 1234567.0;
    //@ assert 1.0e6 == 1000000.0;

    // integer in SMT
    //@ assert 1.2345678e7 == 12345678.0;
    //@ assert 1.23456789e7 == 12345678.9;
    // scientific in SMT
    //@ assert 1.2345670e7 == 12345670.0;

  }

  // translates to scientific
  public static void negative_6(){
    //@ assert 9.0e-6 == 0.000009;
    //@ assert 9.9e-6 == 0.0000099;
    //@ assert 9.99e-6 == 0.00000999;
    //@ assert 9.999e-6 == 0.000009999;
    //@ assert 9.9999e-6 == 0.0000099999;
    //@ assert 9.99999e-6 == 0.00000999999;
  }

  // translates to scientific
  public static void negative_7(){
    //@ assert 9.0e-7 == 0.0000009;
    //@ assert 9.9e-7 == 0.00000099;
    //@ assert 9.99e-7 == 0.000000999;
    //@ assert 9.999e-7 == 0.0000009999;
    //@ assert 9.9999e-7 == 0.00000099999;
    //@ assert 9.99999e-7 == 0.000000999999;
  }
}
