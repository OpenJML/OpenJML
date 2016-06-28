package org.jmlspecs.openjml.jmldoc.test;

/**
 * A Research Class
 * @author Arjun Mitra Reddy Donthala
 * @author Dr. Gary T. Leavens
 * @author Dr. Sumit Kumar Jha
 * @author Dr. Damla Turgut
 * @version 2016-28-06
 */

public class Research extends ETD{
    //@ invariant false;
    //@ invariant true;
    //@ constraint true;
    //@ initially false;
    //@ axiom false;
      
    //@ also requires true;
    //@ model @Deprecated Object Test1 (int i);

    //@ model int Test2 (int i);

    //@ requires i == 0;
    //@ model void Test3 (int i);

    //@ requires i == 0.0;
    //@ model void Test4 (float i);

    //@ requires i == null;
    //@ model void Test5 (Object i);

    //@ requires i == "";
    //@ model void Test6 (String i);

  //@ ensures name.equals("Dr. Gary T. Leavens");
    public static void chair(String name) {
    }
}
