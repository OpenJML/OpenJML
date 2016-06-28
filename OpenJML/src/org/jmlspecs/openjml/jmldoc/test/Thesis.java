package org.jmlspecs.openjml.jmldoc.test;

import org.jmlspecs.annotation.Pure;

/**
 * A Thesis for JMLdoclet
 * @author Arjun Mitra Reddy Donthala
 * @version 2016-28-06
 */


public class Thesis extends Research  {
    
    // ******************************************************************************** CLASS WITH SPECIFICATIONS *********************************************************************************\

        //@ invariant true;
        //@ constraint false;
        //@ initially true;
        //@ axiom true;

    
 
    // ******************************************************************************** FIELDS WITH SPECIFICATIONS *********************************************************************************\

        /**
         * The minimum number of committee members
         */
    
    public static final int MIN_MEMBERS = 3;
    
        /**
         * The maximum number of committee members
         */
    
    public static final int MAX_MEMBERS = 6;
    
        /**
         * The maximum duration in minutes
         */
    
    public static final int MAX_DURATION = 60;
    
        /**
         * The current members on Student's Committee
         */
    
    private int my_members;
        //@ in members;
        //@ public model int members;
        //@ private represents members = my_members;
        //@ public invariant members >= MIN_MEMBERS && members <= MAX_MEMBERS;
    
    /**
     * The duration of Thesis
     */
    
    private int my_duration;
        //@ in minutes;
        //@ public model int minutes;
        //@ private represents minutes = my_duration;
        //@ public invariant 0 <= minutes && minutes < MAX_DURATION;
    
    
    // ******************************************************************************** CONSTRUCTORS WITH SPECIFICATIONS *********************************************************************************\
    
        /**
         * Constructs a new Thesis.
         *
         * @param the_members The initial setting for members.
         */
        //@ requires legalCommittee(the_members);
        //@ ensures members ==  the_members;
        //@ assignable \everything;
        public Thesis(final int the_members) {
        my_members = the_members;
        }
    
    
    // ******************************************************************************** METHODS WITH SPECIFICATIONS *********************************************************************************\
    
        /**
         * @return The current student duration selected in minutes.
         */
    
        //@ ensures \result == minutes;
        public /*@ pure */ int durationInMinutes() {
        return my_duration;
        }
    
         /**
         * @return The current student duration selected in seconds.
         */
    
        //@ ensures \result == minutes * 60;
        public /*@ pure */ int durationInSeconds() {
        return my_duration * 60;
        }
    
        /**
         * Set the number of Committee Members.
         */
    
        //@ requires members >= MIN_MEMBERS && members <= MAX_MEMBERS;
        //@ modifies members;
        //@ ensures members == the_members;
        //@ signals_only \nothing;
        protected void setMembers(final int the_members) {
        my_members = the_members;
        }
    
        /**
         * Check the student is Arjun Mitra Reddy Donthala
         */
    
        //@ ensures name.equals("Arjun Mitra Reddy");
        public static void student(String name) {
        }
    
        /**
         * Check the chair is Dr. Gary T. Leavens
         */
    
        //@ also ensures name.equals("Dr. Gary T. Leavens");
        public static void chair(String name) {
        }
    
        /**
         * Check the chair is Dr. Gary T. Leavens
         */
    
        //@ ensures name1.equals("Dr. Sumit Kumar Jha") && name2.equals("Dr. Damla Turgut");
        public static void remainingMembers (String name1, String name2) {
        }
    
    // ******************************************************************************** ENUMS *********************************************************************************\
    
        /** Thesis Nested Enum */
        public static enum NestedEnum { THESIS, DEFENSE }
    
    // ******************************************************************************** ANNOTATIONS *********************************************************************************\
        
        public static @interface Annotation1 {}
        
        public static @interface Annotation2 {}
        
    // ******************************************************************************** NESTED CLASSES *********************************************************************************\

        @Pure
        static public class FormalMethods {

        //@invariant false && true;
    }
    
    // ******************************************************************************** NESTED INTERFACE *********************************************************************************\

        @Pure
        public static interface ResearchArea { /*@ invariant false; */ }
    
        @Pure
        public static interface ResearchTopic { /*@ invariant false; */ }
 
    // ******************************************************************************** EXAMPLES *********************************************************************************\
 
    
 
    // ******************************************************************************** MODEL CONSTRUCTORS *********************************************************************************\
  
        //@ requires i == 0.0;
        //@ model public Thesis(float i) {}

        //@ requires i == null;
        //@ model public Thesis(Object i) {}
 
    
    // ******************************************************************************** MODEL METHODS *********************************************************************************\
           
    
    
        /*@ ensures \result <==> the_members > MIN_MEMBERS && the_members < MAX_MEMBERS;
        public pure model boolean legalCommittee(int the_members);
         */
    
        //@ also
        //@ requires true;
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
        
    // ******************************************************************************** MODEL FIELDS *********************************************************************************\
    
        /*@
        public secret model int room;
        secret represents room = 0;
        */
    
        /*@
        public model String building;
         */
    
        /*@
        public secret model boolean value;
        secret represents value = false;
         */
    

    // ******************************************************************************** GHOST FIELDS *********************************************************************************\

        /*@
        public ghost String Arjun;
         */

        /*@
       public ghost String DrGary;
         */
        
    // ******************************************************************************** MODEL ANNOTATIONS *********************************************************************************\
        
        //@ model public @interface ModelAnnotation1 {}
        
        //@ model public @interface ModelAnnotation2 {}
        
    
    // ******************************************************************************** MODEL CLASSES *********************************************************************************\
    
        /** Documentation for model nested class JMLdoc*/
        //@ static model public class JMLdoc { invariant true;  void jmlzzz() {} }
        
        
        /** Documentation for model nested class OpenJML*/
        //@ static model public class OpenJML {}
            
    
    // ******************************************************************************** MODEL INTERFACES *********************************************************************************\
    
        /** Documentation for a model nested interface 1. */
        //@ model public static interface ModelNestedInterface1 {}
        
        /** Documentation for a model nested interface 2. */
        //@ model public static interface ModelNestedInterface {}
    

    
    

}
    