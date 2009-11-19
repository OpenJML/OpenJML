package tests;

public class ModelClassExampleBugSub<E> extends ModelClassExampleBug<E> {
    
   /*@ public static model class IndexedContents extends ModelClassExampleBug<E>.Contents {
          public boolean foo() { return false; }
        }
    @*/

    protected ModelClassExampleBugSub() {}

}
