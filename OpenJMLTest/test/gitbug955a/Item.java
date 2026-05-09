public class Item {
    //@ spec_public
    private final String name;
    //@ requires name != null;
    //@ assignable \nothing;
    //@ ensures name() == name;
    public Item(String name) { this.name = name; }
    /*@ public normal_behavior ensures \result == name; helper spec_pure @*/
    public String name() { return name; }
}
