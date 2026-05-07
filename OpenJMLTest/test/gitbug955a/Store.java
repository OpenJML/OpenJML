public interface Store {
    //@ requires name != null;
    //@ ensures \result == null || \result.name().equals(name);
    /*@ spec_pure nullable @*/ Item find(String name);

    //@ requires item != null;
    //@ requires find(item.name()) != null;
    //@ assignable objectState;
    void update(Item item);
}
