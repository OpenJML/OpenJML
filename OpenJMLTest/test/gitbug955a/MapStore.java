public class MapStore implements Store {
    //@ nullable
    private Item stored; //@ in objectState;
    //@ nullable
    @Override public Item find(String name) {
        return (stored != null && stored.name().equals(name)) ? stored : null;
    }
    @Override public void update(Item item) { stored = item; }
}

