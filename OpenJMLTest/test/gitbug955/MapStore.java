public class MapStore implements Store {
    private Item stored;
    @Override public Item find(String name) {
        return (stored != null && stored.name().equals(name)) ? stored : null;
    }
    @Override public void update(Item item) { stored = item; }
}

