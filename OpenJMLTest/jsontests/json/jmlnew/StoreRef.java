// Exercises JmlStoreRefArrayRangeAdapter (a[lo..hi]) and
// JmlStoreRefKeywordAdapter (\nothing, \everything).
public class StoreRef {
    int[] a;
    int b;

    //@ public normal_behavior
    //@   writes a[0..2], b;
    //@ also public normal_behavior
    //@   writes \nothing;
    public void single() {}

    //@ public normal_behavior
    //@   writes a[1..3], a[*], \everything;
    public void multi() {}

    //@ public normal_behavior
    //@   writes a[0..], \nothing;
    public void openRange() {}
}
