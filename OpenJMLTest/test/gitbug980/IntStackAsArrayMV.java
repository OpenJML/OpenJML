// Issue #980, reduced from the reporter's example: frame clauses indexing a \seq model field declared in an
// interface ('reads size, elems[n]', 'assignable elems[n]'), implemented through 'maps _elems[*] \into elems',
// made z3 reject the SMT script (an '=' between REF and (Array Int REF)). (The reporter's full example also has
// postconditions that cannot be proved, since elems has no represents clause; their failures come in a
// varying order, so they are left out.) The test pins that there is no SMT error and the semantics:
// elems[n] stands for _elems[n] (maps), not for the field _elems (in), so nthElement fails
// 'Accessible ... _elems' while nthElement2, which also lists elems, verifies; set may write _elems[n].
public class IntStackAsArrayMV implements IntStackMV {

    private int _size; //@ in size;
    //@ private represents size = _size;
    private int _elems[]; //@ in elems; //@ maps _elems[*] \into elems;

    //@ private invariant _elems.length == MAX_SIZE;
    //@ private invariant 0 <= _size <= MAX_SIZE;

    public IntStackAsArrayMV() {
        _size = 0;
        _elems = new int[MAX_SIZE];
    }

    public int nthElement(int n) {
        return _elems[n];
    }

    public int nthElement2(int n) {
        return _elems[n];
    }

    public void set(int n, int i) {
        _elems[n] = i;
    }
}
