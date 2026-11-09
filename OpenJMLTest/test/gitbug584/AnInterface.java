
// RAC must not emit model fields as class-file fields: in an interface such a field
// (non-final) makes the class file invalid (Illegal field modifiers).
interface AnInterface {

    //@ public model instance int size;
    //@ public model instance Object noRep;
    //@ public model static int count;

    //@ ensures \result == size;
    int getSize();

    //@ ensures \result == size;
    int badSize();
}
