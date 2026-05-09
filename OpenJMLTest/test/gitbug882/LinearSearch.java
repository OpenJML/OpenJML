public class LinearSearch {

    //@  requires array != null;
    //@  requires \exists int i; 0 <= i < array.length; array[i] == search;
    //@  ensures array[\result] == search && !\exists int i; 0 <= i < \result; array[i] == search;
    //@ also
    //@  requires array != null;
    //@  requires !(\exists int i; 0 <= i < array.length; array[i] == search);
    //@  ensures \result == -1;
    //@ behaviors disjoint;
    public static int linearSearch(int search, int array[]) {
        int c;
        int location;

        //@ maintaining 0 <= c <= array.length;
        //@ maintaining \forall int i; 0 <= i < c; array[i] != search;
        //@ loop_writes location, c;
        //@ decreases array.length - c;
        for (c = 0; c < array.length; c++) {  
            if (array[c] == search) {
                location = c;
                break;
            }
        }
        if (c == array.length) {
            location = -1;
        }
        return location;
    }
}

