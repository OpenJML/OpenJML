public class Arr {


public static void main(String ... args) {

//@ ghost array<Short> arx = args.array; // ERROR
Integer[] a = new Integer[10];
//@ ghost array<Integer> ar = a.array; // OK

}
}
