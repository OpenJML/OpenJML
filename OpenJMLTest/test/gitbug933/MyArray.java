public class MyArray {
    private /*@ spec_public @*/ int arr[];

    //@ ensures \fresh(arr);
    //@ ensures arr.length == 5;
    //@ ensures \forall int i; 0 <= i < 5; arr[i] == 0;
    public MyArray(){
        arr = new int[5];
        int i;
        //@ maintaining \forall int j; 0 <= j < i; arr[j] == 0;
        //@ loop_writes arr[*], i;
        //@ decreases 5 - i;
        for(i = 0; i < 5; i++) {
            arr[i] = 0;
        }
    }
    
    //@ ensures \fresh(arr);
    //@ ensures arr.length == 5;
    //@ ensures \forall int i; 0 <= i < 5; arr[i] == 0;
    public MyArray(short z){
        arr = new int[5];
        //@ maintaining \forall int j; 0 <= j < i; arr[j] == 0;
        //@ loop_writes arr[*];
        //@ decreases 5 - i;
        for(int i = 0; i < 5; i++) {
            arr[i] = 0;
        }
    }

    //@ ensures \fresh(arr);
    //@ ensures arr.length == 5;
    //@ ensures \forall int i; 0 <= i < 5; arr[i] == 0;
    public MyArray(int zzz){
        arr = new int[5];
        //@ maintaining 0 <= i;
        //@ maintaining \forall int j; 0 <= j < i; arr[j] == 0;
        //@ loop_writes arr[*];
        //@ decreases 5 - i;
        for(int i = 0; i < 5; i++) {
            arr[i] = 0;
        }
    }

}
