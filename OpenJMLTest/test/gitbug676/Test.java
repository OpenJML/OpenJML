public class Test {
    
    //@ ensures \result >= 0;
    public static int main(String ... args) {
        return args.length;
    }
    
}