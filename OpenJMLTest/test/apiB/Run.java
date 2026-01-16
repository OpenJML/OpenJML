public class Run {
    
    public static void main(String... args) {
        int x = org.openjml.IAPI.openjml("--esc","--progress","-jmltesting","A.java");
        System.exit(x == 6 ? 0 : 1);
    }
}
