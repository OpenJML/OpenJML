public class Run {
    
    public static void main(String... args) {
        org.openjml.IAPI.main("--esc","--progress","-jmltesting","A.java");
        // main above does a System.exit
    }
}
