public class Run {
    
    public static void main(String... args) {
        int x = org.openjml.IAPI.openjml("--rac","--progress","-jmltesting","A.java");
        System.exit(x==1 ? 0 : 1);
    }
}
