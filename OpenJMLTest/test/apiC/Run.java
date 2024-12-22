public class Run {
    
    public static void main(String... args) {
        int x = org.jmlspecs.openjml.Main.execute("--rac","--progress","-jmltesting","A.java");
        System.exit(x==1 ? 0 : 1);
    }
}
