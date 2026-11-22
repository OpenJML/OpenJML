// The .jml initializer of a static field disagrees with its value after static initialization (#774);
// RAC and ESC (in <clinit>, #1152) check it at the end of static initialization
public class A {
    static int si = 5;
    static int sj = si++;
    public static void main(String... a) { System.out.println("END " + sj); }
}
