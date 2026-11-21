// The .jml initializer of a static field disagrees with its value after static initialization (#774);
// RAC checks it at the end of static initialization; ESC will with #1152
public class A {
    static int si = 5;
    static int sj = si++;
    public static void main(String... a) { System.out.println("END " + sj); }
}
