public class Test {
    
    static {}
    {}
    
}
interface B {}
enum C { X, Y}
record D(int i) {}
class A extends B implements C, D {}
// FIXME - more complex enum and record; 
