//@ non_null_by_default
public class Test {
    
    Test field = new Test();
    int ff;
    
    public Test m() {
        
        return new Test() {
            
            public int fff() { return field.ff; }
        };
    }
    
    public int fff() { return 1; }
    
}