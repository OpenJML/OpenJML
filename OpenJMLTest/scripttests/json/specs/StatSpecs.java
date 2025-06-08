public class StatSpecs {
    
    public void q(int r) {
        //@ refining
        //@  ensures true;
        m(r);
    }
    
    public void qq(int r) {
        //@ refining
        //@  ensures true;
        //@ begin
        m(r);
        //@ end
    }
    
}