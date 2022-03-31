import org.jmlspecs.lang.seq;

public class Linked {
    //@ model public seq<Linked> links;
    //@ public represents links = next == null ? seq.<Linked>empty() : next.links.prepend(next);
    
	//@ nullable
	public Linked next;//@ in links; 
	
    public seq<Linked> jlinks;


	// BUG: This did not report a missing declaration for 'oldlinks'
	
    //@ public normal_behavior
    //@   ensures this.links.equals(oldlinks.prepend(this.next));
	public void push() {
	    var b = this.jlinks.equals(oldjlinks.prepend(this.next));
	}
    

}