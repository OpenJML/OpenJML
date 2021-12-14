public class Test {
	
	int f;
	int /*@ nullable*/[] a;
	
	public void m() {
		int h;
		//@ ghost \locset f1 = \set_union();
		//@ ghost var f2 = \set_union(\locset(this.f),\locset(h));
		//@ ghost \locset f3 = \set_union(\locset(this.f),\locset(a[*]),\locset(a[1..2]),\locset(a[1]),f2);
		//@ ghost \locset f4 = \set_union(\locset(this.*),0);
		//@ ghost var f5 = \set_union(\locset(this.f,h));
		//@ ghost boolean b = \subset(f1,f3);
		//@ ghost boolean bb = \subset(f1,f3,f5) || \subset(f1) || \subset(f1,0);
		
	}
	
	
}