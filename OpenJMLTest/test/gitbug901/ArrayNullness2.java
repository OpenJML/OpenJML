import org.jmlspecs.annotation.*;
public class ArrayNullness2 {

    //@ spec_public
	private /*@ nullable @*/String /*@ non_null @*/[] s; 

	//@ pure
	public ArrayNullness2() {
		s = null;
	}

	//@ pure
	public ArrayNullness2(int i) {
	}
}
