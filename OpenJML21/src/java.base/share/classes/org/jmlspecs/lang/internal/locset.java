package org.jmlspecs.lang.internal;
import org.jmlspecs.lang.IJmlPrimitiveType;

// FIXME - needs implementaiotn

//@ no_state
public class locset implements IJmlPrimitiveType {
	
    private locset() {}

    public boolean contains(locset x) { return false; }

    public static locset empty() { return new locset(); }

    public static boolean eq(locset s, locset ss) { return s.equals(ss); }

    public boolean eq(locset s) { return true; }

    public locset add(locset x) { return this; }

    public locset remove(location x)  { return this; }
}
