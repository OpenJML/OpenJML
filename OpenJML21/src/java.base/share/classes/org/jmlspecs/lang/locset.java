package org.jmlspecs.lang;

//@ immutable pure 
public abstract class locset implements IJmlPrimitiveType {
	
	private locset() {}
	
    abstract public boolean contains(locset x);

    public static boolean empty() { return false; }
    
//    static public locset locset() { return new locset(); }
        
    public static boolean eq(locset s, locset ss) { return s.equals(ss); }
    
    abstract public boolean eq(locset s);
    
    abstract public locset add(locset x);
    
    abstract public locset remove(location x);    
}
