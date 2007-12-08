package java.util;

// FIXME - It is possible through the Map interface to add keys or values
// that are not non-null Strings.  These will cause other operations to fail,
// but there is nothing in the specification to indicate that.

public class Properties extends Hashtable{

    /*@ public normal_behavior
      @   ensures \result <==> ( initialHashtable() &&
      @                          isEmpty() && defaults == p);
      @ public pure model boolean initialProperties(Properties p);
      @*/

    //@ spec_public
    protected Properties defaults;

    //@ public normal_behavior
    //@    ensures initialProperties(null);
    //@ pure
    public Properties();

    //@ public normal_behavior
    //@   ensures initialProperties(p);
    //@ pure
    public Properties(Properties p);

    public synchronized void load(java.io.InputStream in)
       throws java.io.IOException;

    public void list(java.io.PrintStream out);

    public void list(java.io.PrintWriter out);

    public java.util.Enumeration propertyNames();

    public synchronized void save(java.io.OutputStream out, String s);

    public synchronized void store(java.io.OutputStream out, String s)
       throws java.io.IOException;


    /*@ public normal_behavior
      @   requires name != null;
      @*/
    /*-@ also public normal_behavior
      @   requires name != null;
      @   ensures (!content.hasMap(name) && defaults == null) ==> 
                                        \result == null;
      @   ensures (!content.hasMap(name) && defaults != null) ==> 
                                        \result == defaults.getProperty(name);
      @   ensures content.hasMap(name) ==> \result == content.maps(name);
      @*/
    /*@ also public exceptional_behavior
      @   requires name == null;
      @   signals_only NullPointerException;
      @*/
    //@ pure
    public String getProperty(String name) throws NullPointerException;

    /*@ public normal_behavior
      @   requires name != null && value != null;
      @   assignable objectState;
      @*/
    /*-@ also public normal_behavior
      @   requires name != null && value != null;
      @   assignable objectState;
      @   ensures content.hasMap(name);
      @   ensures !\old(content.hasMap(name)) ==> 
                              content.theSize == \old(content.theSize + 1);
      @   ensures \old(content.hasMap(name)) ==> 
                              content.theSize == \old(content.theSize);
      @   ensures content.maps(name) == value;
      @   ensures (\forall String s; !name.equals(s) ==> 
                           (content.hasMap(s) <==> \old(content.hasMap(s)))); 
            // FIXME - likely needs more, but cleanup Map first
      @*/
    /*@ also public exceptional_behavior
      @   requires name == null || value == null;
      @   assignable \not_specified;
      @   signals_only NullPointerException;
      @*/
    public synchronized Object setProperty(String name, String value) throws NullPointerException;

    //@ public normal_behavior
    //@   requires name != null;
    //@   ensures !containsKey(name) ==> \result == def;
    //@   ensures containsKey(name) ==> \result == get(name);
    //@ also public exceptional_behavior
    //@   requires name == null;
    //@   signals_only NullPointerException;
    //@ pure
    public String getProperty(String name, String def) throws NullPointerException;
}
