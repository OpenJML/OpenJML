package org.jmlspecs.openjml;

import java.util.ArrayList;
import java.util.Collection;

import javax.tools.JavaFileObject;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;

public class Nowarns {

    /** The key to use to retrieve the instance of this class from the Context object. */
    //@ non_null
    public static final Context.Key<Nowarns> nowarnsKey =
        new Context.Key<Nowarns>();

    /** A method that returns the unique instance of this class for the given Context
     * (creating it if it does not already exist).
     * 
     * @param context the Context whose Nowarns instance is wanted
     * @return the singleton instance (per Context) of this class
     */
    //@ non_null
    public static Nowarns instance(Context context) {
        Nowarns instance = context.get(nowarnsKey);
        if (instance == null) {
            instance = new Nowarns(context);
            context.put(nowarnsKey, instance);
        }
        return instance;
    }
    
    public static class Item {
        /*@Nullable*/ DiagnosticSource source;
        int line;
        String label;
        public Item(DiagnosticSource source, int line, String label) {
            this.source = source;
            this.line = line;
            this.label = label;
        }
    }

    protected Context context;
    
    protected Collection<Item> nowarns = new ArrayList<Item>();

    protected Nowarns(Context context) {
        this.context = context;
    }
    
    public void addItem(DiagnosticSource file, int pos, String label) {
        nowarns.add(new Item(file,file.getLineNumber(pos),label));
    }
    
    public boolean suppress(DiagnosticSource file, int pos, String label) {
        for (Item i: nowarns) {
            if (!label.equals(i.label)) {
                // continue
            } else if (i.source == null) {
                return true;
            } else {
                if (file.equals(i.source) && file.getLineNumber(pos) == i.line) return true; 
            }
        }
        return false;
    }

    public boolean suppress(JavaFileObject file, int pos, String label) {
        for (Item i: nowarns) {
            if (!label.equals(i.label)) {
                // continue
            } else if (i.source == null) {
                return true;
            } else {
                if (file.equals(i.source.getFile()) && i.source.getLineNumber(pos) == i.line) return true; 
            }
        }
        return false;
    }

}
