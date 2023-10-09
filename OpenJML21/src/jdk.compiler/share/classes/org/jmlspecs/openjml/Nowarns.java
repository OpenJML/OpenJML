/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.util.ArrayList;
import java.util.Collection;

import javax.tools.JavaFileObject;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;

/** This class records all the Nowarn annotations in an OpenJML compile. Nowarn
 * annotations are syntactic; they can appear anywhere in a line and affect
 * the reporting of warnings and errors against that line.
 */
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
    
    /** A class that holds the record of a particular Nowarn annotation
     * in the code.
     */
    public static class Item {
        /** The source object */
        /*@Nullable*/ DiagnosticSource source;
        /** The 1-based line number of the location of the annotation. */
        int line;
        /** The label contained in the annotation. */
        String label;
        
        /** Constructs the record of a Nowarn annotation */
        public Item(DiagnosticSource source, int line, String label) {
            this.source = source;
            this.line = line;
            this.label = label;
        }
    }

    /** The usual compilation context. */
    protected Context context;
    
    /** The collection of nowarn annotation items. */
    protected Collection<Item> nowarns = new ArrayList<Item>();

    /** Constructor for the (singleton) instance of the Nowarns object; users
     * should not call this - use instance(context).
     */
    protected Nowarns(Context context) {
        this.context = context;
    }
    
    /** Add a new occurrence of an annotation to the record. */
    public void addItem(DiagnosticSource file, int pos, String label) {
        nowarns.add(new Item(file,file.getLineNumber(pos),label));
    }
    
    /** Check the set of annotations to see if a particular warning should be
     * suppressed
     * @return true if there is a recorded annotation with the given source, position and label
     */
    // FIXME - this is an inefficient lookup, and in the following method
    public boolean suppress(DiagnosticSource file, int pos, String label) {
    	//boolean pr = label.contains("Callable");
        int line = file.getLineNumber(pos);
    	//if (pr) System.out.println("SUPPRESS? " + label + " " + pos + " " + line + " " + file.getFile());
        for (Item i: nowarns) {
        	//if (pr && i.label.contains("Callable")) System.out.println("  ITEM " + i.label + " " + i.line + " " + i.source.getFile());
            if (i.label != null && !label.equals(i.label)) {
                // continue
            } else if (i.source == null) {
                return true; // FIXME - don't we check the line number? what use case is this?
            } else {
                if (file.equals(i.source) && line == i.line) return true; 
            }
        }
        //if (pr) System.out.println("   Not suppressed");
        return false;
    }

    /** Check the set of annotations to see if a particular warning should be
     * suppressed
     * @return true if there is a recorded annotation with the given source, position and label
     */
    public boolean suppress(JavaFileObject file, int pos, String label) {
    	//boolean pr = label.contains("Invariant");
    	//if (pr) System.out.println("SUPPRESS? " + label );
        for (Item i: nowarns) {
        	//if (pr && i.label.contains("Invariant")) System.out.println("  ITEM " + i.label + " " + i.line + " " + i.source.getFile() + " " + i.source.getLineNumber(pos));
            if (i.label != null && !label.equals(i.label)) {
                // continue
            } else if (i.source == null) {
                return true;
            } else {
                if (Utils.ifSourcesEqual(file, i.source.getFile()) && i.source.getLineNumber(pos) == i.line) return true; 
            }
        }
        //if (pr) System.out.println("   Not suppressed");
        return false;
    }

}
