/*
 * This file is part of the OpenJML plugin project. 
 * Copyright 2006-2010 David R. Cok
 * 
 * Created on November 21, 2006
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Collection;
import java.util.LinkedList;

import org.eclipse.jface.preference.IPreferenceStore;

/**
 * This is a base class for persistent options.  The options are
 * stored as workspace preferences.
 * 
 * @author David R. Cok
 */
public class AbstractPreference {

    /** A reference to the plugin's preference store */
    // FIXME - do we need to worry about concurrent accesses into this structure
    public final static IPreferenceStore preferenceStore = Activator.getDefault().getPreferenceStore();

    /** The name used as the key into the 
     * persistent store for the value of the option.
     */
    //@ non_null
    protected String key;

    /** The label to use for the widget */
    //@ non_null
    protected String label;

    /** The tooltip help for the widget */
    //@ non_null
    protected String tooltip;

    /**
     * The protected constructor used by derived classes
     * @param key  The name used as a preference key
     * @param label  A short description suitable as a label
     * @param tooltip  A longer description suitable as help
     */
    protected AbstractPreference(String key, String label, String tooltip) {
        this.key = key;
        this.label = label;
        this.tooltip = tooltip;
    }

    /** An interface for the listeners that are fired when options change.*/
    static public interface Listener {
        /** The method executed when the listener is notified. */
        public void run();
    }

    /** The listeners that will be notified when options change. */
    static private Collection<Listener> listeners = new LinkedList<Listener>();

    /** Adds a listener to the collection of listeners.
     * 
     * @param l Listener to be added
     */
    static synchronized public void addListener(Listener l) {
        listeners.add(l);
    }

    /** Adds a listener to the collection of listeners.
     * 
     * @param l Listener to be removed
     */
    static synchronized public void removeListener(Listener l) {
        listeners.remove(l);
    }

    /** Executes all listeners */
    static synchronized public void notifyListeners() {
        for (Listener i: listeners) {
            i.run();
        }
    }

    /** Returns the label string (short description) for this option
     * 
     * @return the label string
     */
    public String label() { return label; }

    /** Returns the help string for this option
     * 
     * @return the help string
     */
    public String tooltip() { return tooltip; }

    /** Sets the option to its default value */
    public void setToDefault() {
        preferenceStore.setToDefault(key);
    }

    /** An option that has a boolean value */
    static public class BooleanOption extends AbstractPreference {

        /**
         * Creating a boolean option object
         * @param key  The name used as a preference key
         * @param def  The default value used if no value is previously stored
         * @param label A short description usable as a label
         * @param tooltip A long description usable as help
         */
        public BooleanOption(String key, boolean def,
                String label, String tooltip) {
            super(key,label,tooltip);
            preferenceStore.setDefault(key,def);
        }

        /**
         * Returns the current value of the option 
         * @return The current value of the option
         */
        public boolean getValue() { return preferenceStore.getBoolean(key); }

        /**
         * Sets the workspace property value to the given value.
         * 
         * @param b The value to set
         */
        public void setValue(boolean b) { preferenceStore.setValue(key,b); } 

        /** Returns the default value of the preference
         * @return the default value of the preference
         */
        public boolean getDefault() {
            return preferenceStore.getDefaultBoolean(key);
        }

    }

    /** An option that has a int value */
    static public class IntOption extends AbstractPreference {

        /**
         * Creating a int option object
         * @param key  The name used as a preference key
         * @param def  The default value used if no value is previously stored
         * @param label A short description usable as a label
         * @param tooltip A long description usable as help
         */
        public IntOption(String key, int def,
                String label, String tooltip) {
            super(key,label,tooltip);
            preferenceStore.setDefault(key,def);
        }

        /**
         * Returns the current value of the option 
         * @return The current value of the option
         */
        public int getValue() { return preferenceStore.getInt(key); }

        /**
         * Sets the workspace property value to the given value.
         * 
         * @param i The value to set
         */
        public void setValue(int i) { preferenceStore.setValue(key,i); } 

        /** Returns the default value of the preference
         * @return the default value of the preference
         */
        public int getDefault() {
            return preferenceStore.getDefaultInt(key);
        }

    }

    /** An option that has a String value */
    static public class StringOption extends AbstractPreference {

        /**
         * Creating a String option object
         * @param key  The qualified name used as a property key
         * @param def  The default value used if no value is previously stored
         * @param label A short description usable as a label
         * @param tooltip A long description usable as help
         */
        public StringOption(String key, String def,
                String label, String tooltip) {
            super(key,label,tooltip);
            if (def != null) preferenceStore.setDefault(key,def);
        }

        /** Returns the default value of the preference
         * @return the default value of the preference
         */
        public String getDefault() {
            return preferenceStore.getDefaultString(key);
        }

        /**
         * Returns the current value of the option 
         * @return The current value of the option
         */
        public String getValue() { return preferenceStore.getString(key); }

        /**
         * Sets the option value to the given value.
         * 
         * @param v The value to set
         */
        public void setValue(String v) { preferenceStore.setValue(key,v); } 
    }

    /** An option that has one of a set of Strings as its value */
    static public class ChoiceOption extends AbstractPreference {

        /** The choices */
        protected String[] choices;

        /**
         * Creating a String option object
         * @param key  The name used as a preference key
         * @param def  The default value used if no value is previously stored (an index into the array of choices)
         * @param choices The choices (as Strings) to be chosen among
         * @param label A short description usable as a label
         * @param tooltip A long description usable as help
         */
        public ChoiceOption(String key, String[] choices,
                int def,
                String label, String tooltip) {
            super(key,label,tooltip);
            preferenceStore.setDefault(key,choices[def]);
            this.choices = choices;
        }

        /** Returns the array of choices; this array should not be modified.
         * 
         * @return the array of choices
         */
        public String[] choices() { return choices; }

        /** Returns the default value of the preference
         * @return the default value of the preference
         */
        public String getDefault() {
            return preferenceStore.getDefaultString(key);
        }

        /** Returns the default value of the preference
         * @return the default value of the preference
         */
        public int getDefaultIndex() {
            return lookup(preferenceStore.getDefaultString(key));
        }

        /**
         * Returns the current value of the option 
         * @return The current value of the option
         */
        public int getIndexValue() { 
            String r = preferenceStore.getString(key);
            return lookup(r);
        }

        /**
         * Returns the current value of the option 
         * @return The current value of the option
         */
        public String getStringValue() { 
            return preferenceStore.getString(key);
        }

        /**
         * Sets the option value to the given value.
         * 
         * @param v The String value to set
         */
        public void setValue(String v) { preferenceStore.setValue(key,v); }

        /**
         * Sets the option value to the given value.
         * 
         * @param i The index value to set
         */
        //@ requires 0<=i && i<choices.length;
        public void setValue(int i) { preferenceStore.setValue(key,choices[i]); } 

        /**
         * Returns the index in the choices array corresponding
         * to the argument; returns -1 if not found.
         * @param s The String to be sought in the choices array
         * @return The index of the argument in the array
         */
        //@ requires s != null;
        //@ ensures \result != -1 ==> choices[\result].equals(s);
        //@ ensures \result == -1 ==> (\forall int i; 0<=i && i<choices.length; !choices[i].equals(s));
        private int lookup(String s) {
            for (int i=0; i<choices.length; ++i) {
                if (s.equals(choices[i])) return i;
            }
            return -1;
        }
    }
}
