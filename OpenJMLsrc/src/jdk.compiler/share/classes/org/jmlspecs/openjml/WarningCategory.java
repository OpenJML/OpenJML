package org.jmlspecs.openjml;

import com.sun.tools.javac.util.Context;
import java.util.*;

// CAUTION: This class is instantiated before options are read, so its construction must not depend on options.
// During the reading of options, the settings in here may be adjusted 

public class WarningCategory {

    protected Context context;
    
    private static Context.Key<WarningCategory> warningKey = new Context.Key<WarningCategory>();
    
    public static WarningCategory instance(Context context) {
        var w = context.get(warningKey);
        if (w == null) {
            w = new WarningCategory();
            w.context = context;
            context.put(warningKey, w);
        }
        return w;
    }
    
    public static class Key implements Comparable<Key> { // Comparable needed for the TreeSet
        public String name;
        public Key(String s) { name = s; }
        public String toString() { return name; }
        public boolean equals(Object o) { return o instanceof Key n && name.equals(n.toString()); }
        public int hashCode() { return name.hashCode(); }
        public int compareTo(Key k) { return name.compareTo(k.name); }
    }

    // Warning-keys
    public static final Key NULL = null;
    public static final Key IMPLICIT_EVERYTHING = new Key("implicit-everything");
    public static final Key MISSING_MEASURED_BY = new Key("missing-measured-by");
    public static final Key MISSING_SPECS = new Key("missing-specs");
    public static final Key MISSING_SPECS_PATH = new Key("missing-specs-path");
    public static final Key MISSING_SEMICOLON = new Key("missing-semicolon");
    public static final Key LITERAL_DIV_BY_ZERO = new Key("literal-divide-by-zero");
    public static final Key STRICT_JML = new Key("strict-jml");
    public static final Key JML_LINT = new Key("jml-lint");
    public static final Key DEPRECATED = new Key("deprecated");

    public static enum WarnAction { QUIET, WARN, ERROR };
    public static Map<Key, WarnAction> init(Map<Key, WarnAction> map) {
        if (map == null) map = new java.util.TreeMap<>();
        map.put(MISSING_SPECS, WarnAction.QUIET);
        map.put(MISSING_SPECS_PATH, WarnAction.WARN);
        map.put(IMPLICIT_EVERYTHING, WarnAction.WARN);
        map.put(MISSING_MEASURED_BY, WarnAction.QUIET);
        map.put(MISSING_SEMICOLON, WarnAction.QUIET);
        map.put(LITERAL_DIV_BY_ZERO, WarnAction.WARN);
        map.put(STRICT_JML, WarnAction.WARN);
        map.put(JML_LINT, WarnAction.WARN);
        map.put(DEPRECATED, WarnAction.WARN);
        return map;
    }

    public Map<Key,WarnAction> warningKeys;
    {
        warningKeys = init(null);
    }
    
    public void reset() {
        init(warningKeys);
    }
    
    public void setAll(WarnAction a) {
        for (var k: warningKeys.keySet()) warningKeys.put(k, a);
    }
    
    public boolean containsKey(String s) {
        return warningKeys.get(new Key(s)) != null;
    }
    
    public void put(String s, WarnAction action) {
        warningKeys.put(new Key(s), action);
    }
    
    public String list() {
        var sb = new java.lang.StringBuilder();
        sb.append("Value\tDefault\tKey").append("\n");
        var defaultKeys = init(null);
        TreeSet<Key> keys = new TreeSet<>(warningKeys.keySet());
        for (Key k: keys) {
            sb.append(warningKeys.get(k)).append("\t").append(defaultKeys.get(k)).append("\t").append(k).append("\n");
        }
        return sb.toString();
    }
    
    public String help() {
        return  "Help: --help=warn   Subcommands: none all list reset\n" + 
                "Implemented warning keys: " + WarningCategory.instance(context).warningKeys.keySet();
    }

    public WarnAction action(Key key) {
        if (key == null) return WarnAction.WARN;
        WarnAction b = warningKeys.get(key);
        if (b != null) {
            return b;
        }
        Utils.instance(context).error("jml.internal.not.so.bad","Invalid warning key: " + key);
        return WarnAction.WARN;
    }

    public static boolean isNotQuiet(Context context, Key key) {
        return instance(context).action(key) != WarnAction.QUIET;
    }
}
