package org.jmlspecs.openjml;

import com.sun.tools.javac.util.Context;
import java.util.*;

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

    // Warning-keys
    public static final String IMPLICIT_EVERYTHING = "implicit-everything";
    public static final String MISSING_MEASURED_BY = "missing-measured-by";
    public static final String MISSING_SPECS = "missing-specs";
    public static final String MISSING_SEMICOLON = "missing-semicolon";

    public static enum WarnAction { QUIET, WARN, ERROR };
    public static Map<String, WarnAction> init(Map<String, WarnAction> map) {
        if (map == null) map = new java.util.TreeMap<>();
        map.put(MISSING_SPECS, WarnAction.QUIET);
        map.put(IMPLICIT_EVERYTHING, WarnAction.WARN);
        map.put(MISSING_MEASURED_BY, WarnAction.QUIET);
        return map;
    }

    public Map<String,WarnAction> warningKeys;
    {
        warningKeys = init(null);
    }
    
    public void reset() {
        init(warningKeys);
    }
    
    public void setAll(WarnAction a) {
        for (var k: warningKeys.keySet()) warningKeys.put(k, a);
    }
    
    public String list() {
        var sb = new java.lang.StringBuilder();
        sb.append("Value\tDefault\tKey").append("\n");
        var defaultKeys = init(null);
        TreeSet<String> keys = new TreeSet<>(warningKeys.keySet());
        for (String k: keys) {
            sb.append(warningKeys.get(k)).append("\t").append(defaultKeys.get(k)).append("\t").append(k).append("\n");
        }
        return sb.toString();
    }

    public WarnAction allowed(String key) {
        WarnAction b = warningKeys.get(key);
        if (b != null) {
            return b;
        }
        Utils.instance(context).error("jml.internal.not.so.bad","Invalid warning key: " + key);
        return WarnAction.WARN;
    }

}
