package org.jmlspecs.openjml;

import com.sun.tools.javac.util.Context;
import java.util.*;

// CAUTION: This class is instantiated before options are read, so its construction must not depend on options.
// During the reading of options, the settings in here may be adjusted 

public class InferCategory {

    protected Context context;
    
    public boolean showInferred = true;
    
    private static Context.Key<InferCategory> inferKey = new Context.Key<InferCategory>();
    
    public static InferCategory instance(Context context) {
        var w = context.get(inferKey);
        if (w == null) {
            w = new InferCategory();
            w.context = context;
            context.put(inferKey, w);
        }
        return w;
    }

    // Infer-keys
    public static final String LOOP_ASSIGNS = "loop-assigns";
    public static final String LOOP_DECREASES = "loop-decreases";

    public static enum InferAction { NO, YES };
    public static Map<String, InferAction> init(Map<String, InferAction> map) {
        if (map == null) map = new java.util.TreeMap<>();
        map.put(LOOP_ASSIGNS, InferAction.YES);
        return map;
    }

    public Map<String,InferAction> inferKeys;
    {
        inferKeys = init(null);
    }
    
    public void reset() {
        init(inferKeys);
    }
    
    public void setAll(InferAction a) {
        for (var k: inferKeys.keySet()) inferKeys.put(k, a);
    }
    
    public String list() {
        var sb = new java.lang.StringBuilder();
        sb.append("Value\tDefault\tKey").append("\n");
        var defaultKeys = init(null);
        TreeSet<String> keys = new TreeSet<>(inferKeys.keySet());
        for (String k: keys) {
            sb.append(inferKeys.get(k)).append("\t").append(defaultKeys.get(k)).append("\t").append(k).append("\n");
        }
        return sb.toString();
    }
    
    public String help() {
        return  "Help: --help=infer   Subcommands: none all list reset show\n" + 
                "Implemented specification inference keys: " + InferCategory.instance(context).inferKeys.keySet();
    }

    public InferAction action(String key) {
        InferAction b = inferKeys.get(key);
        if (b != null) {
            return b;
        }
        Utils.instance(context).error("jml.internal.not.so.bad","Invalid warning key: " + key);
        return InferAction.NO;
    }
}
