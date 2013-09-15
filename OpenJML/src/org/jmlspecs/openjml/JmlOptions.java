package org.jmlspecs.openjml;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Options;

public class JmlOptions extends Options {

    protected JmlOptions(Context context) {
        super(context);
        defaults();
    }
    
    public static void preRegister(Context context) {
        context.put(Options.optionsKey, new JmlOptions(context));
    }
    
    public void defaults() {
        //System.out.println("SETTING DEFAULTS");
        for (JmlOption opt : JmlOption.values()) {
            Object d = opt.defaultValue();
            if (d == null) continue;
            if (d instanceof Boolean && !(Boolean)d) continue;
            put(opt.optionName(),d.toString());
        }
    }
}
