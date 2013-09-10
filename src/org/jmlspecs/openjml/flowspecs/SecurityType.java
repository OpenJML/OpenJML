package org.jmlspecs.openjml.flowspecs;

import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Type;

/**
 * This class is used to hold security types.
 * 
 * @author John L. Singleton
 *
 */
public class SecurityType extends Type {

    public String level;
    private static final int NONE = 0;
    
    public SecurityType(int tag, TypeSymbol tsym) {
        super(tag, tsym);
    }

    public SecurityType(String level) {
        this(NONE, null);
        this.level = level;
    }

}
