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
    
    public SecurityType(int tag, TypeSymbol tsym, String level) {
        super(tag, tsym);
        this.level = level;
    }

    
}
