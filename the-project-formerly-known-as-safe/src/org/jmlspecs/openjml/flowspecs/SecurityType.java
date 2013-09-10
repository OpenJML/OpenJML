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

    public static int WRONG = 0;
    public static String STR_WRONG = "WRONG";
    public String level;
    private static final int NONE = 0;
    
    public SecurityType(int tag, TypeSymbol tsym) {
        super(tag, tsym);
    }

    public SecurityType(String level) {
        this(NONE, null);
        this.level = level;
    }
    
    public static SecurityType wrong(){
        SecurityType t = new SecurityType("WRONG");
        t.tag = WRONG;
        return t;
    }
    
    @Override
    public String toString()
    {
        return String.format("SecurityType[%s]", level);
    }

}
