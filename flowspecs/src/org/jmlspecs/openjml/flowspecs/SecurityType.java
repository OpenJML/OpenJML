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
        SecurityType t = new SecurityType(STR_WRONG);
        t.tag = WRONG;
        return t;
    }
    
    @Override
    public String toString()
    {
        //TODO - Better formatting??
        return String.format("%s", level);

    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 0; //super.hashCode();
        result = prime * result + ((level == null) ? 0 : level.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        //if (!super.equals(obj)) return false;
        if (!(obj instanceof SecurityType)) return false;
        SecurityType other = (SecurityType) obj;
        if (level == null) {
            if (other.level != null) return false;
        } else if (!level.equals(other.level)) return false;
        return true;
    }
    
    

}
