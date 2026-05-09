/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;

public class Operators extends JmlExtension {

    public static class Operator extends IJmlClauseKind.SingletonKind {
        public int precedence;
        public Operator(String name, int precedence) { super(name); this.precedence = precedence; }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return Type.noType;
        }
    };
    
    public static final String equivalenceID = "<==>";
    public static final Operator equivalenceKind = new Operator(equivalenceID, -2);
    
    public static final String inequivalenceID = "<=!=>";
    public static final Operator inequivalenceKind = new Operator(inequivalenceID, -2);
    
    public static final String impliesID = "==>";
    public static final Operator impliesKind = new Operator(impliesID, -2);
    
    public static final String reverseimpliesID = "<==";  // FIXME - removed
    public static final Operator reverseimpliesKind = new Operator(reverseimpliesID, -2);
    
    public static final String subtypeofID = "<:";
    public static final Operator subtypeofKind = new Operator(subtypeofID, 10);
    
    public static final String subtypeofeqID = "<:=";
    public static final Operator subtypeofeqKind = new Operator(subtypeofeqID, 10);
    
    public static final String jsubtypeofID = "<::";
    public static final Operator jsubtypeofKind = new Operator(jsubtypeofID, 10);
    
    public static final String jsubtypeofeqID = "<::=";
    public static final Operator jsubtypeofeqKind = new Operator(jsubtypeofeqID, 10);
    
    public static final String lockltID = "<#";
    public static final Operator lockltKind = new Operator(lockltID, 10);
    
    public static final String lockleID = "<#=";
    public static final Operator lockleKind = new Operator(lockleID, 10);

    public static final String wfltID = "<<<";
    public static final Operator wfltKind = new Operator(wfltID, 10);
    
    public static final String wfleID = "<<<=";
    public static final Operator wfleKind = new Operator(wfleID, 10);
    
    public static final String dotdotID = "..";
    public static final Operator dotdotKind = new Operator(dotdotID, -1000);
    
    public static final String leftarrowID = "<-";
    public static final IJmlClauseKind leftarrowKind = new Operator(leftarrowID, -1000);
    
    // FIXME -- should be with punctuation?
    public static final String endjmlcommentID = "@*/"; // Also represents a newline at the end of a LINE comment
    public static final IJmlClauseKind endjmlcommentKind = new Operator(endjmlcommentID, -1000);

    public static final String startjmlcommentID = "/*@"; // Also represents a newline at the end of a LINE comment
    public static final IJmlClauseKind startjmlcommentKind = new Operator(startjmlcommentID, -1000);

}

