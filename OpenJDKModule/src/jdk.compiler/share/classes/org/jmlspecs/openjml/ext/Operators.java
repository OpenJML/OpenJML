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
        public Operator(String name) { super(name); }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return Type.noType;
        }
    };
    
    public static final String equivalenceID = "<==>";
    public static final IJmlClauseKind equivalenceKind = new Operator(equivalenceID);
    
    public static final String inequivalenceID = "<=!=>";
    public static final IJmlClauseKind inequivalenceKind = new Operator(inequivalenceID);
    
    public static final String impliesID = "==>";
    public static final IJmlClauseKind impliesKind = new Operator(impliesID);
    
    public static final String reverseimpliesID = "<==";
    public static final IJmlClauseKind reverseimpliesKind = new Operator(reverseimpliesID);
    
    public static final String subtypeofID = "<:";
    public static final IJmlClauseKind subtypeofKind = new Operator(subtypeofID);
    
    public static final String subtypeofeqID = "<:=";
    public static final IJmlClauseKind subtypeofeqKind = new Operator(subtypeofeqID);
    
    public static final String jsubtypeofID = "<::";
    public static final IJmlClauseKind jsubtypeofKind = new Operator(jsubtypeofID);
    
    public static final String jsubtypeofeqID = "<::=";
    public static final IJmlClauseKind jsubtypeofeqKind = new Operator(jsubtypeofeqID);
    
    public static final String lockltID = "<#";
    public static final IJmlClauseKind lockltKind = new Operator(lockltID);
    
    public static final String lockleID = "<#=";
    public static final IJmlClauseKind lockleKind = new Operator(lockleID);

    public static final String wfltID = "<<<";
    public static final IJmlClauseKind wfltKind = new Operator(wfltID);
    
    public static final String wfleID = "<<<=";
    public static final IJmlClauseKind wfleKind = new Operator(wfleID);
    
    public static final String dotdotID = "..";
    public static final IJmlClauseKind dotdotKind = new Operator(dotdotID);
    
    public static final String leftarrowID = "<-";
    public static final IJmlClauseKind leftarrowKind = new Operator(leftarrowID);
    
    // FIXME -- should be with punctuation?
    public static final String endjmlcommentID = "@*/"; // Also represents a newline at the end of a LINE comment
    public static final IJmlClauseKind endjmlcommentKind = new Operator(endjmlcommentID);

    public static final String startjmlcommentID = "/*@"; // Also represents a newline at the end of a LINE comment
    public static final IJmlClauseKind startjmlcommentKind = new Operator(startjmlcommentID);

}

