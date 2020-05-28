/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.VAL;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.RPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.VOID;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlExpression;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.ext.FunctionLikeExpressions.AnyArgBooleanExpressions;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.Infer;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.Attr.ResultInfo;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

/** This class handles expression extensions that take an argument list of JCExpressions.
 * Even if there are constraints on the number of arguments, it
 * is more robust to accept all of them and then issue an error in the typechecker
 * if the number of arguments is wrong.
 * 
 * @author David Cok
 *
 */// TODO: This extension is inappropriately named at present.  However, I expect that this 
// extension will be broken into individual extensions when type checking and
// RAC and ESC translation are added.
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
    
    public static final String specgroupstartID = "{|";
    public static final IJmlClauseKind specgroupstartKind = new Operator(specgroupstartID);
    
    public static final String specgroupendID = "|}";
    public static final IJmlClauseKind specgroupendKind = new Operator(specgroupendID);
    
    public static final String endjmlcommentID = "@*/";
    public static final IJmlClauseKind endjmlcommentKind = new Operator(endjmlcommentID);

}

