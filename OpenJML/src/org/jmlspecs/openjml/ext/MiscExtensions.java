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
public class MiscExtensions extends JmlExtension {

    public static class NoTypeMisc extends IJmlClauseKind.SingletonKind {
        public NoTypeMisc(String name) { super(name); }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return Type.noType;
        }
    };

    public static class NotImplemented extends IJmlClauseKind.SingletonKind {
        public NotImplemented(String name) { super(name); }
        
        @Override
        public JCTree parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseType, JmlParser parser) {
            parser.warnNotImplemented(parser.pos(), this.name(),
                    "JmlParser.term3(), as type modifiers");
            return super.parse(mods, keyword, clauseType, parser);
        }
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return Type.noType;
        }
    };

    public static final String notspecifiedID = "\\not_specified";
    public static final IJmlClauseKind notspecifiedKind = new IJmlClauseKind.SingletonKind(notspecifiedID) {
        // \not_specified can be used in place of an expression, so it needs to return a type. We use an error type
        // so that no error messages are propagated
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return attr.syms.errType;
        }
    };
    
    public static final String nothingID = "\\nothing";
    public static final IJmlClauseKind nothingKind = new NoTypeMisc(nothingID);
    
    public static final String everythingID = "\\everything";
    public static final IJmlClauseKind everythingKind = new NoTypeMisc(everythingID);
    
    public static final String constructorID = "constructor";
    public static final IJmlClauseKind constructorKind = new NoTypeMisc(constructorID);
    
    public static final String fieldID = "field";
    public static final IJmlClauseKind fieldKind = new NoTypeMisc(fieldID);
    
    public static final String methodID = "method";
    public static final IJmlClauseKind methodKind = new NoTypeMisc(methodID);
    
    public static final String intoID = "\\into";
    public static final IJmlClauseKind intoKind = new NoTypeMisc(intoID);
    
    public static final String suchthatID = "\\such_that";
    public static final IJmlClauseKind suchthatKind = new NoTypeMisc(suchthatID);

    public static final String bspeerID = "\\peer";
    public static final IJmlClauseKind bspeerKind = new NoTypeMisc(bspeerID);
    
    public static final String readonlyID = "readonly";
    public static final IJmlClauseKind readonlyKind = new NoTypeMisc(readonlyID);

    public static final String bsreadonlyID = "\\readonly";
    public static final IJmlClauseKind bsreadonlyKind = new NoTypeMisc(bsreadonlyID);

    public static final String bsrepID = "\\rep";
    public static final IJmlClauseKind bsrepKind = new NoTypeMisc(bsrepID);

}

