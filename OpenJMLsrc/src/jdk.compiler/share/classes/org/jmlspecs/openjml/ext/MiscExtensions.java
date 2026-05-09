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
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class MiscExtensions extends JmlExtension {

    public static class NoTypeMisc extends IJmlClauseKind.SingletonKind {
        public NoTypeMisc(String name) { super(name); }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return Type.noType;
        }
    };

//    public static class NotImplemented extends IJmlClauseKind.SingletonKind {
//        public NotImplemented(String name) { super(name); }
//        
//        @Override
//        public JCTree parse(JCModifiers mods, String keyword,
//                IJmlClauseKind clauseType, JmlParser parser) {
//            parser.warnNotImplemented(parser.pos(), this.keyword(),
//                    "JmlParser.term3(), as type modifiers");
//            return super.parse(mods, keyword, clauseType, parser);
//        }
//        @Override
//        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
//            return Type.noType;
//        }
//    };

//    public static final String constructorID = "constructor";
//    public static final IJmlClauseKind constructorKind = new NoTypeMisc(constructorID);
//    
//    public static final String fieldID = "field";
//    public static final IJmlClauseKind fieldKind = new NoTypeMisc(fieldID);
//    
//    public static final String methodID = "method";
//    public static final IJmlClauseKind methodKind = new NoTypeMisc(methodID);
    
    public static final String intoID = "\\into";
    public static final IJmlClauseKind intoKind = new NoTypeMisc(intoID);
    
    public static final String suchthatID = "\\such_that";
    public static final IJmlClauseKind suchthatKind = new NoTypeMisc(suchthatID);

    public static final String bspeerID = "\\peer";
    public static final IJmlClauseKind bspeerKind = new NoTypeMisc(bspeerID);
    
    public static final String bsrepID = "\\rep";
    public static final IJmlClauseKind bsrepKind = new NoTypeMisc(bsrepID);

}

