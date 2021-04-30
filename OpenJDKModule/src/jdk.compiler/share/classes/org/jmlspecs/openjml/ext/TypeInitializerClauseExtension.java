package org.jmlspecs.openjml.ext;


import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class TypeInitializerClauseExtension extends JmlExtension {

    public static final String initializerID = "initializer";
    public static final String staticinitializerID = "static_initializer";

    public static final IJmlClauseKind initializerClause = new InitializerBlock(initializerID);
    
    public static final IJmlClauseKind staticinitializerClause = new InitializerBlock(staticinitializerID);
    
    private static class InitializerBlock extends IJmlClauseKind.TypeClause {
        public InitializerBlock(String keyword) { super(keyword); }
        
        public 
        JmlTypeClauseInitializer parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            init(parser);
            parser.nextToken(); // skip over initializer token
            JmlTypeClauseInitializer initializer = parser.maker().at(pp).JmlTypeClauseInitializer(clauseType,mods);
            //@ FIXME - parse failure?
            initializer.specs = parser.currentMethodSpecs;
            parser.currentMethodSpecs = null;
            initializer = parser.to(initializer);
            // FIXME parser.list.append(initializer);
            wrapup(initializer, clauseType, false);
            return initializer;
        }
        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
