/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.IJmlLoop;
import org.jmlspecs.openjml.JmlTree.JmlInlinedLoop;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.List;

public class InlinedLoopStatement extends JmlExtension implements IJmlLoop {

    public boolean isSplit() { return false; }
    public void setSplit(boolean s) {}
    
    public static final String inlinedloopID = "inlined_loop";
    
    public List<JmlStatementLoop> loopSpecs;

    @Override
    public List<JmlStatementLoop> loopSpecs() {
        return loopSpecs;
    }
    
    @Override
    public JCTree.JCStatement body() {
        return null;
    }

    @Override
    public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) {
        this.loopSpecs = loopSpecs;
    }

    public static final IJmlClauseKind inlinedLoopStatement = new IJmlClauseKind.Statement(inlinedloopID) {
        public JmlInlinedLoop parse(JCModifiers mods, String id, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();
            int pe = parser.endPos();
            parser.nextToken();
            JmlInlinedLoop st = parser.maker().at(pp).JmlInlinedLoop(null);
            wrapup(st,clauseType,true);
            return st;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            return null;
        }
    };
}
