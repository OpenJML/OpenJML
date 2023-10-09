package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseCallable;
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.List;

public class CallableClauseExtension extends JmlExtension {

    public static final String callableID = "callable";
    
    public static final IJmlClauseKind callableClause = new IJmlClauseKind.MethodSpecClauseKind(callableID) {
        @Override
        public boolean oldNoLabelAllowed() { return false; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public JmlMethodClauseCallable parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            int pe = parser.endPos();
            init(parser);
            
            parser.warnNotImplemented(pp, keyword, "JmlParser");
            parser.nextToken();
            var n = parser.parseOptionalName();

            JmlSingleton refkeyword = parser.parseOptStoreRefKeyword();
            List<JmlMethodSig> sigs = null;
            if (refkeyword == null) {
                sigs = parseMethodNameList();
            }
            JmlMethodClauseCallable ec;
            if (refkeyword != null) {
                ec = parser.maker().at(pp).JmlMethodClauseCallable(refkeyword);
            } else {
                ec = parser.maker().at(pp).JmlMethodClauseCallable(sigs);
            }
            wrapup(ec, clauseType, true, true);
            ec.name = n;
            return ec;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
