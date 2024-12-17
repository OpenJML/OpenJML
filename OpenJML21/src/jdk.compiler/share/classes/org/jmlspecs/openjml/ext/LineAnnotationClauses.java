package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlFactory;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

public class LineAnnotationClauses extends JmlExtension {

    public static final String allowID = "allow";
    public static final String forbidID = "forbid";
    public static final String ignoreID = "ignore";
    //public static final String nowarnID = "nowarn";
    public static final IJmlClauseKind allowClauseKind = new ExceptionLineAnnotationKind(allowID);
    public static final IJmlClauseKind forbidClauseKind = new ExceptionLineAnnotationKind(forbidID);
    public static final IJmlClauseKind ignoreClauseKind = new ExceptionLineAnnotationKind(ignoreID);
    
    //public static final IJmlClauseKind nowarnClauseKind = new ExceptionLineAnnotationKind(nowarnID);
    
    
    public static class ExceptionLineAnnotationKind extends IJmlClauseKind.LineAnnotationKind {
        public ExceptionLineAnnotationKind(String keyword) { super(keyword); }
        
        @Override
        public void scan(int keywordPos, String keyword, IJmlClauseKind clauseKind, JmlScanner scanner) {
            Context context = scanner.context;
            JmlFactory M = JmlTree.Maker.instance(context);
            utils = Utils.instance(context);
            java.util.List<JCExpression> exprs = new java.util.LinkedList<>();
            try {
                int tokenPos = scanner.token().pos;
                Token t = scanner.advance();
                if (t.kind == TokenKind.SEMI || scanner.isEndJml()) {
                    // Empty list
                	// For allow, forbid, ignore, this means RuntimeException
                	JCExpression qid = M.Ident(Names.instance(context).fromString("RuntimeException"));
                	qid.pos = tokenPos;
                	exprs.add(qid);
                } else {
                    while (scanner.jml() && t.kind != TokenKind.SEMI && !scanner.isEndJml()) {
                        if (t.kind != TokenKind.IDENTIFIER){
                            // Bad statement or missing terminating semicolon
                            scanner.jmltokenizer.jmlError(t.pos, scanner.jmltokenizer.errPos(), "jml.bad.line.annotation");
                            // expected identifier
                            // skip to semi
                            while (scanner.token().kind != TokenKind.SEMI && !scanner.isEndJml()) scanner.advance();
                            return;
                        }
                        Name name = t.name();
                        int p = t.pos;
                        t = scanner.advance();
                        {
                            JCExpression qid = M.Ident(name);
                            qid.pos = p;
                            while (t.kind == TokenKind.DOT) {
                                t = scanner.advance();
                                if (t.kind != TokenKind.IDENTIFIER){
                                    // Bad statement or missing terminating semicolon
                                    scanner.jmltokenizer.jmlError(t.pos, scanner.jmltokenizer.errPos(), "jml.bad.line.annotation");
                                    // expected identifier
                                    // skip to semi
                                    while (scanner.token().kind != TokenKind.SEMI && !scanner.isEndJml()) scanner.advance();
                                    return;
                                }
                                qid = M.Select(qid, t.name());
                                qid.pos = t.pos;
                                t = scanner.advance();
                            }
                            exprs.add(qid);
                        }
                        if (t.kind == TokenKind.COMMA){
                            t = scanner.advance();
                        }
                    }
                }
                if (scanner.isEndJml()) { 
                	// allow optional semicolon without a warning
                //    utils.warning(t.pos, "jml.line.annotation.with.no.semicolon");
                    // Here we are swallowing the end of comment - we normally 
                    // expect that token in the stream. However if there is just a 
                    // nowarn, the Java scanner will not expect a standalone ENDJMLCOMMENT
                    // FIXME - check the case of //@ some JML stuff ; nowarn xx 
                    // or with /*@  -- does this parse OK
                } else {
                	scanner.advance(); // read semi
                }
                {
                    ExceptionLineAnnotation a = new ExceptionLineAnnotation();
                    a.line = scanner.jmltokenizer.getLineMap().getLineNumber(keywordPos);
                    a.clauseKind = clauseKind;
                    a.keywordPos = keywordPos;
                    a.exceptionTypes = exprs;
                    scanner.lineAnnotations.add(a);
                }
            } finally {
            }
        }
        
    }
    
    public static class ExceptionLineAnnotation extends IJmlClauseKind.LineAnnotationKind.LineAnnotation {
        java.util.List<JCTree.JCExpression> exceptionTypes = new java.util.LinkedList<>();

        @Override
        public java.util.List<JCExpression> exprs() { return exceptionTypes; }

        @Override
        public Type typecheck(JmlAttr attr, Env<AttrContext> env) {
            for (JCTree.JCExpression e : this.exprs()){  // FIXME - not for nowarn
                e.type = attr.attribType(e,env);
            }
            return null;
        }
    }

}
