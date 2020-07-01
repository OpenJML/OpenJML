package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlFactory;
import org.jmlspecs.openjml.Nowarns;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlTokenizer;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class LineAnnotationClauses extends JmlExtension {

    public static final String allowID = "allow";
    public static final String forbidID = "forbid";
    public static final String ignoreID = "ignore";
    public static final String nowarnID = "nowarn";
    public static final IJmlClauseKind allowClauseKind = new ExceptionLineAnnotationKind(allowID);
    public static final IJmlClauseKind forbidClauseKind = new ExceptionLineAnnotationKind(forbidID);
    public static final IJmlClauseKind ignoreClauseKind = new ExceptionLineAnnotationKind(ignoreID);
    
    // We use ExceptionnLineAnnotationKind for nowarn annotations in order to share the scan method,
    // even though it is handled differently and does not hold a list of exceptions
    public static final IJmlClauseKind nowarnClauseKind = new ExceptionLineAnnotationKind(nowarnID);
    
    
    public static class ExceptionLineAnnotationKind extends IJmlClauseKind.LineAnnotationKind {
        public ExceptionLineAnnotationKind(String keyword) { super(keyword); }
        
        @Override
        public void scan(int keywordPos, String keyword, IJmlClauseKind clauseKind, JmlTokenizer tokenizer) {
            Context context = tokenizer.context;
            JmlFactory M = JmlTree.Maker.instance(context);
            java.util.List<JCExpression> exprs = new java.util.LinkedList<>();
            try {
                int tokenPos = tokenizer.pos();
                Token t = tokenizer.readToken();
                if (t.kind == TokenKind.SEMI || t.ikind == JmlTokenKind.ENDJMLCOMMENT) {
                    // No labels - for nowarn this means suppress everything
                    // Indicate this with null
                    if (clauseKind == nowarnClauseKind) Nowarns.instance(context).addItem(Log.instance(context).currentSource(),keywordPos,null);
                    else Log.instance(context).warning(t.pos, "jml.message", "Ignoring annotation with no exceptions listed");
                } else {
                    while (tokenizer.jml() && t.kind != TokenKind.SEMI && t.ikind != JmlTokenKind.ENDJMLCOMMENT) {
                        if (t.kind != TokenKind.IDENTIFIER){
                            // Bad statement or missing terminating semicolon
                            tokenizer.jmlError(t.pos, tokenizer.errPos(), "jml.bad.line.annotation");
                            // expected identifier
                            tokenizer.skipThroughChar(';');
                            return;
                        }
                        Name name = t.name();
                        int p = t.pos;
                        t = tokenizer.readToken();
                        if (clauseKind == nowarnClauseKind) {
                            Nowarns.instance(context).addItem(Log.instance(context).currentSource(),tokenPos,name.toString());
                        } else {
                            JCExpression qid = M.Ident(name);
                            qid.pos = p;
                            while (t.kind == TokenKind.DOT) {
                                t = tokenizer.readToken();
                                if (t.kind != TokenKind.IDENTIFIER){
                                    // Bad statement or missing terminating semicolon
                                    tokenizer.jmlError(t.pos, tokenizer.errPos(), "jml.bad.line.annotation");
                                    // expected identifier
                                    tokenizer.skipThroughChar(';');
                                    return;
                                }
                                qid = M.Select(qid, t.name());
                                qid.pos = t.pos;
                                t = tokenizer.readToken();
                            }
                            exprs.add(qid);
                        }
                        if (t.kind == TokenKind.COMMA){
                            t = tokenizer.readToken();
                        }
                    }
                }
                if (tokenizer.jmlTokenKind == JmlTokenKind.ENDJMLCOMMENT) { 
                    Log.instance(context).warning(t.pos, "jml.line.annotation.with.no.semicolon");
                    // Here we are swallowing the end of comment - we normally 
                    // expect that token in the stream. However if there is just a 
                    // nowarn, the Java scanner will not expect a standalone ENDJMLCOMMENT
                    // FIXME - check the case of //@ some JML stuff ; nowarn xx 
                    // or with /*@  -- does this parse OK
                }
                if (clauseKind != nowarnClauseKind) {
                    ExceptionLineAnnotation a = new ExceptionLineAnnotation();
                    a.line = tokenizer.getLineMap().getLineNumber(keywordPos);
                    a.clauseKind = clauseKind;
                    a.keywordPos = keywordPos;
                    a.exceptionTypes = exprs;
                    tokenizer.lineAnnotations.add(a);
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
            for (JCTree.JCExpression e : this.exprs()){
                e.type = attr.attribType(e,env);
            }
            return null;
        }
    }

}
