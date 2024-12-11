package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.BANG;
import static com.sun.tools.javac.parser.Tokens.TokenKind.FOR;
import static org.jmlspecs.openjml.ext.JmlPrimitiveTypes.*;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.Maker;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Kinds.KindSelector;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

public class TypeExprClauseExtension extends JmlExtension {

    public static final String invariantID = "invariant";
    public static final String constraintID = "constraint";
    public static final String axiomID = "axiom";
    public static final String initiallyID = "initially";
    
    public static final IJmlClauseKind invariantClause = new TypeClause(invariantID);
    
    public static final IJmlClauseKind constraintClause = new TypeClause(constraintID);
    
    public static final IJmlClauseKind axiomClause = new TypeClause(axiomID);
    
    public static final IJmlClauseKind initiallyClause = new TypeClause(initiallyID);
    
    public static class TypeClause extends IJmlClauseKind.TypeClause {
        public TypeClause(String keyword) { super(keyword); }

        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClause parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            
            if (clauseType == constraintClause) {
                JmlTree.JmlTypeClauseConstraint tcl = parseConstraint(mods);
                tcl.source = log.currentSourceFile();
                return tcl;
            } else {
                parser.nextToken();
                Name n = parser.parseOptionalName();
                JCExpression e = parser.parseExpression();
                Maker M = parser.maker().at(pp);
                if (mods == null) { mods = M.Modifiers(0); }
                if (mods.getEndPosition(parser.endPosTable()) == -1) parser.storeEnd(mods, pp);
                JmlTypeClauseExpr tcl = parser.to(M.JmlTypeClauseExpr(mods, keyword, clauseType, e));
                wrapup(tcl, clauseType, true, true);
                return tcl;
            }
        }
        
        /** Parses a constraint clause */
        public JmlTypeClauseConstraint parseConstraint(JCModifiers mods) {
            int pos = parser.pos();
            parser.nextToken();
            Name n = parser.parseOptionalName();
            JCExpression e = parser.parseExpression();
            List<JmlMethodSig> sigs = null;
            boolean notlist = false;
            if (parser.token().kind == FOR) {
                parser.nextToken();
                if (parser.token().kind == BANG) {
                    notlist = true;
                    parser.nextToken();
                }
                if (parser.tokenIsId(everythingID)) {
                    parser.nextToken();
                    // This is the default, so we just leave sigs null
                    if (notlist) sigs = new ListBuffer<JmlMethodSig>().toList();
                    notlist = false;
                } else if (parser.tokenIsId(nothingID)) {
                    parser.nextToken();
                    if (!notlist) sigs = new ListBuffer<JmlMethodSig>().toList();
                    notlist = false;
                    // Here we just have an empty list
                } else {
                    sigs = parseMethodNameList();
                }
            }
            if (mods == null) mods = parser.jmlF.at(pos).Modifiers(0);
            if (mods.getEndPosition(parser.endPosTable()) == -1) parser.storeEnd(mods, pos);
            JmlTypeClauseConstraint tcl = parser.to(parser.jmlF.at(pos).JmlTypeClauseConstraint(
                    mods, e, sigs));
            tcl.notlist = notlist;
            wrapup(tcl, constraintClause, true, true);
            return tcl;
        }

        
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
        	JmlTypeClauseExpr clause = (JmlTypeClauseExpr)tree;
            boolean isStatic = clause.modifiers != null && attr.isStatic(clause.modifiers);
            JavaFileObject old = log.useSource(clause.source);
            attr.jmlenv = attr.jmlenv.pushCopy();
            VarSymbol previousSecretContext = attr.currentSecretContext;
            boolean prevAllowJML = attr.jmlresolve.setAllowJML(true);
            Env<AttrContext> localEnv = env; // FIXME - here and in constraint, should we make a new local environment?
            try {
                attr.jmlenv.inPureEnvironment = true;
                attr.jmlenv.currentClauseKind = clause.clauseType;
                // invariant, axiom, initially
                //if (tree.token == JmlToken.AXIOM) isStatic = true; // FIXME - but have to sort out use of variables in axioms in general
                if (isStatic) attr.addStatic(localEnv);

                if (clause.clauseType == invariantClause) {
                	attr.jmlenv.jmlVisibility = -1;
                	attr.attribAnnotationTypes(clause.modifiers.annotations,env); // Is this needed?
                    var a = utils.findModifier(clause.modifiers,Modifiers.SECRET);
                    attr.jmlenv.jmlVisibility = clause.modifiers.flags & Flags.AccessFlags;
                    if (a != null) {
                        // FIXME
//                        if (a.args.size() != 1) {
//                        	utils.error(clause.pos(),"jml.secret.invariant.one.arg");
//                        } else {
//                            Name datagroup = attr.getAnnotationStringArg(a);
//                            if (datagroup != null) {
//                                //Symbol v = rs.findField(env,env.enclClass.type,datagroup,env.enclClass.sym);
//                                Symbol v = JmlResolve.instance(attr.context).resolveIdent(a.args.get(0).pos(),env,datagroup,KindSelector.VAR);
//                                if (v instanceof VarSymbol) attr.currentSecretContext = (VarSymbol)v;
//                                else if (v instanceof PackageSymbol) {
//                                	utils.error(a.args.get(0).pos(),"jml.annotation.arg.not.a.field",v.getQualifiedName());
//                                }
//                            }
//                        }
                    }
                }
                attr.attribExpr(clause.expression, localEnv, attr.syms.booleanType);
                attr.checkTypeClauseMods(clause,clause.modifiers,clause.clauseType.keyword() + " clause",clause.clauseType);
                return null;
            } catch (Exception e) {
            	utils.note(clause, "jml.message", "Exception occurred in attributing clause: " + clause);
            	utils.note("    Env: " + env.enclClass.name + " " + (env.enclMethod==null?"<null method>": env.enclMethod.name));
            	throw e;
            } finally {
                if (isStatic) attr.removeStatic(localEnv);  // FIXME - move this to finally, but does not screw up the checks on the next line?
                attr.currentSecretContext = previousSecretContext;
                attr.jmlresolve.setAllowJML(prevAllowJML);
                attr.jmlenv = attr.jmlenv.pop();
                log.useSource(old);
            }
        }
    }
}
