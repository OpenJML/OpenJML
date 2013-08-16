package org.jmlspecs.openjml.provers;

import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayHavoc;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.esc.BasicBlocker;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.ProverException;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

/** This class converts OpenJDK ASTs (i.e., JCTree) into Strings appropriate
 * to send to Yices; in the process, requests to define various variables may
 * be sent back to the invoking YicesProver.  It is implemented as a tree 
 * walker.
 * @author David Cok
 */
public class SMTTranslator extends JmlTreeScanner {

    /** The tool used to report errors and warnings */
//    protected Log log;
    
    /** The prover that invoked this translator; we need this because we have to
     * tell it to define variables as they are encountered. */
    /*@ non_null */protected AbstractProver p;
    
    /** Does the translation.  
     * 
     * @param t the tree to translate
     * @return the translated string
     */
    public String translate(JCTree t) 
            throws ProverException {
        try {
            result.setLength(0);
            t.accept(this);
            return result.toString(); // FIXME - no type given?
        } catch (RuntimeException e) {
            if (e.getCause() instanceof ProverException) {
                throw (ProverException)e.getCause();
            } else {
                // Some unknown exception thrown - so convert it to a 
                // ProverException and copy the stack trace
                ProverException ee = new ProverException(e.toString());
                ee.setStackTrace(e.getStackTrace());
                throw ee;
            }
        }
    }
    
    /** The constructor of a new translator, connected to the given prover.
     * 
     * @param p the prover to connect with
     */
    protected SMTTranslator(/*@ non_null */AbstractProver p) {
        this.p = p;
    }

    /** The builder in which to create the resulting string */
    /*@ non_null */
    private StringBuilder result = new StringBuilder();

    int distinctCount = 100; // FIXME - ???
    protected boolean define(String name, String type) {
        try {
            if (YicesProver.JAVATYPE.equals(type)) { // FIXME _ ???
                boolean n = ((SMTProver)p).rawdefine(name,type);
                if (n) return n;
                String s = "(EQ ("+"distinct$"+" "+name+") " + (++distinctCount) +")";
                p.rawassume(s);
                return false;
            } else {
                return ((SMTProver)p).rawdefine(name,type);
            }
        } catch (ProverException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void visitIdent(JCIdent that) {
        // Make sure the id is defined.
        // Emit it simply as its string
        String s = that.toString();
        result.append(s);
    }
    
    public String convertIdentType(JCIdent that) {
        Type t = that.type;
        String s;
        if (t.isPrimitive()) {
            s = convertExprType(t);
        } else if (t.tag == TypeTags.ARRAY) {
            //defineArrayTypesIfNeeded(t);
            s =  BasicBlocker.encodeType(t);
        } else {
            s = "Object"; // FIXME
        }
        if (that.sym != null && that.sym.owner instanceof Symbol.ClassSymbol && !that.sym.isStatic() ) { // FIXME - isStatis is not correct for JML fields in interfaces
            // If at this point s is a new type, it won't get defined  FIXME
            // FIXME - the translating of types is a MESS - some here some in YicesProver some in BasicBlocker
            s = "(-> REF " + s + ")"; // FIXME - ???
        }
        return s;
    }
    
    public static String convertExprType(Type t) {
        String s;
        if (!t.isPrimitive()) {
            if (t instanceof ArrayType) {
                t = ((ArrayType)t).getComponentType();
                s = "(Array Int " + convertExprType(t) + ")";
            } else {
                s = "Object";
            }
        } else if (t.tag == TypeTags.BOOLEAN) {
            s = "Bool";
        } else if (t.tag == TypeTags.INT){
            s = "Int";
        } else if (t.tag == TypeTags.CHAR){
            s = "Int";
        } else {
            s = "Int";
        }
        return s;

    }
        
    @Override
    public void visitParens(JCParens that) {
        // Ignore parenthesized expression - all the output for SMT
        // is parenthesized in prefix form anyway
        that.expr.accept(this);
    }
    
    @Override
    public void visitLiteral(JCLiteral that) {
        // Should only get these: boolean, int, class, null, ...
        // FIXME - characters, strings? others?
        switch (that.typetag) {
            case TypeTags.CLASS:
                // FIXME - ???
                if (that.value instanceof Type) {
                    String s = "T$" + ((Type)that.value).toString();
                    s = s.replace("[]","$$A");
                    s = s.replace("<","$_");
                    s = s.replace(",","..");
                    s = s.replace(">","_$");
                    s = "|" + s + "|";
                    define(s,YicesProver.JAVATYPE);
                    result.append(s);
                } else {
                    result.append(that.toString());
                }
                break;
            case TypeTags.BOT:
                result.append("NULL");
                break;
            case TypeTags.CHAR:
                // that.toString uses pretty printing which knows to convert the
                // value (which is an Integer) into a quoted char
                // We want to use it simply as an int
                result.append(that.value.toString());
                break;
            case TypeTags.BOOLEAN:
                result.append(that.getValue().equals(Boolean.TRUE) ? "true" : "false");
                break;
                
            default:
                result.append(that.toString());
        }
    }

    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // Should have only one argument (an \old or \pre can get here)
        //System.out.println("visit Apply: " + that.meth.getClass() + " " + that.meth);
        switch (that.token) {
            case BSTYPEOF:
                result.append("(");
                result.append(SMTProver.TYPEOF);
                result.append(" ");
                that.args.get(0).accept(this);
                result.append(")");
                break;
            default:
                // FIXME
                System.out.println("Unknown token in SMTTranslator.visitJmlMethodInvocation: " + that.token.internedName());
                break;
        }
    }
    
    @Override
    public void visitApply(JCMethodInvocation that) {
        // FIXME - document
        if (that.meth != null) {
            // FIXME - review this
            //System.out.println("visit Apply: " + that.meth.getClass() + " " + that.meth);
            if (!(that.meth instanceof JCIdent)) 
                that.args.get(0).accept(this);
            else {
                // check for definition
                String nm = that.meth.toString();
//                if (!p.isDefined(nm)) {
//                    // Was not already defined
//                    String s = "(define " + nm + "::(->";
//                    for (JCExpression e: that.args) {
//                        s = s + " " + p.defineType(e.type);
//                    }
//                    String t = p.defineType(that.type);
//                    p.checkAndDefine(nm,t);
//                    s = s + " " + t + "))\n";
//                    try {
//                        p.send(s);
//                        p.eatPrompt();
//                    } catch (ProverException e) {
//                        throw new RuntimeException(e);
//                    }
//                } 
                // regular method application
                result.append("(");
                that.meth.accept(this);
                result.append(" ");
                for (JCExpression e: that.args) {
                    e.accept(this);
                    result.append(" ");
                }
                result.append(")");
                
            }
        } else if (that instanceof JmlBBArrayAssignment) {
            JCIdent newarrs = (JCIdent)that.args.get(0);
            JCIdent oldarrs = (JCIdent)that.args.get(1);
            JCExpression arr = that.args.get(2);
            JCExpression index = that.args.get(3);
            JCExpression rhs = that.args.get(4);
            
            // One might think that rhs.type could be used as the element type,
            // but no, there might be some conversions that happen.  In particular,
            // rhs may be a null literal.
            // Of course - what if arr is a null literal ?  FIXME
            //System.out.println("BBASSIGN TYPES " + that.type + " " + arr.type + " " + rhs.type);
            Type t = ((ArrayType)arr.type).elemtype;
            //defineArrayTypesIfNeeded(t,oldarrs.toString(),newarrs.toString());
            
            {
                // (= newarrs (update oldarrs (arr) (update (oldarrs arr) (index) value)))
                result.append("(= " + newarrs);
                result.append(" (update ");
                result.append(oldarrs);
                result.append(" (");
                arr.accept(this);
                result.append(") (store (");
                result.append(oldarrs);
                result.append(" ");
                arr.accept(this);
                result.append(") (");
                index.accept(this);
                result.append(") ");
                rhs.accept(this);
                result.append(")))");
            }
        } else if (that instanceof JmlBBFieldAssignment) {
            JCIdent newfield = (JCIdent)that.args.get(0);
            JCIdent oldfield = (JCIdent)that.args.get(1);
            JCExpression selected = that.args.get(2);
            JCExpression rhs = that.args.get(3);
            Type t = rhs.type;
            String s = BasicBlocker.encodeType(t);
//            try {
                String type = "(-> REF " + s + ")";
//                if (!p.checkAndDefine(newfield.toString(),type)) {
//                    // Was not already defined
//                    p.send("(define " + newfield + "::" + type + ")\n");
//                    p.eatPrompt();
//                } 
//                if (!p.(oldfield.toString(),type)) {
//                    // Was not already defined
//                    p.sendcheckAndDefine("(define " + oldfield + "::(-> REF " + s + "))\n");
//                    p.eatPrompt();
//                } 
                result.append("(= " + newfield);
                result.append(" (store ");
                result.append(oldfield);
                result.append(" (");
                selected.accept(this);
                result.append(") ");
                rhs.accept(this);
                result.append("))");
//            } catch (ProverException e) {
//                throw new RuntimeException(e);
//            }
        } else if (that instanceof JmlBBArrayHavoc) {
            JCIdent newarrs = (JCIdent)that.args.get(0);
            JCIdent oldarrs = (JCIdent)that.args.get(1);
            JCExpression arr = that.args.get(2);
            JCExpression indexlo = that.args.get(3);
            JCExpression indexhi = that.args.get(4);
            JCExpression precondition = that.args.get(5);
            boolean above = ((JmlBBArrayHavoc)that).above;
            
            // One might think that rhs.type could be used as the element type,
            // but no, there might be some conversions that happen.  In particular,
            // rhs may be a null literal.
            // Of course - what if arr is a null literal ?  FIXME
            //System.out.println("BBASSIGN TYPES " + that.type + " " + arr.type + " " + rhs.type);
            Type t = ((ArrayType)arr.type).elemtype;
            //defineArrayTypesIfNeeded(t,oldarrs.toString(),newarrs.toString());
            
            {
                // (and (forall (b::<a type>) (=> (/= b a) (= (newarrs b) (oldarrs b)) ))
                //      (/= (newarrs a) (oldarrs a))
                //      (forall (i::int) (=> (not <precondition && i in range>) (= ((newarrs a) i) ((oldarrs a) i)))))
                result.append("(and (forall (b::");
                //result.append(p.defineType(arr.type));
                result.append(") (=> (/= b ");
                arr.accept(this);
                result.append(") (= (");
                result.append(newarrs);
                result.append(" b) (");
                result.append(oldarrs);
                result.append(" b))))");
                
                result.append("(/= (");
                result.append(newarrs);
                result.append(" ");
                arr.accept(this);
                result.append(") (");
                result.append(oldarrs);
                result.append(" ");
                arr.accept(this);
                result.append("))");
                
                result.append("(forall (i Int) (=> (not (and ");
                precondition.accept(this);
                result.append(" (<= ");
                indexlo.accept(this);
                result.append(" i) (");
                result.append(above ? "<" : "<=");
                result.append(" i ");
                indexhi.accept(this);
                result.append("))) (= ((");
                result.append(newarrs);
                result.append(" ");
                arr.accept(this);
                result.append(") i) ((");
                result.append(oldarrs);
                result.append(" ");
                arr.accept(this);
                result.append(") i)))))");
            }
        } else {
            // FIXME
            System.out.println("UNEXPECTED");
        }
    }
    
    @Override
    public void visitUnary(JCUnary that) {
        // boolean not (!) encoded as: (not arg)
        // arithmetic negation (-) as: (- 0 arg)   [there is no unary negation]
        switch (that.getTag()) {
            case JCTree.NOT:
                result.append("(not ");
                break;
            case JCTree.NEG:
                result.append("(- ");
                break;
            case JCTree.POS:
                // Nothing special needed
                that.arg.accept(this);
                return;
            case JCTree.COMPL: // FIXME
            default:
                throw new RuntimeException(new ProverException("Unary operator not implemented for Yices: " + that.getTag()));
        }
        that.arg.accept(this);
        result.append(")");
    }
    
    @Override
    public void visitBinary(JCBinary that) {
        // encoded as: (op lhs rhs)
        result.append("(");
        int typetag = that.type.tag;
        switch (that.getTag()) {
            case JCTree.EQ:
                result.append("= ");
                break;
            case JCTree.AND:
                result.append("and ");
                break;
            case JCTree.OR:
                result.append("or ");
                break;
            case JCTree.PLUS:
                result.append("+ ");
                break;
            case JCTree.MINUS:
                result.append("- ");
                break;
            case JCTree.MUL:
                result.append("* ");
                break;
            case JCTree.DIV:
                result.append("/ ");
                break;
            case JCTree.MOD:
                result.append("mod ");
                break;
            case JCTree.NE:
                result.append("distinct ");
                break;
            case JCTree.LE:
                result.append("<= ");
                break;
            case JCTree.LT:
                result.append("< ");
                break;
            case JCTree.GE:
                result.append(">= ");
                break;
            case JCTree.GT:
                result.append("> ");
                break;
            case JCTree.BITAND:
            case JCTree.BITXOR:
            case JCTree.BITOR:
            case JCTree.SL:
            case JCTree.SR:
            case JCTree.USR:
            default:  // FIXME - others: shift, mod, bit operations
                throw new RuntimeException(new ProverException("Binary operator not implemented for SMT: " + that.getTag()));
        }
        that.lhs.accept(this);
        result.append(" ");
        that.rhs.accept(this);
        result.append(")");
    }

    @Override
    public void visitJmlBinary(JmlBinary that) {
        // encoded as: (op lhs rhs)
        result.append("(");
        if (that.op == JmlToken.IMPLIES) {
            result.append("=> ");
        } else if (that.op == JmlToken.EQUIVALENCE) {
            result.append("= ");
        } else if (that.op == JmlToken.INEQUIVALENCE) {
            result.append("distinct ");
        } else if (that.op == JmlToken.REVERSE_IMPLIES) {
            result.append("=> ");
            that.rhs.accept(this);
            result.append(" ");
            that.lhs.accept(this);
            result.append(")");
            return;
        } else if (that.op == JmlToken.SUBTYPE_OF) {
            result.append(SMTProver.JMLSUBTYPE);
            result.append(" ");
        } else if (that.op == JmlToken.JSUBTYPE_OF) {
            result.append(SMTProver.JAVASUBTYPE);
            result.append(" ");
        } else {
           throw new RuntimeException(new ProverException("Binary operator not implemented for Yices: " + that.getTag()));
        }
        that.lhs.accept(this);
        result.append(" ");
        that.rhs.accept(this);
        result.append(")");
    }
    
    @Override
    public void visitConditional(JCConditional that) {
        // encoded as:  (ite cond lhs rhs)
        result.append("(ite ");
        that.cond.accept(this);
        result.append(" ");
        that.truepart.accept(this);
        result.append(" ");
        that.falsepart.accept(this);
        result.append(")");
    }
    
    @Override
    public void visitIndexed(JCArrayAccess that) {
        if (!(that instanceof JmlBBArrayAccess)) {
            throw new RuntimeException(new ProverException("A BasicBlock AST should have JMLBBArrayAccess nodes for array access: " + that.getClass()));
        }
        // FIXME - document
        JCIdent arraysId = ((JmlBBArrayAccess)that).arraysId;
        String arr = arraysId.toString();

        //defineArrayTypesIfNeeded(that.type,arr);
        
        result.append("((");
        result.append(arr);
        result.append(" ");
        that.indexed.accept(this);
        result.append(") ");
        that.index.accept(this);
        result.append(")");
    }
    

    
    @Override
    public void visitSelect(JCFieldAccess that) {
        if (!(that instanceof JmlBBFieldAccess)) {
            throw new RuntimeException(new ProverException("A BasicBlock AST should have JmlBBFieldAccess nodes for field access: " + that.getClass()));
        }
        // FIXME - document
        JCIdent fieldId = ((JmlBBFieldAccess)that).fieldId;
        Type t = that.type;
//        try {
//            String s = p.defineType(t);
//            String nm = fieldId.toString();
//            p.rawdefine(nm,"(-> REF " + s + ")");
//        } catch (ProverException e) {
//            throw new RuntimeException(e);
//        }

        result.append("(");
        String s = fieldId.toString();
        result.append(s);
        result.append(" ");
        that.selected.accept(this);
        result.append(")");
    }
    
    @Override// FIXME - the following is not correct
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        // Presuming all expression to this point are FORALL - FIXME
        // translates to (forall (name::type ... name::type) expr)
        result.append("(forall (");
        
        List<String> oldTypes = new LinkedList<String>();
        do {

            for (JCVariableDecl decl: that.decls) {
                result.append("(");
                String id = decl.name.toString();
                result.append(id);
                result.append(" ");
                result.append(convertExprType(decl.type));
                result.append(")");
            }

            if (that.value instanceof JmlQuantifiedExpr) {
                that = (JmlQuantifiedExpr)that.value;
            } else break;
        } while (true);
        
        result.append(") ");
        if (that.range == null) {
            that.value.accept(this);
        } else {
            result.append("(=> ");
            that.range.accept(this);
            result.append(" ");
            that.value.accept(this);
            result.append(")");
        }
        result.append(")");
        
//        for (JCVariableDecl decl: that.decls) {
//            String id = decl.name.toString();
//            String ot = oldTypes.remove(0);
//            if (ot == null) {
//                p.removeDeclaration(id);
//            } else {
//                p.declare(id,ot);
//            }
//        }
    }
    
    @Override
    public void visitTypeCast(JCTypeCast that) {
        result.append("(");
        result.append(SMTProver.CAST);
        result.append(" ");
        that.expr.accept(this);
        result.append(" ");
        that.clazz.accept(this);
        result.append(")");
    }
    
    @Override
    public void visitTree(JCTree tree) {
        Exception e = new ProverException("Did not expect to call a visit method in YicesJCExpr: " + tree.getClass());
        throw new RuntimeException(e);
    }
    
}
