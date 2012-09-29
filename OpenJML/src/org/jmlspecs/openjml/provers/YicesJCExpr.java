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
import org.jmlspecs.openjml.proverinterface.ProverException;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.Type.TypeVar;
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
public class YicesJCExpr extends JmlTreeScanner {

    /** The tool used to report errors and warnings */
//    protected Log log;
    
    /** The prover that invoked this translator; we need this because we have to
     * tell it to define variables as they are encountered. */
    /*@ non_null */protected YicesProver p;
    
    /** Does the translation.  
     * 
     * @param t the tree to translate
     * @return the translated string
     */
    public String toYices(JCTree t) 
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
    protected YicesJCExpr(/*@ non_null */YicesProver p) {
        this.p = p;
    }

    /** The builder in which to create the resulting string */
    /*@ non_null */
    private StringBuilder result = new StringBuilder();

    protected void send(String s) {
        try {
            p.send(s);
            p.eatPrompt();
        } catch (ProverException e) {
            throw new RuntimeException(e);
        }
    }

    int distinctCount = 100;
    protected boolean define(String name, String type) {
        try {
            if (YicesProver.JAVATYPE.equals(type)) {
                boolean n = p.rawdefine(name,type);
                if (n) return n;
                String s = "(= ("+"distinct$"+" "+name+") " + (++distinctCount) +")";
                p.rawassume(s);
                return false;
            } else {
                return p.rawdefine(name,type);
            }
        } catch (ProverException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void visitIdent(JCIdent that) {
        // Make sure the id is defined.
        // Emit it simply as its string
        try { 
            String id = that.toString();
            p.rawdefine(id,convertIdentType(that));  // rawdefine does not repeat a definition
        } catch (ProverException e) { 
            throw new RuntimeException(e);
        }
        result.append(that.toString());
    }
    
    public String convertIdentType(JCIdent that) {
        Type t = that.type;
        String s;
        if (t.isPrimitive()) {
            s = convertExprType(t);
        } else if (t.tag == TypeTags.ARRAY) {
            defineArrayTypesIfNeeded(t);
            s =  BasicBlocker.encodeType(t);
        } else if (t.toString().endsWith("IJMLTYPE")) {
            s = YicesProver.JMLTYPE;
        } else {
            s = "REF"; // FIXME
        }
        if (that.sym != null && that.sym.type instanceof TypeVar) return s; // Even though a TypeVar is not static, we don't make it a function of the object 
        if (that.sym != null && that.sym.owner instanceof Symbol.ClassSymbol && !that.sym.isStatic() ) { // FIXME - isStatis is not correct for JML fields in interfaces
            // If at this point s is a new type, it won't get defined  FIXME
            // FIXME - the translating of types is a MESS - some here some in YicesProver some in BasicBlocker
            s = "(-> REF " + s + ")";
        }
        return s;
    }
    
    public static String convertExprType(Type t) {
        String s;
        if (!t.isPrimitive()) {
            if (t instanceof ArrayType) {
                t = ((ArrayType)t).getComponentType();
//                s = convertType(t);
//                s = "(-> int " + s + ")";
                s = "refA$" + convertExprType(t);
            } else if (t.tsym.flatName().toString().endsWith("IJMLTYPE")) {
                s = YicesProver.JMLTYPE;
            } else {
                s = "REF";
            }
        } else if (t.tag == TypeTags.BOOLEAN) {
            s = "bool";
        } else if (t.tag == TypeTags.INT){
            s = "int";
        } else if (t.tag == TypeTags.CHAR){
            s = "int";
        } else {
            s = "int";
        }
        return s;

    }
        
    @Override
    public void visitParens(JCParens that) {
        // Ignore parenthesized expression - all the output for Yices
        // is parenthesized in prefix form anyway
        that.expr.accept(this);
    }
    
    @Override
    public void visitLiteral(JCLiteral that) {
        // Should only get these: boolean, int, class, null, ...
        // FIXME - characters, strings? others?
        switch (that.typetag) {
            case TypeTags.CLASS:
                if (that.value instanceof Type) {
                    String s = "T$" + ((Type)that.value).toString();
                    s = s.replace("[]","$$A");
                    s = s.replace("<","$_");
                    s = s.replace(",","..");
                    s = s.replace(">","_$");
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
                // toString uses pretty printing which knows to convert the
                // value (which is an Integer) into a quoted char
                // We want to use it simply as an int
                result.append(that.value.toString());
                break;
            default:
                result.append(that.toString());
        }
    }

    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // Should have only one argument (an \old or \pre can get here)
        //log.noticeWriter.println("visit Apply: " + that.meth.getClass() + " " + that.meth);
        if (that.token == null) {
            visitApply(that);
        } else {
            switch (that.token) {
                case BSTYPEOF:
                    result.append("(");
                    result.append(YicesProver.TYPEOF);
                    result.append(" ");
                    that.args.get(0).accept(this);
                    result.append(")");
                    break;
                default:
                    // FIXME
                    System.out.println("Unknown token in YicsJCExpr.visitJmlMethodInvocation: " + that.token.internedName());
                break;
            }
        }
    }
    
    @Override
    public void visitApply(JCMethodInvocation that) {
        // FIXME - document
        if (that.meth != null) {
            // FIXME - review this
            //log.noticeWriter.println("visit Apply: " + that.meth.getClass() + " " + that.meth);
            if (!(that.meth instanceof JCIdent)) 
                that.args.get(0).accept(this);
            else {
                // check for definition
                String nm = that.meth.toString();
                if (!p.isDefined(nm)) {
                    // Was not already defined
                    String s = "(define " + nm + "::(->";
                    for (JCExpression e: that.args) {
                        s = s + " " + p.defineType(e.type);
                    }
                    String t = p.defineType(that.type);
                    p.checkAndDefine(nm,t);
                    s = s + " " + t + "))\n";
                    try {
                        p.send(s);
                        p.eatPrompt();
                    } catch (ProverException e) {
                        throw new RuntimeException(e);
                    }
                } 
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
            //log.noticeWriter.println("BBASSIGN TYPES " + that.type + " " + arr.type + " " + rhs.type);
            Type t = ((ArrayType)arr.type).elemtype;
            defineArrayTypesIfNeeded(t,oldarrs.toString(),newarrs.toString());
            
            {
                // (= newarrs (update oldarrs (arr) (update (oldarrs arr) (index) value)))
                result.append("(= " + newarrs);
                result.append(" (update ");
                result.append(oldarrs);
                result.append(" (");
                arr.accept(this);
                result.append(") (update (");
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
            try {
                String type = "(-> REF " + s + ")";
                if (!p.checkAndDefine(newfield.toString(),type)) {
                    // Was not already defined
                    p.send("(define " + newfield + "::" + type + ")\n");
                    p.eatPrompt();
                } 
                if (!p.checkAndDefine(oldfield.toString(),type)) {
                    // Was not already defined
                    p.send("(define " + oldfield + "::(-> REF " + s + "))\n");
                    p.eatPrompt();
                } 
                result.append("(= " + newfield);
                result.append(" (update ");
                result.append(oldfield);
                result.append(" (");
                selected.accept(this);
                result.append(") ");
                rhs.accept(this);
                result.append("))");
            } catch (ProverException e) {
                throw new RuntimeException(e);
            }
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
            //log.noticeWriter.println("BBASSIGN TYPES " + that.type + " " + arr.type + " " + rhs.type);
            Type t = ((ArrayType)arr.type).elemtype;
            defineArrayTypesIfNeeded(t,oldarrs.toString(),newarrs.toString());
            
            {
                // (and (forall (b::<a type>) (=> (/= b a) (= (newarrs b) (oldarrs b)) ))
                //      (/= (newarrs a) (oldarrs a))
                //      (forall (i::int) (=> (not <precondition && i in range>) (= ((newarrs a) i) ((oldarrs a) i)))))
                result.append("(and (forall (b::");
                result.append(p.defineType(arr.type));
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
                
                result.append("(forall (i::int) (=> (not (and ");
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
                result.append("(- 0 ");
                break;
            case JCTree.POS:
                // Nothing special needed
                that.arg.accept(this);
                return;
            case JCTree.COMPL:
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
            case JCTree.BITAND: // FIXME - need different op for integer operands
                result.append("and ");
                break;
            case JCTree.OR:
            case JCTree.BITOR: // FIXME - need different op for integer operands
                result.append("or ");
                break;
            case JCTree.PLUS:
                result.append("+ ");
                break;
            case JCTree.MINUS:
                result.append("- ");
                break;
            case JCTree.MUL:
                if (typetag == TypeTags.INT || typetag == TypeTags.SHORT || typetag == TypeTags.LONG || typetag == TypeTags.BYTE)
                    result.append("imul ");
                else // float, double
                    result.append("rmul ");
                if (that.lhs instanceof JCLiteral) {
                    String s = that.lhs.toString();
                    String ss = "(assert (forall (x::int) (= (imul " + s + " x) (* " + s + " x))))\n";
                    send(ss);
                } else if (that.rhs instanceof JCLiteral) {
                    String s = that.rhs.toString();
                    String ss = "(assert (forall (x::int) (= (imul x " + s + ") (* x " + s + "))))\n";
                    send(ss);
                }
                break;
                //result.append("* ");
                //break;
            case JCTree.DIV:
                if (typetag == TypeTags.INT || typetag == TypeTags.SHORT || typetag == TypeTags.LONG || typetag == TypeTags.BYTE)
                    result.append("idiv ");
                else // float, double
                    result.append("rdiv ");
                if (that.rhs instanceof JCLiteral) {
                    String s = that.rhs.toString();
                    String ss = "(assert (forall (x::int) (= (idiv x " + s + ") (div x " + s + "))))\n";
                    send(ss);
                }
                break;
            case JCTree.MOD:
                if (typetag == TypeTags.INT || typetag == TypeTags.SHORT || typetag == TypeTags.LONG || typetag == TypeTags.BYTE)
                    result.append("imod ");
                else // float, double
                    result.append("rmod ");
                if (that.rhs instanceof JCLiteral) {
                    String s = that.rhs.toString();
                    String ss = "(assert (forall (x::int) (= (imod x " + s + ") (mod x " + s + "))))\n";
                    send(ss);
                }
                break;
                //result.append("mod ");
                //break;
            case JCTree.NE:
                result.append("/= ");
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
            case JCTree.BITXOR:
            case JCTree.SL:
            case JCTree.SR:
            case JCTree.USR:
            default:  // FIXME - others: shift, mod, bit operations
                throw new RuntimeException(new ProverException("Binary operator not implemented for Yices: " + that.getTag()));
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
            result.append("/= ");
        } else if (that.op == JmlToken.REVERSE_IMPLIES) {
            result.append("=> ");
            that.rhs.accept(this);
            result.append(" ");
            that.lhs.accept(this);
            result.append(")");
            return;
        } else if (that.op == JmlToken.SUBTYPE_OF) {
            result.append(YicesProver.JMLSUBTYPE);
            result.append(" ");
        } else if (that.op == JmlToken.JSUBTYPE_OF) {
            result.append(YicesProver.JAVASUBTYPE);
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

        defineArrayTypesIfNeeded(that.type,arr);
        
        result.append("((");
        result.append(arr);
        result.append(" ");
        that.indexed.accept(this);
        result.append(") ");
        that.index.accept(this);
        result.append(")");
    }
    
    protected void defineArrayTypesIfNeeded(Type componenttype, String... ids) {
        if (componenttype instanceof ArrayType)
            defineArrayTypesIfNeeded( ((ArrayType)componenttype).elemtype );
        try {
            String comptype = BasicBlocker.encodeType(componenttype);
//            String tyy = "array$" + comptype;
//            if (!p.checkAndDefine(tyy)) {
//                // Was not already defined
//                p.send("(define-type " + tyy + " (-> int "+comptype+"))\n");
//                p.eatPrompt();
//            }
            String ty = "refA$" + comptype;
            // FIXME _ mixed types?
            p.rawdefinetype(ty,"(subtype (a::ARRAYorNULL) (or (= a NULL) (" + YicesProver.JAVASUBTYPE + " (typeof$ a) T$java.lang.Object$$A)))",YicesProver.ARRAY);
            for (String arr: ids) {
                if (!p.isDefined(arr)) {
                    String arrty = "(-> " + ty + " (-> int "+comptype+"))";
                    // Was not already defined
                    p.rawdefine(arr,arrty);
                }
            }
        } catch (ProverException e) {
            throw new RuntimeException(e);
        }

    }
    
    @Override
    public void visitSelect(JCFieldAccess that) {
        if (!(that instanceof JmlBBFieldAccess)) {
            throw new RuntimeException(new ProverException("A BasicBlock AST should have JmlBBFieldAccess nodes for field access: " + that.getClass()));
        }
        // FIXME - document
        JCIdent fieldId = ((JmlBBFieldAccess)that).fieldId;
        Type t = that.type;
        try {
            String s = p.defineType(t);
            String nm = fieldId.toString();
            p.rawdefine(nm,"(-> REF " + s + ")");
        } catch (ProverException e) {
            throw new RuntimeException(e);
        }

        result.append("(");
        result.append(fieldId);
        result.append(" ");
        that.selected.accept(this);
        result.append(")");
    }
    
    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        // Presuming all expression to this point are FORALL - FIXME
        // translates to (forall (name::type ... name::type) expr)
        result.append("(forall (");
        
        List<String> oldTypes = new LinkedList<String>();
        do {

            for (JCVariableDecl decl: that.decls) {
                String ytype = p.defineType(decl.type);

                String id = decl.name.toString();
                result.append(id);
                result.append("::");
                result.append(ytype);
                result.append(" ");
                
                String oldType = p.getTypeString(id);
                oldTypes.add(oldType);
                p.declare(id,ytype);
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
        
        for (JCVariableDecl decl: that.decls) {
            String id = decl.name.toString();
            String ot = oldTypes.remove(0);
            if (ot == null) {
                p.removeDeclaration(id);
            } else {
                p.declare(id,ot);
            }
        }
    }
    
    @Override
    public void visitTypeCast(JCTypeCast that) {
        result.append("(");
        result.append(YicesProver.CAST);
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
