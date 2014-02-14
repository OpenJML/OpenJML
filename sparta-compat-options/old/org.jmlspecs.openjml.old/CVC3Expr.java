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
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

/** This class converts OpenJDK ASTs (i.e., JCTree) into Strings appropriate
 * to send to CVC3; in the process, requests to define various variables may
 * be sent back to the invoking CVC3Prover.  It is implemented as a tree 
 * walker.
 * @author David Cok
 */
public class CVC3Expr extends JmlTreeScanner {

    /** The tool used to report errors and warnings */
//    protected Log log;
    
    /** The prover that invoked this translator; we need this because we have to
     * tell it to define variables as they are encountered. */
    /*@ non_null */protected CVC3Prover p;
    
    /** Does the translation.  
     * 
     * @param t the tree to translate
     * @return the translated string
     */
    public String toCVC3(JCTree t) 
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
    protected CVC3Expr(/*@ non_null */CVC3Prover p) {
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
            if (CVC3Prover.TYPE.equals(type)) {
                boolean n = p.rawdefine(name,type);
                if (n) return n;
                String s = "( " + "distinct$("+name+") = " + (++distinctCount) +" )";
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
            id = id.replace('$','_');
            id = id.replace('.','_');
            p.rawdefine(id,convertIdentType(that));  // rawdefine does not repeat a definition
            result.append(id);
        } catch (ProverException e) { 
            throw new RuntimeException(e);
        }
    }
    
    public String convertIdentType(JCIdent that) {
        Type t = that.type;
        String s;
        if (t.isPrimitive()) {
            s = convertExprType(t);
        } else if (t.tag == TypeTags.ARRAY) {
            defineArrayTypesIfNeeded(t);
            s =  BasicBlocker.encodeType(t);
        } else {
            s = "REF"; // FIXME
        }
        if (that.sym != null && that.sym.owner instanceof Symbol.ClassSymbol && !that.sym.isStatic() ) { // FIXME - isStatis is not correct for JML fields in interfaces
            // If at this point s is a new type, it won't get defined  FIXME
            // FIXME - the translating of types is a MESS - some here some in CVC3Prover some in BasicBlocker
            s = " REF -> " + s;
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
            } else {
                s = "REF";
            }
        } else if (t.tag == TypeTags.BOOLEAN) {
            s = "BOOLEAN";//"BITVECTOR(1)";
        } else if (t.tag == TypeTags.INT){
            s = "INT";
        } else if (t.tag == TypeTags.CHAR){
            s = "INT";
        } else {
            s = "INT";
        }
        return s;

    }
        
    @Override
    public void visitParens(JCParens that) {
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
                    s = s.replace(",","__");
                    s = s.replace(">","_$");
                    s = s.replace(".","_");
                    define(s,CVC3Prover.TYPE);
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
            case TypeTags.BOOLEAN:
                result.append(that.value.equals(1) ? "TRUE" : "FALSE");
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
                result.append(CVC3Prover.TYPEOF);
                result.append("(");
                that.args.get(0).accept(this);
                result.append(")");
                break;
            default:
                // FIXME
                System.out.println("Unknown token in YicsJCExpr.visitJmlMethodInvocation: " + that.token.internedName());
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
                that.meth.accept(this);
                result.append("(");
                boolean first = true;
                for (JCExpression e: that.args) {
                    if (!first) { result.append(","); first = true; }
                    e.accept(this);
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
                String type = " REF -> " + s;
                if (!p.checkAndDefine(newfield.toString(),type)) {
                    // Was not already defined
                    p.send(newfield + " : " + type + ";\n");
                    p.eatPrompt();
                } 
                if (!p.checkAndDefine(oldfield.toString(),type)) {
                    // Was not already defined
                    p.send(oldfield + " : REF -> " + s + ";\n");
                    p.eatPrompt();
                } 
                result.append("( " + newfield);
                result.append(" = update( ");
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
            //System.out.println("BBASSIGN TYPES " + that.type + " " + arr.type + " " + rhs.type);
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
                result.append("(NOT ");
                break;
            case JCTree.NEG:
                result.append("(- ");
                break;
            case JCTree.POS:
                // Nothing special needed
                that.arg.accept(this);
                return;
            case JCTree.COMPL:
            default:
                throw new RuntimeException(new ProverException("Unary operator not implemented for CVC3: " + that.getTag()));
        }
        that.arg.accept(this);
        result.append(")");
    }
    
    @Override
    public void visitBinary(JCBinary that) {
        result.append("(");
        that.lhs.accept(this);
        //int typetag = that.type.tag;
        switch (that.getTag()) {
            case JCTree.EQ:
                if (that.lhs.type.tag == TypeTags.BOOLEAN) {
                    result.append(" <=> ");
                } else {
                    result.append(" = ");
                }
                break;
            case JCTree.AND:
                result.append(" AND ");
                break;
            case JCTree.OR:
                result.append(" OR ");
                break;
            case JCTree.PLUS:
                result.append(" + ");
                break;
            case JCTree.MINUS:
                result.append(" - ");
                break;
            case JCTree.MUL:
                result.append(" * ");
                break;
            case JCTree.DIV:
                result.append(" / ");
                break;
            case JCTree.MOD:  // FIXME - need mod
                result.append(" / ");
                break;
            case JCTree.NE:
                result.append(" /= ");
                break;
            case JCTree.LE:
                result.append(" <= ");
                break;
            case JCTree.LT:
                result.append(" < ");
                break;
            case JCTree.GE:
                result.append(" >= ");
                break;
            case JCTree.GT:
                result.append(" > ");
                break;
            case JCTree.BITAND:
            case JCTree.BITXOR:
            case JCTree.BITOR:
            case JCTree.SL:
            case JCTree.SR:
            case JCTree.USR:
            default:  // FIXME - others: shift, mod, bit operations
                throw new RuntimeException(new ProverException("Binary operator not implemented for CVC3: " + that.getTag()));
        }
        that.rhs.accept(this);
        result.append(")");
    }

    @Override
    public void visitJmlBinary(JmlBinary that) {
        // encoded as: (op lhs rhs)
        if (that.op == JmlToken.SUBTYPE_OF) {
            result.append(CVC3Prover.SUBTYPE);  // FIXME
            result.append("(");
            that.lhs.accept(this);
            result.append(",");
            that.rhs.accept(this);
            result.append(")");
            return;
        }
        
        if (that.op == JmlToken.JSUBTYPE_OF) {
            System.out.println("NOT IMPLEMENTED");
//            result.append(CVC3Prover.JSUBTYPE);  // FIXME
//            result.append("(");
//            that.lhs.accept(this);
//            result.append(",");
//            that.rhs.accept(this);
//            result.append(")");
            return;
        }
        
        result.append("(");
        that.lhs.accept(this);
        if (that.op == JmlToken.IMPLIES) {
            result.append(" => ");
        } else if (that.op == JmlToken.EQUIVALENCE) {
            result.append(" <=> ");
        } else if (that.op == JmlToken.INEQUIVALENCE) {
            result.append(" XOR ");
        } else if (that.op == JmlToken.REVERSE_IMPLIES) {
            result.append(" | ");
            result.append("(! ");
            that.rhs.accept(this);
            result.append("))");
            return;
        } else {
           throw new RuntimeException(new ProverException("Binary operator not implemented for CVC3: " + that.getTag()));
        }
        result.append(" ");
        that.rhs.accept(this);
        result.append(")");
    }
    
    @Override
    public void visitConditional(JCConditional that) {
        result.append("(IF ");
        that.cond.accept(this);
        result.append(" THEN ");
        that.truepart.accept(this);
        result.append(" ELSE ");
        that.falsepart.accept(this);
        result.append("ENDIF)");
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
            p.rawdefinetype(ty,"(subtype (a::ARRAYorNULL) (or (= a NULL) (subtype$ (typeof$ a) T$java.lang.Object$$A)))",CVC3Prover.ARRAY);
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
            p.rawdefine(nm," REF -> " + s);
        } catch (ProverException e) {
            throw new RuntimeException(e);
        }

        result.append(fieldId);
        result.append("(");
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
        result.append(CVC3Prover.CAST);
        result.append(" ");
        that.expr.accept(this);
        result.append(" ");
        that.clazz.accept(this);
        result.append(")");
    }
    
    @Override
    public void visitTree(JCTree tree) {
        Exception e = new ProverException("Did not expect to call a visit method in CVC3Expr: " + tree.getClass());
        throw new RuntimeException(e);
    }
    
}
