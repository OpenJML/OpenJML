package org.jmlspecs.openjml.provers;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.BasicBlocker;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.proverinterface.ProverException;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class YicesJCExpr extends JmlTreeScanner {

    Log log;
    YicesProver p;
    
    static public YicesTerm toYices(Context context, JCTree t, YicesProver p) {
        YicesJCExpr tr = new YicesJCExpr(context,p);
        t.accept(tr);
        return new YicesTerm(null,tr.result.toString()); // FIXME - no type given?
    }
    
    protected YicesJCExpr(Context context,YicesProver p) {
        this.p = p;
        this.log = Log.instance(context);
    }

    private StringBuilder result = new StringBuilder();

    public void visitIdent(JCIdent that) {
        try {
            p.define(that.toString(),that.type);
        } catch (ProverException e) {
            System.out.println(e);
            // FIXME - what to do?
        }
        result.append(that.toString());
    }
        
    public void visitParens(JCParens that) {
        that.expr.accept(this);
    }
    
    public void visitLiteral(JCLiteral that) {
        result.append(that.toString());
    }
    
    public void visitApply(JCMethodInvocation that) {
        if (that.meth != null) {
            // Should have only one argument (an \old or \pre can get here)
            that.args.get(0).accept(this);
        } else if (that instanceof JmlBBArrayAssignment) {
            JCIdent newarrs = (JCIdent)that.args.get(0);
            JCIdent oldarrs = (JCIdent)that.args.get(1);
            JCExpression arr = that.args.get(2);
            JCExpression index = that.args.get(3);
            JCExpression rhs = that.args.get(4);
            Type t = rhs.type;
            String s = BasicBlocker.encodeType(t);
            String ty = "array$" + s;
            try {
                if (!p.checkAndDefine(ty)) {
                    p.send("(define-type " + ty + ")\n");
                    p.eatPrompt();
                }
                if (!p.checkAndDefine(newarrs.toString())) {
                    // Was not already defined
                    p.send("(define " + newarrs + "::(-> " + ty + "  int " + s + "))\n");
                    p.eatPrompt();
                } 
                if (!p.checkAndDefine(oldarrs.toString())) {
                    // Was not already defined
                    p.send("(define " + oldarrs + "::(-> " + ty + "  int " + s + "))\n");
                    p.eatPrompt();
                } 
                result.append("(= " + newarrs);
                result.append(" (update ");
                result.append(oldarrs);
                result.append(" (");
                arr.accept(this);
                result.append(" ");
                index.accept(this);
                result.append(") ");
                rhs.accept(this);
                result.append("))");
            } catch (ProverException e) {
                // FIXME - what to do?
            }
        } else if (that instanceof JmlBBFieldAssignment) {
            JCIdent newfield = (JCIdent)that.args.get(0);
            JCIdent oldfield = (JCIdent)that.args.get(1);
            JCExpression selected = that.args.get(2);
            JCExpression rhs = that.args.get(3);
            Type t = rhs.type;
            String s = BasicBlocker.encodeType(t);
            try {
                if (!p.checkAndDefine(newfield.toString())) {
                    // Was not already defined
                    p.send("(define " + newfield + "::(-> REF " + s + "))\n");
                    p.eatPrompt();
                } 
                if (!p.checkAndDefine(oldfield.toString())) {
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
                // FIXME - what to do?
            }
        }
    }
    
    public void visitUnary(JCUnary that) {
        result.append("(");
        switch (that.getTag()) {
            case JCTree.NOT:
                result.append("not ");
                break;
            case JCTree.NEG:
                result.append("- 0 ");
                break;
            default:
                System.out.println("NOT IMPL UNARY " + that.getTag());  // FIXME
                result.append("?NOTIMPL? ");
                break;
        }
        that.arg.accept(this);
        result.append(")");
    }
    
    public void visitBinary(JCBinary that) {
        result.append("(");
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
            default:
                System.out.println("NOT IMPL BINARY " + that.getTag());
                result.append("?NOTIMPL? ");
                break;
        }
        that.lhs.accept(this);
        result.append(" ");
        that.rhs.accept(this);
        result.append(")");
    }

    public void visitJmlBinary(JmlBinary that) {
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
       } else {
            System.out.println("NOT IMPL JMLBINARY " + that.getTag());
            result.append("?NOTIMPL? ");
        }
        that.lhs.accept(this);
        result.append(" ");
        that.rhs.accept(this);
        result.append(")");
    }
    
    public void visitConditional(JCConditional that) {
        result.append("(ite ");
        that.cond.accept(this);
        result.append(" ");
        that.truepart.accept(this);
        result.append(" ");
        that.falsepart.accept(this);
        result.append(")");
    }
    
    public void visitIndexed(JCArrayAccess that) {
        JCIdent arraysId = ((JmlBBArrayAccess)that).arraysId;
        Type t = that.type;
        String s = BasicBlocker.encodeType(t);
        String arr = arraysId.toString();
        String ty = "array$" + s;
        try {
            if (!p.checkAndDefine(ty)) {
                // Was not already defined
                p.send("(define-type " + ty + ")\n");
                p.eatPrompt();
            }
            if (!p.checkAndDefine(arr)) {
                // Was not already defined
                p.send("(define " + arr + "::(-> " + ty + "  int " + s + "))\n");
                p.eatPrompt();
            }
        } catch (ProverException e) {
            // FIXME - what to do?
        }

        result.append("(");
        result.append(arr);
        result.append(" ");
        that.indexed.accept(this);
        result.append(" ");
        that.index.accept(this);
        result.append(")");
    }
    
    public void visitSelect(JCFieldAccess that) {
        JCIdent fieldId = ((JmlBBFieldAccess)that).fieldId;
        Type t = that.type;
        String s = BasicBlocker.encodeType(t);
        try {
            if (!p.checkAndDefine(fieldId.toString())) {
                // Was not already defined
                p.send("(define " + fieldId + "::(-> REF " + s + "))\n");
                p.eatPrompt();
            }
        } catch (ProverException e) {
            // FIXME - what to do?
        }

        result.append("(");
        result.append(fieldId);
        result.append(" ");
        that.selected.accept(this);
        result.append(")");
    }
    
}
