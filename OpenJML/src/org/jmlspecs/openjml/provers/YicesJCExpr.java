package org.jmlspecs.openjml.provers;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.esc.BasicProgram.AuxVarDSA;
import org.jmlspecs.openjml.esc.BasicProgram.ProgVarDSA;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class YicesJCExpr extends JmlTreeScanner {

    Log log;
    
    static public YicesTerm toYices(Context context, JCTree t) {
        YicesJCExpr tr = new YicesJCExpr(context);
        t.accept(tr);
        return new YicesTerm(null,tr.result.toString()); // FIXME - no type given?
    }
    
    protected YicesJCExpr(Context context) {
        log = Log.instance(context);
    }

    private StringBuilder result = new StringBuilder();

    public void visitIdent(JCIdent that) {
        result.append(that.toString());
    }
    
    public void visitProgVarDSA(ProgVarDSA that) {
        result.append(that.toString());
    }
    
    public void visitAuxVarDSA(AuxVarDSA that) {
        result.append(that.toString());
    }
    
    public void visitParens(JCParens that) {
        that.expr.accept(this);
    }
    
    public void visitLiteral(JCLiteral that) {
        result.append(that.toString());
    }
    
    public void visitApply(JCMethodInvocation that) {
        // Should have only one argument (an \old or \pre can get here)
        that.args.get(0).accept(this);
    }
    
    public void visitUnary(JCUnary that) {
        result.append("(");
        switch (that.getTag()) {
            case JCTree.NOT:
                result.append("not ");
                break;
            case JCTree.NEG:
                result.append("- ");
                break;
            default:
                System.out.println("NOT IMPL UNARY " + that.getTag());
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
    
}
