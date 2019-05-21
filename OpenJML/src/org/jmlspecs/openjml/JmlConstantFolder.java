package org.jmlspecs.openjml;

import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.vistors.JmlTreeTranslator;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class JmlConstantFolder extends JmlTreeTranslator {

    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    final public JmlTreeUtils treeutils;

    /** Cached value of the symbol table */
    final public Symtab syms;

    /** Cached value of the Types tool */
    final public Types types;

    /** Cached value of the Log tool */
    final public Log log;

    /** Cached value of the AST node factory */
    final public JmlTree.Maker M;

    public JmlConstantFolder(Context context) {
        copy = false;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
    }
    
    public boolean isIntZero(JCLiteral lit) {
        return lit.type.getTag() == TypeTag.INT && ((Number)lit.getValue()).intValue() == 0;
    }
    public boolean isLongZero(JCLiteral lit) {
        return lit.type.getTag() == TypeTag.LONG && ((Number)lit.getValue()).intValue() == 0;
    }

    @Override
    public void visitBinary(JCBinary tree) {
        tree.lhs = translate(tree.lhs);
        tree.rhs = translate(tree.rhs);
        JCLiteral lhs = tree.lhs instanceof JCLiteral ? (JCLiteral)tree.lhs : null;
        JCLiteral rhs = tree.rhs instanceof JCLiteral ? (JCLiteral)tree.rhs : null;
        boolean bothlit = lhs != null && rhs != null;
        Object lhsv = lhs != null ? lhs.getValue() : null;
        Object rhsv = rhs != null ? rhs.getValue() : null;
        Object res = null;
        JCBinary that = tree;
        switch (tree.getTag()) {
            case EQ: 
                if (bothlit) res = lhsv.equals(rhsv); 
                break;
            case NE: 
                if (bothlit) res = !lhsv.equals(rhsv); 
                break;
            case AND: {
                if (bothlit) res = (Boolean)lhsv && (Boolean)rhsv; 
                else if (lhsv != null) res = (Boolean)lhsv ? rhs : lhs;
                else if (rhsv != null) res = (Boolean)rhsv ? lhs : rhs;
                break;
            }
            case OR: {
                if (bothlit) res = (Boolean)lhsv || (Boolean)rhsv; 
                else if (lhsv != null) res = (Boolean)lhsv ? lhs : rhs;
                else if (rhsv != null) res = (Boolean)rhsv ? rhs : lhs;
                break;
            }
            case PLUS: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (tree.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() + ((Number)rhsv).intValue();
                    } else if (tree.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() + ((Number)rhsv).longValue();
                    } else if (types.isSameType(tree.type,syms.stringType)) {
                        // FIXME - what about null arguments?
                        res = lhs.toString() + rhsv.toString();
                    } // bigint, real float double string
                } else if (rhs != null) {
                    if (isIntZero(rhs)) {
                        res = tree.lhs;
                    } else if (isLongZero(rhs)) {
                        res = tree.lhs;
                    }
                     // bigint, real float double string
                } else if (lhs != null) {
                    if (isIntZero(lhs)) {
                        res = tree.rhs;
                    } else if (isLongZero(lhs)) {
                        res = tree.rhs;
                    }
                     // bigint, real float double string
                }
                break;
            case MINUS: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() - ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() - ((Number)rhsv).longValue();
                    } // bigint, real flot double string
                } else if (rhs != null) {
                    if (rhs.type.getTag() == TypeTag.INT && ((Number)lhsv).intValue() == 0) {
                        res = tree.lhs;
                    } else if (rhs.type.getTag() == TypeTag.LONG && ((Number)lhsv).longValue() == 0) {
                        res = tree.lhs;
                    }
                     // bigint, real float double string
                }
                break;
            case MUL: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        int kl = ((Number)lhsv).intValue();
                        int kr = ((Number)rhsv).intValue();
                        int r = kl * kr;
                        if (kl != 0 && r/kl != kr) {
                            log.warning(tree, "jml.message", "Literal multiply overflow");
                            break;
                        }
                        res = r;
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() * ((Number)rhsv).longValue();
                    } // bigint, real
                }
                break;
            case DIV: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        int d = ((Number)rhsv).intValue();
                        if (d == 0) {
                            log.warning(that.rhs, "jml.message", "Literal divide by zero");
                            break;
                        } else {
                            res = ((Number)lhsv).intValue() / d;
                        }
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        long d = ((Number)rhsv).longValue();
                        if (d == 0) {
                            log.warning(that.rhs, "jml.message", "Literal divide by zero");
                            break;
                        } else {
                            res = ((Number)lhsv).longValue() / d;
                        }
                    }
                    // bigint, real

                }
                break;
            case MOD: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        int d = ((Number)rhsv).intValue();
                        if (d == 0) {
                            log.warning(that.rhs, "jml.message", "Literal mod by zero");
                            res = 0;
                        } else {
                            res = ((Number)lhsv).intValue() % d;
                        }
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        long d = ((Number)rhsv).longValue();
                        if (d == 0) {
                            log.warning(that.rhs, "jml.message", "Literal mod by zero");
                            res = 0;
                        } else {
                            res = ((Number)lhsv).longValue() % d;
                        }
                    }
                    // bigint, real

                }
                break;
            case BITAND:  // FIXME - logical result?
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() & ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() & ((Number)rhsv).longValue();
                    } else if (that.type.getTag() == TypeTag.BOOLEAN) {
                        res = ((Boolean)lhsv).booleanValue() & ((Boolean)rhsv).booleanValue();
                    } // bigint
                }
                break;
            case BITOR:  // FIXME - logical result?
                if (bothlit) { 

                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() | ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() & ((Number)rhsv).longValue();
                    } else if (that.type.getTag() == TypeTag.BOOLEAN) {
                        res = ((Boolean)lhsv).booleanValue() | ((Boolean)rhsv).booleanValue();
                    } // bigint
                }
                break;
            case BITXOR:  // FIXME - logical result?
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() ^ ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() & ((Number)rhsv).longValue();
                    } else if (that.type.getTag() == TypeTag.BOOLEAN) {
                        res = ((Boolean)lhsv).booleanValue() != ((Boolean)rhsv).booleanValue();
                    } // bigint
                }
                break;
            case GT:
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() > ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() > ((Number)rhsv).longValue();
                    } // bigint, real
                }
                break;
            case GE: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() >= ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() >= ((Number)rhsv).longValue();
                    } // bigint, real
                }
                break;
            case LT: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() < ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() < ((Number)rhsv).longValue();
                    } // bigint, real
                }
                break;
            case LE: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() <= ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() <= ((Number)rhsv).longValue();
                    } // bigint, real
                }
                break;
            case SL: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() << ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() << ((Number)rhsv).longValue();
                    } // bigint, real
                }
                break;
            case SR: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() >> ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() >> ((Number)rhsv).longValue();
                    } // bigint, real
                }
                break;
            case USR: // FIXME - what about overflow checks and arithmetic mode
                if (bothlit) { 
                    if (that.type.getTag() == TypeTag.INT) {
                        res = ((Number)lhsv).intValue() >>> ((Number)rhsv).intValue();
                    } else if (that.type.getTag() == TypeTag.LONG) {
                        res = ((Number)lhsv).longValue() >>> ((Number)rhsv).longValue();
                    } // bigint, real
                } 
                break;
            default:
                result = tree;
                return ;
        }
        if (res == null) {
            // Not a case for constant folding
            result = tree;
            return ;
        }
        result = M.at(tree).Literal(res);
        treeutils.copyEndPosition(tree,result);
    }

    @Override
    public void visitJmlBinary(JmlBinary that) {
        JmlBinary r = copy ? new JmlBinary(that) : that;
        r.lhs = translate(that.lhs);
        r.rhs = translate(that.rhs);
        // Not translating: op, opcode, operator
        result = r;
    }

    public void visitIf(JCIf tree) {
        JCExpression c = tree.cond = translate(tree.cond);
        tree.thenpart = translate(tree.thenpart);
        tree.elsepart = translate(tree.elsepart);
        result = tree;
        if (c instanceof JCLiteral) {
            Object v = ((JCLiteral)c).getValue();
            if ((Boolean)v) result = tree.thenpart;
            else result = tree.elsepart;
        }
    }
    
    Map<Symbol,JCLiteral> constants = new HashMap<>();

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        super.visitJmlVariableDecl(that);
        JCExpression init = ((JmlVariableDecl)result).init;
        if (that.sym.owner instanceof Symbol.MethodSymbol && init instanceof JCLiteral) {
            // Local variable
            constants.put(that.sym, (JCLiteral)init);
        }
    }
    
    public void visitAssign(JCAssign tree) {
        super.visitAssign(tree);
        JCExpression lhs = ((JCAssign)result).lhs;
        JCExpression v = ((JCAssign)result).rhs;
        if (lhs instanceof JCIdent) {
            Symbol s = ((JCIdent)lhs).sym;
            if (s.owner instanceof Symbol.MethodSymbol) {
                if (v instanceof JCLiteral) {
                    constants.put(s, (JCLiteral)v);
                } else {
                    constants.remove(s);
                }
            }
        }
    }
}
