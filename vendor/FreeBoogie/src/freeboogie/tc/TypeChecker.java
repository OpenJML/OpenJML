package freeboogie.tc;

import java.io.StringWriter;
import java.math.BigInteger;
import java.util.HashMap;

import freeboogie.ast.*;
import freeboogie.ast.utils.PrettyPrinter;
import freeboogie.util.Closure;
import freeboogie.util.Err;

/**
 * Typechecks an AST. Errors are reported using the class {@code Err}.
 * It maps expressions to types.
 * 
 * It also acts more-or-less as a Facade for the whole package.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // many unused parameters
public class TypeChecker extends Evaluator<Type> {
  
  // used for primitive types
  private PrimitiveType boolType, intType, refType, nameType, anyType;
  
  // used to signal an error in a subexpression.
  // the content is the same as for anyType but it's a different reference
  //  (unique while typechecking)
  private PrimitiveType errType;
  
  private SymbolTable st;
  
  private GlobalsCollector gc;
  
  private BlockFlowGraphs flowGraphs;
  
  // where there any type errors?
  private boolean errors;
  
  // maps expressions to their types
  private HashMap<Expr, Type> typeOf;
  
  // maps implementations to procedures
  private UsageToDefMap<Implementation, Procedure> implProc;
  
  // maps implementation params to procedure params
  private UsageToDefMap<VariableDecl, VariableDecl> paramMap;

  // Maps type variables to the real types.
  // Gets set by the |check| functions.
  private HashMap<String, Type> typeVar;
  
  // to get unique names for the type variables
  private int typeVarCnt;
  private static final String TYPE_VAR_PREFIX = " tv";
    // contains space so that it can't come from parsing
  
  // === public interface ===

  /**
   * Typechecks an AST.
   * @param ast the AST to check
   * @return whether there were any errors while typechecking (or in earlier phases) 
   */
  public boolean process(Declaration ast) {
    boolType = PrimitiveType.mk(PrimitiveType.Ptype.BOOL);
    intType = PrimitiveType.mk(PrimitiveType.Ptype.INT);
    refType = PrimitiveType.mk(PrimitiveType.Ptype.REF);
    nameType = PrimitiveType.mk(PrimitiveType.Ptype.NAME);
    anyType = PrimitiveType.mk(PrimitiveType.Ptype.ANY);
    errType = PrimitiveType.mk(PrimitiveType.Ptype.ERROR);
    
    typeOf = new HashMap<Expr, Type>();
    typeVar = new HashMap<String, Type>();
    
    errors = false;
    typeVarCnt = 0;

    // build symbol table
    SymbolTableBuilder stb = new SymbolTableBuilder();
    if (stb.process(ast)) return true;
    st = stb.getST();
    gc = stb.getGC();
    
    // check implementations
    ImplementationChecker ic = new ImplementationChecker();
    if (ic.process(ast, gc)) return true;
    implProc = ic.getImplProc();
    paramMap = ic.getParamMap();
    
    // check blocks
    flowGraphs = new BlockFlowGraphs();
    if (flowGraphs.process(ast)) return true;

    // do the typecheck
    ast.eval(this);
    return errors;
  }

  /**
   * Returns the flow graph of {@code impl}.
   * @param impl the implementation whose flow graph is requested
   * @return the flow graph of {@code impl}
   */
  public SimpleGraph<Block> getFlowGraph(Implementation impl) {
    return flowGraphs.getFlowGraph(impl);
  }
  
  /**
   * Returns the map of expressions to types.
   * @return the map of expressions to types.
   */
  public HashMap<Expr, Type> getTypes() {
    return typeOf;
  }
  
  /**
   * Returns the map from implementations to procedures.
   * @return the map from implementations to procedures
   */
  public UsageToDefMap<Implementation, Procedure> getImplProc() {
    return implProc;
  }
  
  /**
   * Returns the map from implementation parameters to procedure parameters.
   * @return the map from implementation parameters to procedure parameters
   */
  public UsageToDefMap<VariableDecl, VariableDecl> getParamMap() {
    return paramMap;
  }
  
  /**
   * Returns the symbol table.
   * @return the symbol table
   */
  public SymbolTable getST() {
    return st;
  }
  
  // === helper methods ===
  
  // report an error and set the errors flag
  // TODO: perhaps do some smarter formating
  private void report(AstLocation l, String s) {
    Err.error("" + l + ": " + s + ".");
    errors = true;
  }
  
  // assumes |d| is a list of |VariableDecl|
  // gives a TupleType with the types in that list
  private TupleType tupleTypeOfDecl(Declaration d) {
    if (d == null) return null;
    assert d instanceof VariableDecl;
    VariableDecl vd = (VariableDecl)d;
    return TupleType.mk(vd.getType(), tupleTypeOfDecl(vd.getTail()));
  }
  
  // TODO: don't forget to check that the where expressions are booleans
  // strip DepType since only the prover can handle the where clauses
  // transform one element tuples into the types they contain
  private Type strip(Type t) {
    if (t instanceof DepType)
      return strip(((DepType)t).getType());
    else if (t instanceof TupleType) {
      TupleType tt = (TupleType)t;
      if (tt.getTail() == null) return strip(tt.getType());
    }
    return t;
  }
  
  // replaces all occurrences of UserType(a) with UserType(b) 
  private Type subst(Type t, String a, String b) {
    if (t instanceof UserType) {
      UserType tt = (UserType)t;
      if (tt.getName().equals(a)) return UserType.mk(b, tt.loc());
      return t;
    } else if (t instanceof ArrayType) {
      ArrayType tt = (ArrayType)t;
      return ArrayType.mk(
        subst(tt.getRowType(), a, b),
        subst(tt.getColType(), a, b),
        subst(tt.getElemType(), a, b),
        tt.loc());
    } else if (t instanceof GenericType) {
      GenericType tt = (GenericType)t;
      return GenericType.mk(
        subst(tt.getParam(), a, b),
        subst(tt.getType(), a, b),
        tt.loc());
    } else if (t instanceof DepType) {
      DepType tt = (DepType)t;
      return subst(tt.getType(), a, b);
    }
    assert t == null || t instanceof PrimitiveType;
    return t;
  }
  
  // returns the name of the type variable or null if |t| is not a type variable
  private String typeVarName(Type t) {
    if (t instanceof UserType) {
      UserType s = (UserType)t;
      if (typeVar.containsKey(s.getName()))
        return s.getName();
    }
    return null;
  }
  
  // If |a| is a type variable, then unify it with b.
  // Returns whether a unification was performed.
  private boolean unify(Type a, Type b) {
    String an = typeVarName(a);
    if (an == null) return false;
    
    String bn;
    while ((bn = typeVarName(b)) != null && typeVar.get(bn) != null) 
      b = typeVar.get(bn);
    
    Type c = typeVar.get(an);
    sub(c, b); sub(b, c);
    
    typeVar.put(an, b);
    return true;
  }
  
  private boolean sub(PrimitiveType a, PrimitiveType b) {
    return a.getPtype() == b.getPtype();
  }
  
  private boolean sub(ArrayType a, ArrayType b) {
    if (!sub(b.getRowType(), a.getRowType())) return false;
    if (a.getColType()==null ^ b.getColType() == null) return false;
    else if (a.getColType() != null)
      if (!sub(b.getColType(), a.getColType())) return false;
    return sub(a.getElemType(), b.getElemType());
  }
  
  // TODO: Is this OK?
  private boolean sub(UserType a, UserType b) {
    return a.getName().equals(b.getName());
  }
  
  private boolean sub(GenericType a, GenericType b) {
    if (!sub(a.getParam(), b.getParam()) || !sub(b.getParam(), a.getParam()))
      return false;
    return sub(a.getType(), b.getType());
  }
  
  private boolean sub(TupleType a, TupleType b) {
    if (!sub(a.getType(), b.getType())) return false;
    TupleType ta = a.getTail();
    TupleType tb = b.getTail();
    if (ta == tb) return true;
    if (ta == null ^ tb == null) return false;
    return sub(ta, tb);
  }

  // returns (a <: b)
  private boolean sub(Type a, Type b) {
    // get rid of where clauses and make tuples with one element non-tuples
    a = strip(a); b = strip(b);
    
    if (a == b) return true; // the common case
    if (a == errType || b == errType) return true; // don't trickle up errors
    
    // an empty tuple is only the same with an empty tuple
    if (a == null ^ b == null) return false;
    
    
    // check if b is ANY
    if (b instanceof PrimitiveType) {
      PrimitiveType sb = (PrimitiveType)b;
      if (sb.getPtype() == PrimitiveType.Ptype.ANY) return true;
    }
    
    // the `generics' hack
    if (unify(a, b) || unify(b, a)) return true;
    
    // allow T to be used when <tv>T is needed and tv is a type variable
    if (b instanceof GenericType && !(a instanceof GenericType)) {
      GenericType sb = (GenericType)b;
      if (typeVarName(sb.getParam()) != null && sub(a, sb.getType()))
        return unify(sb.getParam(), anyType);
    }
    
    // allow <x>T to be used where T is expected
    if (a instanceof GenericType && !(b instanceof GenericType)) {
      GenericType sa = (GenericType)a;
      if (sub(sa.getType(), b)) return true;
    }
    
    // the main check
    if (a instanceof PrimitiveType && b instanceof PrimitiveType)
      return sub((PrimitiveType)a, (PrimitiveType)b);
    else if (a instanceof ArrayType && b instanceof ArrayType)
      return sub((ArrayType)a, (ArrayType)b);
    else if (a instanceof UserType && b instanceof UserType) 
      return sub((UserType)a, (UserType)b);
    else if (a instanceof GenericType && b instanceof GenericType)
      return sub((GenericType)a, (GenericType)b);
    else if (a instanceof TupleType && b instanceof TupleType)
      return sub((TupleType)a, (TupleType)b);
    else
      return false;
  }
  
  /**
   * If {@code a} cannot be used where {@code b} is expected then an error
   * at location {@code l} is produced and {@code errors} is set.
   */
  private void check(Type a, Type b, AstLocation l) {
    if (sub(a, b)) return;
    report(l, "Found type " + TypeUtils.typeToString(a) 
      + " instead of " + TypeUtils.typeToString(b));
  }
  
  /**
   * Same as {@code check}, except it is more picky about the types:
   * They must be exactly the same.
   */
  private void checkExact(Type a, Type b, AstLocation l) {
    if (sub(a, b) || sub(b, a)) return;
    report(l, "Unrelated types: "
      + TypeUtils.typeToString(a) + " and " + TypeUtils.typeToString(b));
  }
  
  // === visiting operators ===
  @Override
  public PrimitiveType eval(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    Type t = strip(e.eval(this));
    switch (op) {
    case MINUS:
      check(t, intType, e.loc());
      typeOf.put(unaryOp, intType);
      return intType;
    case NOT:
      check(t, boolType, e.loc());
      typeOf.put(unaryOp, boolType);
      return boolType;
    default:
      assert false;
      return null; // dumb compiler
    }
  }

  @Override
  public PrimitiveType eval(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    Type l = strip(left.eval(this));
    Type r = strip(right.eval(this));
    switch (op) {
    case PLUS:
    case MINUS:
    case MUL:
    case DIV:
    case MOD:
      // integer arguments and integer result
      check(l, intType, left.loc());
      check(r, intType, right.loc());
      typeOf.put(binaryOp, intType);
      return intType;
    case LT:
    case LE:
    case GE:
    case GT:
      // integer arguments and boolean result
      check(l, intType, left.loc());
      check(r, intType, right.loc());
      typeOf.put(binaryOp, boolType);
      return boolType;
    case EQUIV:
    case IMPLIES:
    case AND:
    case OR:
      // boolean arguments and boolean result
      check(l, boolType, left.loc());
      check(r, boolType, right.loc());
      typeOf.put(binaryOp, boolType);
      return boolType;
    case SUBTYPE:
      // l subtype of r and boolean result (TODO: a user type is a subtype of a user type)
      check(l, r, left.loc());
      typeOf.put(binaryOp, boolType);
      return boolType;
    case EQ:
    case NEQ:
      // typeOf(l) == typeOf(r) and boolean result
      checkExact(l, r, binaryOp.loc());
      typeOf.put(binaryOp, boolType);
      return boolType;
    default:
      assert false;
      return errType; // dumb compiler
    }
  }
  
  // === visiting atoms, including arrays with that `generic' hack ===
  @Override
  public Type eval(AtomId atomId, String id) {
    Declaration d = st.ids.def(atomId);
    Type t = errType;
    if (d == null)
      // HACK for `generics'
      t = UserType.mk(id);
    else {
      if (d instanceof VariableDecl)
        t = ((VariableDecl)d).getType();
      else if (d instanceof ConstDecl)
        t = ((ConstDecl)d).getType();
      else
        assert false;
    }
    typeOf.put(atomId, t);
    return t;
  }

  @Override
  public PrimitiveType eval(AtomNum atomNum, BigInteger val) {
    typeOf.put(atomNum, intType);
    return intType;
  }

  @Override
  public PrimitiveType eval(AtomLit atomLit, AtomLit.AtomType val) {
    switch (val) {
    case TRUE:
    case FALSE:
      typeOf.put(atomLit, boolType);
      return boolType;
    case NULL:
      typeOf.put(atomLit, refType);
      return refType;
    default:
      assert false;
      return errType; // dumb compiler 
    }
  }

  @Override
  public Type eval(AtomOld atomOld, Expr e) {
    Type t = e.eval(this);
    typeOf.put(atomOld, t);
    return t;
  }

  @Override
  public PrimitiveType eval(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    Type t = e.eval(this);
    check(t, boolType, e.loc());
    typeOf.put(atomQuant, boolType);
    return boolType;
  }

  @Override
  public Type eval(AtomFun atomFun, String function, Exprs args) {
    Function d = st.funcs.def(atomFun);
    Signature sig = d.getSig();
    Declaration fargs = sig.getArgs();
    
    Type at = strip(args == null? null : (TupleType)args.eval(this));
    Type fat = strip(tupleTypeOfDecl(fargs));
    
    check(at, fat, args == null? atomFun.loc() : args.loc());
    Type rt = strip(tupleTypeOfDecl(sig.getResults()));
    typeOf.put(atomFun, rt);
    return rt;
  }

  @Override
  public Type eval(AtomCast atomCast, Expr e, Type type) {
    e.eval(this);
    typeOf.put(atomCast, type);
    return type;
  }

  @Override
  public Type eval(AtomIdx atomIdx, Atom atom, Index idx) {
    Type t = strip(atom.eval(this));
    if (t == errType) return errType;
    if (!(t instanceof ArrayType)) {
      Err.error("" + atom.loc() + ": Must be an array.");
      errors = true;
      return null;
    }
    ArrayType at = (ArrayType)t;
    Type et = at.getElemType();

    // the bulk of the `generic' hack
    String resultTypeVar = null;
    String freshTypeVar = null;
    if (et instanceof UserType) {
      UserType uet = (UserType)et;
      if (st.types.def(uet) == null) {
        // make uet a type variable
        resultTypeVar = uet.getName();
        freshTypeVar = TYPE_VAR_PREFIX + typeVarCnt++;
        at = (ArrayType)subst(at, resultTypeVar, freshTypeVar);
        typeVar.put(freshTypeVar, null);
      }
    }
    
    // look at indexing types
    check(idx.getA().eval(this), at.getRowType(), idx.getA().loc());
    if (idx.getB() != null)
      check(idx.getB().eval(this), at.getColType(), idx.getB().loc());

    // get the result type in case it was a type variable
    if (resultTypeVar != null) {
      et = typeVar.get(freshTypeVar);
      if (et == null) {
        report(atomIdx.loc(), "Can't deduce array type");
        et = errType;
      }
      typeVar.remove(freshTypeVar);
    }
    
    typeOf.put(atomIdx, et);
    return et;
  }
  
  // === visit commands ===
  @Override
  public Type eval(AssignmentCmd assignmentCmd, Expr lhs, Expr rhs) {
    Type lt = strip(lhs.eval(this));
    Type rt = strip(rhs.eval(this));
    check(rt, lt, assignmentCmd.loc());
    return null;
  }

  @Override
  public Type eval(AssertAssumeCmd assertAssumeCmd, AssertAssumeCmd.CmdType type, Expr expr) {
    Type t = expr.eval(this);
    check(t, boolType, assertAssumeCmd.loc());
    return null;
  }

  @Override
  public Type eval(CallCmd callCmd, String procedure, Identifiers results, Exprs args) {
    Procedure p = st.procs.def(callCmd);
    Signature sig = p.getSig();
    Declaration fargs = sig.getArgs();
    
    // check the actual arguments against the formal ones
    Type at = strip(args == null? null : args.eval(this));
    Type fat = strip(tupleTypeOfDecl(fargs));
    check(at, fat, (args == null? callCmd.loc() : args.loc()));
    
    // check the assignment of the results
    Type lt = strip(results == null? null : results.eval(this));
    Type rt = strip(tupleTypeOfDecl(sig.getResults()));
    check(rt, lt, callCmd.loc());
    
    return null;
  }
  
  // === visit dependent types ===
  @Override
  public DepType eval(DepType depType, Type type, Expr pred) {
    Type t = pred.eval(this);
    check(t, boolType, pred.loc());
    return null;
  }
  
  // === visit Exprs and Identifiers to make TupleType-s ===
  @Override
  public TupleType eval(Exprs exprs, Expr expr, Exprs tail) {
    Type t = expr.eval(this);
    assert t != null; // shouldn't have nested tuples
    TupleType tt = tail == null? null : (TupleType)tail.eval(this);
    TupleType rt = TupleType.mk(t, tt);
    typeOf.put(exprs, rt);
    return rt;
  }

  @Override
  public TupleType eval(Identifiers identifiers, AtomId id, Identifiers tail) {
    Type t = id.eval(this);
    TupleType tt = tail == null? null : (TupleType)tail.eval(this);
    TupleType rt = TupleType.mk(t, tt);
    // TODO: put this in typeOf?
    return rt;
  }
  
  // === visit various things that must have boolean params ===
  @Override
  public Type eval(Axiom axiom, Expr expr, Declaration tail) {
    Type t = expr.eval(this);
    check(t, boolType, expr.loc());
    if (tail != null) tail.eval(this);
    return null;
  }

  @Override
  public Type eval(Specification specification, Specification.SpecType type, Expr expr, boolean free, Specification tail) {
    Type t = null;
    switch (type) {
    case REQUIRES:
    case ENSURES:
      t = expr.eval(this);
      check(t, boolType, expr.loc());
    case MODIFIES:
      break;
    default:
      assert false;
      return errType; // dumb compiler
    }
    if (tail != null) tail.eval(this);
    return null;
  }
  
  // === do not look at block successors ===
  @Override
  public Type eval(Block block, String name, Commands cmds, Identifiers succ, Block tail) {
    if (cmds != null) cmds.eval(this);
    if (tail != null) tail.eval(this);
    return null;
  }

  
}
