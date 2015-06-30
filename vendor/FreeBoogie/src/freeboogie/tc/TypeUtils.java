package freeboogie.tc;

import java.io.StringWriter;

import freeboogie.ast.*;
import freeboogie.ast.utils.PrettyPrinter;

/**
 * Various utilities for handling {@code Type}. For the moment, it contains
 * a structural equality test that ignores AST locations. 
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class TypeUtils {
  
  // TODO: reuse this code for TypeChecker.sub. how?
  
  private static boolean eq(ArrayType a, ArrayType b) {
    return
      eq(a.getElemType(), b.getElemType()) &&
      eq(a.getRowType(), b.getRowType()) &&
      eq(a.getColType(), b.getColType());
  }
  
  private static boolean eq(PrimitiveType a, PrimitiveType b) {
    return a.getPtype() == b.getPtype();
  }
  
  private static boolean eq(GenericType a, GenericType b) {
    return eq(a.getParam(), b.getParam()) && eq(a.getType(), b.getType());
  }
  
  private static boolean eq(UserType a, UserType b) {
    return a.getName().equals(b.getName());
  }
  
  private static boolean eq(TupleType a, TupleType b) {
    if (a == b) return true;
    if (a == null ^ b == null) return false;
    return eq(a.getType(), b.getType()) && eq(a.getTail(), b.getTail());
  }

  /**
   * Recursively strip all dependent types from {@code a}.
   * @param a the type to strip of predicates
   * @return the type {@code a} striped of predicates
   */
  public static Type stripDep(Type a) {
    if (a instanceof ArrayType) {
      ArrayType sa = (ArrayType)a;
      return ArrayType.mk(stripDep(sa.getRowType()), 
        stripDep(sa.getColType()), stripDep(sa.getElemType()));
    } else if (a instanceof GenericType) {
      GenericType sa = (GenericType)a;
      return GenericType.mk(stripDep(sa.getParam()), stripDep(sa.getType()));
    } else if (a instanceof TupleType) {
      TupleType sa = (TupleType)a;
      return TupleType.mk(stripDep(sa.getType()), (TupleType)stripDep(sa.getTail()));
    } else if (a instanceof DepType) return stripDep(((DepType)a).getType());
    else return a;
  }
  
  private static Declaration stripDep(Declaration a) {
    if (!(a instanceof VariableDecl)) return a;
    VariableDecl va = (VariableDecl)a;
    return VariableDecl.mk(va.getName(), stripDep(va.getType()), stripDep(va.getTail()), va.loc());
  }

  /**
   * Returns a signature that looks like {@code s} but has all predicates
   * of dependent types removed.
   * @param s the signature to strip
   * @return the signature {@code s} without dependent types
   */
  public static Signature stripDep(Signature s) {
    return Signature.mk(s.getName(), stripDep(s.getArgs()), stripDep(s.getResults()), s.loc());
  }
  
  /**
   * Compares two types for structural equality, ignoring locations
   * and predicates of dependent types.
   * @param a the first type
   * @param b the second type
   * @return whether the two types are structurally equal
   */
  public static boolean eq(Type a, Type b) {
    if (a == b) return true;
    if (a == null ^ b == null) return false;
    if (a instanceof ArrayType && b instanceof ArrayType)
      return eq((ArrayType)a, (ArrayType)b);
    else if (a instanceof PrimitiveType && b instanceof PrimitiveType)
      return eq((PrimitiveType)a, (PrimitiveType)b);
    else if (a instanceof GenericType && b instanceof GenericType)
      return eq((GenericType)a, (GenericType)b);
    else if (a instanceof UserType && b instanceof UserType)
      return eq((UserType)a, (UserType)b);
    else if (a instanceof TupleType && b instanceof TupleType)
      return eq((TupleType)a, (TupleType)b);
    else
      return false;
  }

  /**
   * Returns whether {@code t} contains a dependent type.
   * @param t the type to check
   * @return whether {@code t} contains {@code DepType}
   */
  public static boolean hasDep(Type t) {
    if (t instanceof DepType) return true;
    else if (t instanceof ArrayType) {
      ArrayType st = (ArrayType)t;
      return 
        hasDep(st.getElemType()) || 
        hasDep(st.getRowType()) || 
        hasDep(st.getRowType()); 
    } else if (t instanceof GenericType) {
      GenericType st = (GenericType)t;
      return hasDep(st.getParam()) || hasDep(st.getType());
    } else if (t instanceof TupleType) {
      TupleType st = (TupleType)t;
      return hasDep(st.getType()) || hasDep(st.getTail());
    }
    return false;
  }

  /**
   * Pretty print a type
   * @param t the type to pretty print
   * @return the string representation of {@code t}
   */
  public static String typeToString(Type t) {
    if (t == null) return "()";
    StringWriter sw = new StringWriter();
    PrettyPrinter pp = new PrettyPrinter(sw);
    t.eval(pp);
    if (t instanceof TupleType)
      return "(" + sw + ")";
    else 
      return sw.toString();
  }
  
}
