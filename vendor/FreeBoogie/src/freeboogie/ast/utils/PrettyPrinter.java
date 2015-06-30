package freeboogie.ast.utils;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.Writer;
import java.math.BigInteger;
import java.util.HashMap;

import freeboogie.ast.*;
import freeboogie.util.Err;

/**
 * Prints AST nodes in a readable (and parseable) way.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // lots of unused parameters
public class PrettyPrinter extends Transformer {
  private static final int indent = 2; // indentation spaces
  
  private Writer writer; // where the output is sent
  
  /**
   * The nesting level:
   * Should be zero when I start and when I finish printing.
   */ 
  private int indentLevel;
  
  private int skipVar; // if >0 then skip "var "
  
  // ready made strings to be printed for enums
  private static final HashMap<AssertAssumeCmd.CmdType,String> cmdRep 
    = new HashMap<AssertAssumeCmd.CmdType,String>(5);
  private static final HashMap<AtomLit.AtomType,String> atomRep
    = new HashMap<AtomLit.AtomType,String>(5);
  private static final HashMap<AtomQuant.QuantType,String> quantRep
    = new HashMap<AtomQuant.QuantType,String>(5);
  private static final HashMap<BinaryOp.Op,String> binRep
    = new HashMap<BinaryOp.Op,String>(29);
  private static final HashMap<PrimitiveType.Ptype,String> typeRep
    = new HashMap<PrimitiveType.Ptype,String>(11);
  private static final HashMap<Specification.SpecType,String> specRep
    = new HashMap<Specification.SpecType,String>(5);
  private static final HashMap<UnaryOp.Op,String> unRep
    = new HashMap<UnaryOp.Op,String>(5);
  
  static {
    cmdRep.put(AssertAssumeCmd.CmdType.ASSERT, "assert ");
    cmdRep.put(AssertAssumeCmd.CmdType.ASSUME, "assume ");
    atomRep.put(AtomLit.AtomType.FALSE, "false");
    atomRep.put(AtomLit.AtomType.TRUE, "true");
    atomRep.put(AtomLit.AtomType.NULL, "null");
    quantRep.put(AtomQuant.QuantType.EXISTS, "exists ");
    quantRep.put(AtomQuant.QuantType.FORALL, "forall ");
    binRep.put(BinaryOp.Op.AND, " && ");
    binRep.put(BinaryOp.Op.DIV, " / ");
    binRep.put(BinaryOp.Op.EQ, " == ");
    binRep.put(BinaryOp.Op.EQUIV, " <==> ");
    binRep.put(BinaryOp.Op.GE, " >= ");
    binRep.put(BinaryOp.Op.GT, " > ");
    binRep.put(BinaryOp.Op.IMPLIES, " ==> ");
    binRep.put(BinaryOp.Op.LE, " <= ");
    binRep.put(BinaryOp.Op.LT, " < ");
    binRep.put(BinaryOp.Op.MINUS, " - ");
    binRep.put(BinaryOp.Op.MOD, " % ");
    binRep.put(BinaryOp.Op.MUL, " * ");
    binRep.put(BinaryOp.Op.NEQ, " != ");
    binRep.put(BinaryOp.Op.OR, " || ");
    binRep.put(BinaryOp.Op.PLUS, " + ");
    binRep.put(BinaryOp.Op.SUBTYPE, " <: ");
    typeRep.put(PrimitiveType.Ptype.ANY, "any");
    typeRep.put(PrimitiveType.Ptype.BOOL, "bool");
    typeRep.put(PrimitiveType.Ptype.INT, "int");
    typeRep.put(PrimitiveType.Ptype.NAME, "name");
    typeRep.put(PrimitiveType.Ptype.REF, "ref");
    specRep.put(Specification.SpecType.ENSURES, "ensures ");
    specRep.put(Specification.SpecType.MODIFIES, "modifies ");
    specRep.put(Specification.SpecType.REQUIRES, "requires ");
    unRep.put(UnaryOp.Op.MINUS, "-");
    unRep.put(UnaryOp.Op.NOT, "!");
  }
  
  /**
   * Initialize the pretty printer with a writer.
   * @param w the writer
   */
  public PrettyPrinter(Writer w) {
    assert w != null;
    writer = w;
    indentLevel = 0;
    skipVar = 0;
  }
  
  /** Swallow exceptions. */
  private void say(String s) {
    try {
      writer.write(s);
    } catch (IOException e) {
      Err.help("Can't pretty print. Nevermind.");
    }
  }
  
  /** Send a newline to the writer. */
  private void nl() {
    say("\n"); // TODO: handle Windows?
    for (int i = indent * indentLevel; i > 0; --i) say(" ");
  }
  
  /** End command. */
  private void semi() {
    say(";"); nl();
  }
  
  // === the visiting methods ===
  
  @Override
  public void see(ArrayType arrayType, Type rowType, Type colType, Type elemType) {
    say("[");
    rowType.eval(this);
    if (colType != null) {
      say(", ");
      colType.eval(this);
    }
    say("]");
    elemType.eval(this);
  }

  @Override
  public void see(AssertAssumeCmd assertAssumeCmd, AssertAssumeCmd.CmdType type, Expr expr) {
    say(cmdRep.get(type));
    expr.eval(this);
    semi();
  }

  @Override
  public void see(AssignmentCmd assignmentCmd, Expr lhs, Expr rhs) {
    lhs.eval(this);
    say(" := ");
    rhs.eval(this);
    semi();
  }

  @Override
  public void see(AtomCast atomCast, Expr e, Type type) {
    say("cast(");
    e.eval(this);
    say(", ");
    type.eval(this);
    say(")");
  }

  @Override
  public void see(AtomFun atomFun, String function, Exprs args) {
    say(function);
    say("(");
    if (args != null) args.eval(this);
    say(")");
  }

  @Override
  public void see(AtomId atomId, String id) {
    say(id);
  }

  @Override
  public void see(AtomIdx atomIdx, Atom atom, Index idx) {
    atom.eval(this);
    idx.eval(this);
  }

  @Override
  public void see(AtomLit atomLit, AtomLit.AtomType val) {
    say(atomRep.get(val));
  }

  @Override
  public void see(AtomNum atomNum, BigInteger val) {
    say(val.toString());
  }

  @Override
  public void see(AtomOld atomOld, Expr e) {
    say("old(");
    e.eval(this);
    say(")");
  }

  @Override
  public void see(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    ++skipVar;
    say("(");
    say(quantRep.get(quant));
    vars.eval(this);
    say(" :: ");
    if (trig != null) trig.eval(this);
    e.eval(this);
    say(")");
    --skipVar;
  }

  @Override
  public void see(Axiom axiom, Expr expr, Declaration tail) {
    say("axiom ");
    expr.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    say("(");
    left.eval(this);
    say(binRep.get(op));
    right.eval(this);
    say(")");
  }

  @Override
  public void see(Block block, String name, Commands cmds, Identifiers succ, Block tail) {
    say(name);
    say(":");
    ++indentLevel; nl();
    if (cmds != null) cmds.eval(this);
    if (succ == null) {
      say("return");
    } else {
      say("goto ");
      succ.eval(this);
    }
    semi();
    --indentLevel; nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(Body body, Declaration vars, Block blocks) {
    say(" {");
    ++indentLevel; nl();
    if (vars != null) vars.eval(this);
    if (blocks != null) blocks.eval(this);
    --indentLevel; nl();
    say("}");
    nl();
  }

  @Override
  public void see(CallCmd callCmd, String function, Identifiers results, Exprs args) {
    say("call ");
    if (results != null) {
      results.eval(this);
      say(" := ");
    }
    say(function);
    say("(");
    if (args != null) args.eval(this);
    say(");");
    nl();
  }

  @Override
  public void see(Commands commands, Command cmd, Commands tail) {
    cmd.eval(this);
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(ConstDecl constDecl, String id, Type type, Declaration tail) {
    say("const ");
    say(id);
    say(" : ");
    type.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(DepType depType, Type type, Expr pred) {
    type.eval(this);
    say(" where ");
    pred.eval(this);
  }

  @Override
  public void see(Exprs exprs, Expr expr, Exprs tail) {
    expr.eval(this);
    if (tail != null) {
      say(", ");
      tail.eval(this);
    }
  }

  @Override
  public void see(Function function, Signature sig, Declaration tail) {
    say("function ");
    sig.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(GenericType genericType, Type param, Type type) {
    say("<");
    param.eval(this);
    say(">");
    type.eval(this);
  }

  @Override
  public void see(HavocCmd havocCmd, AtomId id) {
    say("havoc ");
    id.eval(this);
    semi();
  }

  @Override
  public void see(Identifiers identifiers, AtomId id, Identifiers tail) {
    id.eval(this);
    if (tail != null) {
      say(", ");
      tail.eval(this);
    }
  }

  @Override
  public void see(Implementation implementation, Signature sig, Body body, Declaration tail) {
    say("implementation ");
    sig.eval(this);
    body.eval(this);
    nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(Index index, Expr a, Expr b) {
    say("[");
    a.eval(this);
    if (b != null) {
      say(", ");
      b.eval(this);
    }
    say("]");
  }

  @Override
  public void see(PrimitiveType primitiveType, PrimitiveType.Ptype ptype) {
    say(typeRep.get(ptype));
  }

  @Override
  public void see(Procedure procedure, Signature sig, Specification spec, Declaration tail) {
    say("procedure ");
    sig.eval(this);
    say(";");
    if (spec != null) {
      ++indentLevel; nl();
      spec.eval(this);
      --indentLevel; nl();
    }
    nl();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(Signature signature, String name, Declaration args, Declaration results) {
    ++skipVar;
    say(name);
    say("(");
    if (args != null) args.eval(this);
    say(")");
    if (results != null) {
      say(" returns (");
      results.eval(this);
      say(")");
    }
    --skipVar;
  }

  @Override
  public void see(Specification specification, Specification.SpecType type, Expr expr, boolean free, Specification tail) {
    if (free) say("free ");
    say(specRep.get(type));
    expr.eval(this);
    semi();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(TupleType tupleType, Type type, TupleType tail) {
    type.eval(this);
    if (tail != null) {
      say(", ");
      tail.eval(this);
    }
  }

  @Override
  public void see(TypeDecl typeDecl, String name, Declaration tail) {
    say("type ");
    say(name);
    semi();
    tail.eval(this);
  }

  @Override
  public void see(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    say(unRep.get(op));
    e.eval(this);
  }

  @Override
  public void see(UserType userType, String name) {
    say(name);
  }

  @Override
  public void see(VariableDecl variableDecl, String name, Type type, Declaration tail) {
    if (skipVar==0) say("var ");
    if (name != null) {
      say(name);
      say(" : ");
    }
    type.eval(this);
    if (skipVar>0) {
      if (tail != null) say(", ");
    } else semi();
    if (tail != null) tail.eval(this);
  }
  
  @Override
  public void see(Trigger trigger, String label, Exprs exprs, Trigger tail) {
    say("{");
    if (label != null) {
      say(":");
      say(label);
      say(" ");
    }
    if (exprs != null) exprs.eval(this);
    say("} ");
    if (tail != null) tail.eval(this);
  }

}
