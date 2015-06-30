package freeboogie.tc;

import java.util.HashMap;
import java.util.LinkedList;

import freeboogie.ast.*;
import freeboogie.util.Err;

/**
 * Constructs a {@code SymbolTable} from an AST.
 * 
 * NOTE: generic types in boogie are a hack so I'll treat them as such.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // lots of unused parameters
public class SymbolTableBuilder extends Transformer {
  private LinkedList<HashMap<String, VariableDecl>> localScopes;
  
  private SymbolTable symbolTable;
  
  private GlobalsCollector gc;
  
  private boolean errors;
  
  // for modifies spec we ignore the arguments
  private boolean lookInLocalScopes;
  
  /*
   * HACK to support `generic' types: Do not warn if we are under
   * an array because it might be a `type variable'. The typechecker
   * should enforce that things make sense a bit later on. 
   */
  // the number of ArrayType nodes above the current node 
  private int arrayCnt;
  
  /**
   * Builds a symbol table. Reports name clashes (because it
   * uses {@code GlobalsCollector}. Reports undeclared variables.
   * @param ast the AST to analyze
   * @return whether there were any problems detected
   */
  public boolean process(Declaration ast) {
    errors = false;
    localScopes = new LinkedList<HashMap<String, VariableDecl>>();
    symbolTable = new SymbolTable();
    gc = new GlobalsCollector();
    arrayCnt = 0;
    lookInLocalScopes = true;
    boolean e = gc.process(ast);
    ast.eval(this);
    return errors || e;
  }

  /**
   * Returns the symbol table.
   * @return the symbol table
   */
  public SymbolTable getST() {
    return symbolTable;
  }
  
  /**
   * Returns the globals collector, which can be used to resolve global names.
   * @return the globals collector
   */
  public GlobalsCollector getGC() {
    return gc;
  }
  
  // === helpers ===
  
  // reports an error at location l if d s null
  private <T> T check(T d, String s, AstLocation l) {
    if (d != null || arrayCnt > 0) return d;
    Err.error("" + l + ": Undeclared identifier " + s + ".");
    errors = true;
    return null;
  }
  
  // the return might by ConstDecl or VariableDecl
  private Declaration lookup(String s, AstLocation l) {
    if (lookInLocalScopes) {
      for (HashMap<String, VariableDecl> scope : localScopes) {
        VariableDecl d = scope.get(s);
        if (d != null) return d;
      }
    }
    return check(gc.idDef(s), s, l);
  }
  
  // === visit methods ===
  
  // Grr, why doesn't Java have functions as parameters or at least macros?
  
  @Override
  public void see(UserType userType, String name) {
    symbolTable.types.put(userType, check(gc.typeDef(name), name, userType.loc()));
  }

  @Override
  public void see(CallCmd callCmd, String p, Identifiers results, Exprs args) {
    symbolTable.procs.put(callCmd, check(gc.procDef(p), p, callCmd.loc()));
    if (results != null) results.eval(this);
    if (args != null) args.eval(this);
  }

  @Override
  public void see(AtomFun atomFun, String f, Exprs args) {
    symbolTable.funcs.put(atomFun, check(gc.funDef(f), f, atomFun.loc()));
    if (args != null) args.eval(this);
  }

  @Override
  public void see(AtomId atomId, String id) {
    symbolTable.ids.put(atomId, lookup(id, atomId.loc()));
  }

  // === collect info from local scopes ===
  @Override
  public void see(VariableDecl variableDecl, String name, Type type, Declaration tail) {
    HashMap<String, VariableDecl> scope = localScopes.peekFirst();
    if (scope != null && name != null) {
      // we are in a local scope
      VariableDecl old = scope.get(name);
      if (old != null) {
        Err.error("" + variableDecl.loc() + ": Variable already defined.");
        errors = true;
      } else 
        scope.put(name, variableDecl);
    }
    type.eval(this);
    if (tail != null) tail.eval(this);
  }
  
  // === keep track of local scopes ===
  @Override
  public void see(Procedure procedure, Signature sig, Specification spec, Declaration tail) {
    symbolTable.procs.seenDef(procedure);
    HashMap<String, VariableDecl> newScope = new HashMap<String, VariableDecl>();
    localScopes.addFirst(newScope);
    sig.eval(this);
    if (spec != null) spec.eval(this);
    localScopes.removeFirst();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(Implementation implementation, Signature sig, Body body, Declaration tail) {
    HashMap<String, VariableDecl> newScope = new HashMap<String, VariableDecl>();
    localScopes.addFirst(newScope);
    sig.eval(this);
    body.eval(this);
    localScopes.removeFirst();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    HashMap<String, VariableDecl> newScope = new HashMap<String, VariableDecl>();
    localScopes.addFirst(newScope);
    vars.eval(this);
    if (trig != null) trig.eval(this);
    e.eval(this);
    localScopes.removeFirst();
  }
  
  // === remember if we are below a modifies spec ===
  
  @Override
  public void see(Specification specification, Specification.SpecType type, Expr expr, boolean free, Specification tail) {
    if (type == Specification.SpecType.MODIFIES) {
      assert lookInLocalScopes; // no nesting
      lookInLocalScopes = false;
    }
    expr.eval(this);
    lookInLocalScopes = true;
    if (tail != null) tail.eval(this);
  }
  
  
  // === remember if we are below an ArrayType ===
  @Override
  public void see(ArrayType arrayType, Type rowType, Type colType, Type elemType) {
    ++arrayCnt;
    super.see(arrayType, rowType, colType, elemType);
    --arrayCnt;
  }

  // === do not lok at goto-s ===
  @Override
  public void see(Block block, String name, Commands cmds, Identifiers succ, Block tail) {
    if (cmds != null) cmds.eval(this);
    if (tail != null) tail.eval(this);
  }
  
  
}
