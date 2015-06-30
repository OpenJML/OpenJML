package freeboogie.tc;

import java.util.HashMap;

import freeboogie.ast.*;
import freeboogie.util.Err;

/**
 * Checks whether the implementations' signatures correspond to the
 * procedure signatures. It also connects in/out {@code VariableDecl}
 * arguments of the implementation with the one in the procedure.
 * (This link is needed later when verifying that the implementation
 * satisfies the spec that accompanies the procedure.) it produces
 * errors if an implementation does not have a corresponding procedure
 * or if there is a type mismatch in the signature.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // unused parameters
public class ImplementationChecker extends Transformer {
  private boolean errors;
  private GlobalsCollector gc;
  
  // connects implementations to procedures
  private UsageToDefMap<Implementation, Procedure> implProc;
  
  // connects implementation parameters to procedure parameters
  private UsageToDefMap<VariableDecl, VariableDecl> paramMap;
  
  // === public interface ===
  
  /**
   * Processes the implementations in {@code ast} assuming that {@code p}
   * maps procedure names to their AST nodes. ({@code GlobalsCollector} provides
   * such a mapping.)
   * @param ast the AST to check
   * @param g the globals collector that can resolve procedure names 
   * @return whether any errors were detected
   */
  public boolean process(Declaration ast, GlobalsCollector g) {
    errors = false;
    gc = g;
    implProc = new UsageToDefMap<Implementation, Procedure>();
    paramMap = new UsageToDefMap<VariableDecl, VariableDecl>();
    ast.eval(this);
    return errors;
  }
  
  /**
   * Returns the map linking procedures to their usages.
   * @return the map linking procedures to their usages
   */
  public UsageToDefMap<Implementation, Procedure> getImplProc() {
    return implProc;
  }
  
  /**
   * Returns the map of implementation in/out parameters to the map
   * of procedure in/out parameters.
   * @return the link between implementation and procedure parameters
   */
  public UsageToDefMap<VariableDecl, VariableDecl> getParamMap() {
    return paramMap;
  }
  
  // === helpers ==
  private void report(AstLocation l, String s) {
    Err.error("" + l + ": " + s + ".");
    errors = true;
  }
  
  // assumes {@code a} and {@code b} are lists of {@code VariableDecl}
  // compares their types and connects them in implDecl
  // reports type mismatches
  private void compare(Declaration a, Declaration b) {
    if (a == null && b == null) return;
    if (a == null ^ b == null) {
      report(a==null? b.loc() : a.loc(), "Implementation-Procedure parameter count mismatch");
      return;
    }
    
    VariableDecl va = (VariableDecl)a;
    VariableDecl vb = (VariableDecl)b;
    if (!TypeUtils.eq(TypeUtils.stripDep(va.getType()), TypeUtils.stripDep(vb.getType()))) {
      report(va.loc(), "Type should be " + TypeUtils.typeToString(vb.getType()));
      return;
    }
    paramMap.put(va, vb);
  }
  
  // assumes {@code a} and {@code b} are lists of {@code VariableDecl}
  // checks that a does not have dependent types
  private void depCheck(Declaration a) {
    if (a == null) return;
    VariableDecl va = (VariableDecl)a;
    if (TypeUtils.hasDep(va.getType()))
      report(va.loc(), "Dependent type in implementation signature");
  }
  
  // === visiting implementations ===

  @Override
  public void see(Implementation implementation, Signature sig, Body body, Declaration tail) {
    String name = sig.getName();
    Procedure p = gc.procDef(name);
    if (p == null) {
      report(implementation.loc(), "Implementation without procedure");
      return;
    }
    
    implProc.put(implementation, p);
    
    Signature psig = p.getSig();
    compare(sig.getArgs(), psig.getArgs());
    compare(sig.getResults(), psig.getResults());
    
    depCheck(sig.getArgs());
    depCheck(sig.getResults());

    if (tail != null) tail.eval(this);
  }
}
