package freeboogie.tc;

import freeboogie.ast.*;

/**
 * A structure whose members connect usages to definitions.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class SymbolTable {
  /** User defined types */
  public UsageToDefMap<UserType, TypeDecl> types
    = new UsageToDefMap<UserType, TypeDecl>();
  
  /** Procedures */
  public UsageToDefMap<CallCmd, Procedure> procs
    = new UsageToDefMap<CallCmd, Procedure>();
  
  /** Functions */
  public UsageToDefMap<AtomFun, Function> funcs
    = new UsageToDefMap<AtomFun, Function>();
  
  /**
   * Identifiers. The declarations might only be {@code ConstDecl} and
   * {@code VariableDecl}.
   */
  public UsageToDefMap<AtomId, Declaration> ids
    = new UsageToDefMap<AtomId, Declaration>();
}
