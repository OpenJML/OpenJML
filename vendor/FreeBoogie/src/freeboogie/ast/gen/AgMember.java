package freeboogie.ast.gen;

/**
 * Represents a member from the abstract grammar.
 * 
 * @author rgrig
 * @author reviewed by TODO
 */
public class AgMember {
  /** The type of this member. */
  public String type = null;

  /** The name of this member. */
  public String name = null;

  /** Whether this member is a primitive. */
  public boolean primitive = true;
  
  /** Whether this member's type is an enum. */
  public boolean isenum = false;

  /**
   * Whether this member should be non-null. (note: This is about members in the
   * abstract grammar, not members in this Java code.)
   */
  public boolean nonNull = false;
}
