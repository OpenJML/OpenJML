package freeboogie.ast.gen;

import java.util.HashSet;
import java.util.Set;

/**
 * Represents an enum from the abstract grammar.
 * 
 * @author rgrig
 * @author reviewed by TODO
 */
public class AgEnum {
  /** The name of the enum. */
  public String name = null;

  /** The values of the enum. */
  public Set<String> values = new HashSet<String>(23);
}
