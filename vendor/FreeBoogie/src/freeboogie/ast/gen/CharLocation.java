package freeboogie.ast.gen;

/**
 * A simple line-column structure.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class CharLocation extends Location<Character> {
  private int line, col;
  private boolean eof;
  private boolean newLine;
  
  /** Initialization */
  public CharLocation() {
    line = 0;
    col = -1;
    eof = false;
  }
  
  /**
   * Copy constructor.
   * @param other the other object
   */
  public CharLocation(CharLocation other) {
    line = other.line;
    col = other.col;
    eof = other.eof;
  }
  
  @Override
  public CharLocation advance(Character element) {
    CharLocation result = new CharLocation(this);
    if (element == null) result.eof = true;
    if (result.eof) return result;
    if (newLine) {
      ++result.line; result.col = 0;
    } else ++result.col;
    result.newLine = element == '\n';
    return result;
  }
  
  @Override
  public String toString() {
    if (eof) return "EOF";
    return "(" + (line + 1) + ", " + (col + 1) + ")";
  }
}
