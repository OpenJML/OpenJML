package freeboogie.ast;

/**
 * Represents a known or unknown file location.
 *  
 * @author rgrig 
 * @author reviewed by TODO
 */
public class AstLocation implements Comparable<AstLocation> {
  private String file;
  private int line, column;
  
  private static AstLocation unknown = new AstLocation();
  private AstLocation() {
    file = null;
  }
  
  /** Singleton unknown location.
   * @return the unknown location 
   */
  public static AstLocation unknown() {
    return unknown;
  }
  
  /** Creates a location from position info.
   * @param file_ The file name, preferably in full path.
   * @param line_ The line number, starting from 1.
   * @param column_ The column number, starting from 1 and 
   *                counting tabs as one char.
   */
  //@ requires file != null ==> line_ > 0;
  //@ requires file != null ==> column_ > 0;
  public AstLocation(String file_, int line_, int column_) {
    file = file_;
    line = line_;
    column = column_;
  }
  
  /** @return Returns the column. */
  public int getColumn() {
    return column;
  }

  /** @return Returns the file. */
  public String getFile() {
    return file;
  }

  /** @return Returns the line. */
  public int getLine() {
    return line;
  }

  @Override
  public String toString() {
    if (this == unknown) return "?";
    return (file == null ? "" : file + ":") + line + ":" + column;
  }

  // the Comparable<T> interface
  public int compareTo(AstLocation o) {
    if (this == unknown ^ o == unknown)
      if (this == unknown) return -1; else return +1;
    if (file != o.file) {
      if (file == null) return -1;
      if (o.file == null) return +1;
      return file.compareTo(o.file);
    }
    if (line != o.line) return line - o.line;
    return column - o.column;
  }
  
  @Override
  public boolean equals(Object o) {
    if (!(o instanceof AstLocation)) return false;
    return compareTo((AstLocation)o) == 0;
  }
}
