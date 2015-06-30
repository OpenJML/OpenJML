package freeboogie.ast.gen;

import java.io.IOException;
import java.io.InputStream;

/**
 * A character stream.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class CharStream extends PeekStream<Character> {
  
  private InputStream stream;
  private String name;
  
  /**
   * Sets the input stream.
   * @param stream the input stream
   */
  public CharStream(InputStream stream) {
    super(new CharLocation());
    this.stream = stream;
    this.name = "INTERNAL ERROR: CharStream name not set";
  }
  
  /**
   * Sets the input stream and the name to be used to identify it
   * (for reporting errors).
   * 
   * @param stream the input stream
   * @param name the name of the stream
   */
  public CharStream(InputStream stream, String name) {
    this(stream);
    this.name = name;
  }
  
  @Override
  public String getName() {
    return name;
  }

  /* @see freeboogie.ast.gen.PeekStream#read() */
  @Override
  public Character read() throws IOException {
    Character r = null;
    int c = stream.read();
    if (c != -1) r = Character.valueOf((char) c);
    return r;
  }
}
