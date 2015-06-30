package freeboogie.ast.gen;

/**
 * A location for {@code Token}-s.
 * 
 * I'll use the convention that an empty token is described by two
 * pointers just before it.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 * 
 * @param <T> the token type.
 */
public class TokenLocation<T extends Token> extends Location<T> {
  private CharLocation begin;
  private CharLocation end;
  
  /**
   * Initializes a {@code TokenLocation}.
   */
  public TokenLocation() {
    begin = end = new CharLocation();
  }
  
  /**
   * Copy constructor.
   * @param other the object to copy
   */
  public TokenLocation(TokenLocation other) {
    begin = other.begin;
    end = other.end;
  }

  @Override
  public TokenLocation<T> advance(T element) {
    TokenLocation<T> r = new TokenLocation<T>(this);
    r.begin = r.end;
    if (element.rep.length() > 0)
      r.begin = r.begin.advance(element.rep.charAt(0));
    for (int i = 0; i < element.rep.length(); ++i)
      r.end = r.end.advance(element.rep.charAt(i));
    return r;
  }
  
  @Override
  public String toString() {
    return "" + begin + "--" + end;
  }
}
