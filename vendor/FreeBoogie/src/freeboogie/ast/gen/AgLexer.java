package freeboogie.ast.gen;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

/**
 * Recognizes abstract grammar (AG) tokens.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class AgLexer extends PeekStream<AgToken> {
  
  private static final Map<Character, AgToken.Type> oneCharTokens
    = new HashMap<Character, AgToken.Type>(17);
  
  static {
    oneCharTokens.put('=', AgToken.Type.EQ);
    oneCharTokens.put('!', AgToken.Type.BANG);
    oneCharTokens.put(',', AgToken.Type.COMMA);
    oneCharTokens.put(';', AgToken.Type.SEMICOLON);
    oneCharTokens.put('(', AgToken.Type.LP);
    oneCharTokens.put(')', AgToken.Type.RP);
    oneCharTokens.put('\n', AgToken.Type.NL);
  }
  
  private CharStream stream;
  private Character lastChar;
  private StringBuilder repBuilder;
  
  /**
   * Initializes the lexer.
   * @param stream the underlying stream
   * @throws IOException if thrown by the underlying stream
   */
  public AgLexer(CharStream stream) throws IOException {
    super(new TokenLocation<AgToken>());
    this.stream = stream;
    repBuilder = new StringBuilder();
    readChar();
  }
  
  private void readChar() throws IOException {
    if (lastChar != null) repBuilder.append(lastChar);
    lastChar = stream.next();
  }

  private String rep() {
    String r = repBuilder.toString();
    repBuilder = new StringBuilder();
    return r;
  }
  
  /*
   * This method always reads one more character than the recognized
   * token and also eats the read characters from the underlying stream.
   *
   * The method is a bit too complex but lexers usually are.
   * 
   * @see freeboogie.ast.gen.PeekStream#read()
   */
  @Override
  protected AgToken read() throws IOException {
    if (lastChar == null) return null;
    
    AgToken.Type type = oneCharTokens.get(lastChar);
    if (type != null) {
      readChar();
    } else if (Character.isWhitespace(lastChar)) {
      type = AgToken.Type.WS;
      do readChar(); while (Character.isWhitespace(lastChar));
    } else if (lastChar == ':') {
      readChar();
      if (lastChar == '>') { 
        type = AgToken.Type.SUPERTYPE;
        readChar();
      } else 
        type = AgToken.Type.COLON;
    } else if (lastChar == '/') {
      readChar();
      if (lastChar != '/') type = AgToken.Type.ERROR;
      else {
        type = AgToken.Type.COMMENT;
        while (lastChar != '\n') readChar();
        readChar();
      }
    } else if (Character.isLetter(lastChar)) {
      do readChar();
      while (Character.isLetter(lastChar));
      if (repBuilder.toString().equals("enum")) 
        type = AgToken.Type.ENUM;
      else type = AgToken.Type.ID;
    } else {
      type = AgToken.Type.ERROR;
      readChar();
    }
    
    stream.eat();
    return new AgToken(type, rep());
  }
  
  /**
   * Like {@code next}, but skips WS, COMMENT, and ERROR tokens.
   * It also gives error messages for ERROR tokens.
   * @return the next good token
   * @throws IOException if thrown by the underlying stream
   */
  public AgToken nextGood() throws IOException {
    AgToken r;
    do r = next(); while (r != null && !r.isGood());
    return r;
  }
  
  /**
   * For testing. (TODO)
   * 
   * @param args
   */
  public static void main(String[] args) {
    // TODO Auto-generated method stub
  }
}
