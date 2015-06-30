package freeboogie.ast.gen;

import java.io.IOException;
import java.io.InputStream;
import java.util.logging.Logger;

import freeboogie.util.Err;

/**
 * Used for flow control in {@code AgParser}.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("serial")
class EofReached extends Exception {
  // only the type is important
}

/**
 * A hand-crafted parser for abstract grammar (AG) textual descriptions.
 * See packages {@link freeboogie.ast} and {@link freeboogie.ast.gen}
 * for examples. A reason why this is handcrafted is that I want to
 * compare the experience of writing it with the experience of writing
 * the BoogiePL parser using ANTLR. It should also be not too hard since
 * the input language is <i>really</i> simple. On the other hand I can 
 * explore the design space of a parse more, for example by giving really
 * custom error messages and hints of what might be wrong.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class AgParser {
  
  private static final Logger log = Logger.getLogger("freeboogie.ast.gen"); 
  
  private AgLexer lexer;
  private Grammar grammar;
  
  private boolean okToFinish;
  
  /**
   * Creates an AG parser.
   */
  public AgParser() {
    grammar = new Grammar();
    okToFinish = false;
  }
  
  /**
   * Sets the input stream for the next parsing operation. 
   * @param stream the input stream
   * @throws IOException 
   */
  public void setInputStream(InputStream stream) throws IOException {
    lexer = new AgLexer(new CharStream(stream));
  }
  
  /** 
   * This will read in an AG from the input stream.
   * 
   * @throws IOException if thrown by the underlying stream 
   */
  public void parseAg() throws IOException {
    try {
      while (true) parseStatement();
    } catch (EofReached e) {
      if (!okToFinish) {
        Err.error("The end of file took me by surprise.");
        Err.help("Did you forget a semicolon?");
      } 
    }
  }
  
  /**
   * Gets the grammar. Initially it is empty.
   * @return the grammar
   */
  public Grammar getGrammar() {
    return grammar;
  }
  
  private void parseStatement() throws IOException, EofReached {
    okToFinish = true;
    AgToken t = nextToken();
    if (t.type != AgToken.Type.ID) {
      skipStatementBecauseOf(t);
      return;
    }
    okToFinish = false;
    
    String className = t.rep;
    t = nextToken();
    if (t.type == AgToken.Type.EQ) {
      // parse "class = members"
      parseMembers(className);
    } else if (t.type == AgToken.Type.COLON) {
      // parse "class : spec\n"
      parseSpec(className);
    } else if (t.type == AgToken.Type.SUPERTYPE) {
      // parse "class :> derived"
      parseSubclasses(className);
    } else {
      skipStatementBecauseOf(t);
      return;
    }
    lexer.eat();
    log.fine("Parsed statement from AG (" + className + ").");
  }
  
  private void parseMembers(String className) 
  throws IOException, EofReached {
    AgClass cls = grammar.getAgClass(className);
    int memCnt = 0;

    // The user should not see this sentinel token.
    AgToken t = new AgToken(AgToken.Type.COMMA, "INTERNAL ERROR"); 
    while (t.type == AgToken.Type.COMMA) {
      t = nextToken();
      AgMember mem = new AgMember();
      if (t.type == AgToken.Type.ENUM) {
        mem.type = parseEnum(cls);
        if (mem.type == null) return;
      } else if (t.type == AgToken.Type.ID)
        mem.type = t.rep;
      else {
        if (memCnt == 0) 
          Err.help("You should specify at least one member in a '=' statement.");
        skipStatementBecauseOf(t);
        return;
      }
      t = nextToken();
      if (t.type == AgToken.Type.BANG) {
        mem.nonNull = true;
        t = nextToken();
      }
      if (t.type != AgToken.Type.ID) {
        err("I was expecting a name for this member.");
        skipStatementBecauseOf(t);
        return;
      }
      mem.name = t.rep;
      cls.members.add(mem);
      ++memCnt;
      t = nextToken();
    }
    if (t.type != AgToken.Type.SEMICOLON) 
      skipStatementBecauseOf(t);
  }
  
  /* Reads all the text up to the first newline */
  private void parseSpec(String className) throws IOException {
    AgClass cls = grammar.getAgClass(className);
    StringBuilder sb = new StringBuilder();
    AgToken tok = lexer.next();
    while (tok != null && tok.type != AgToken.Type.NL) {
      sb.append(tok.rep);
      tok = lexer.next();
    }
    if (tok == null) {
      Err.error("The spec for '" + className + "' ends abruptly.");
      Err.help("No newline at the end of the grammar file?");
    }
    cls.invariants.add(sb.toString());
  }
  
  private void parseSubclasses(String className) 
  throws IOException, EofReached {
    grammar.getAgClass(className);
    AgToken id, sep;
    id = nextToken();
    if (id.type == AgToken.Type.SEMICOLON) {
      err("This :> statement is meaningless.");
      return;
    }
    while (true) {
      if (id.type != AgToken.Type.ID) {
        skipStatementBecauseOf(id);
        return;
      }
      AgClass derived = grammar.getAgClass(id.rep);
      if (derived.base != null) {
        err("You specify multiple base classes for '" + derived.name +"'");
        Err.help("I'll use '" + derived.base + "'");
      } else
        derived.base = className;
      sep = nextToken();
      if (sep.type == AgToken.Type.SEMICOLON) break;
      if (sep.type != AgToken.Type.COMMA) {
        skipStatementBecauseOf(sep);
        return;
      }
      id = nextToken();
    }
  }
  
  /*
   * Parses (enum_name; val1, ..., valn), adds this to the class cls,
   * and returns enum_name. Returns null if parsing fails.
   */
  private String parseEnum(AgClass cls) throws IOException, EofReached {
    AgToken t = nextToken();
    if (t.type != AgToken.Type.LP) {
      err("I was expecting '(' after 'enum'.");
      Err.help("Are you trying to use 'enum' as a type name?");
      skipStatementBecauseOf(t);
      return null;
    }
    
    t = nextToken();
    if (t.type != AgToken.Type.ID) {
      err("There should be an enum name here.");
      skipStatementBecauseOf(t);
      return null;
    }
    AgEnum agEnum = cls.getEnum(t.rep);
    
    t = nextToken();
    if (t.type != AgToken.Type.COLON) {
      err("I was expecting ':' after the enum type name.");
      skipStatementBecauseOf(t);
      return null;
    }
    t = nextToken();
    if (t.type == AgToken.Type.RP) return agEnum.name;
    while (true) {
      if (t.type != AgToken.Type.ID) {
        err("I was expecting an enum value.");
        skipStatementBecauseOf(t);
        return null;
      }
      agEnum.values.add(t.rep);
      t = nextToken();
      if (t.type == AgToken.Type.RP) break;
      if (t.type != AgToken.Type.COMMA) {
        err("I was expecting a comma between enum values.");
        skipStatementBecauseOf(t);
        return null;
      }
      t = nextToken();
    }
      
    return agEnum.name;
  }
  
  private void skipStatementBecauseOf(AgToken tok) 
  throws IOException, EofReached {
    StringBuilder sb = new StringBuilder();
    err("I'm confused by '" + tok.rep + "'");
    do {
      tok = nextToken();
      if (tok.type == AgToken.Type.ID) sb.append(' ');
      sb.append(tok.rep);
    } while (tok.type != AgToken.Type.SEMICOLON);
    Err.error("I skipped: " + sb);
    lexer.eat();
  }
  
  private AgToken nextToken() throws IOException, EofReached {
    AgToken token = lexer.nextGood();
    if (token == null) throw new EofReached();
    log.finer("read token: " + token.rep);
    return token;
  }

  private void err(String e) {
    lexer.eat();
    Err.error("AG" + lexer.getLoc() + ": " + e);
  }
  
  /**
   * For testing purposes. (TODO)
   * @param args
   */
  public static void main(String[] args) {
  // TODO Auto-generated method stub

  }
}
