package freeboogie.tc;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import freeboogie.ast.Declaration;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import freeboogie.util.Err;

/**
 * Used for testing the typechecker.
 * It prints a list of identifiers and the place where they are defined.
 * It also prints errors if there are name clashes.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Main {

  /** Test a bit the package.
   * @param args the files to process
   * @throws IOException 
   * @throws RecognitionException 
   */
  public static void main(String[] args) throws IOException, RecognitionException {
    TypeChecker tc = new TypeChecker();
    for (int i = 0; i < args.length; ++i) {
      try {
        System.out.println("=== " + args[i] + " ===" );
        FbLexer lexer = new FbLexer(new ANTLRFileStream(args[i]));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FbParser parser = new FbParser(tokens);
        parser.fileName = args[i];
        Declaration d = parser.program();
        if (d != null) {
          // parsing was OK
          tc.process(d);
        }
      } catch (FileNotFoundException e) {
        Err.error("I couldn't read from " + args[i] + ". Nevermind.");
      }
    }
  }

}
