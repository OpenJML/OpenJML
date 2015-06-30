package freeboogie.parser;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import freeboogie.ast.Declaration;
import freeboogie.ast.utils.PrettyPrinter;
import freeboogie.util.Err;

/**
 * Generate a pretty print of the AST constructed during parsing.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Main {

  /**
   * @param args
   * @throws IOException 
   * @throws RecognitionException 
   */
  public static void main(String[] args) throws IOException, RecognitionException {
    PrintWriter pw = new PrintWriter(System.out);
    PrettyPrinter pp = new PrettyPrinter(pw);
    for (int i = 0; i < args.length; ++i) {
      try {
        FbLexer lexer = new FbLexer(new ANTLRFileStream(args[i]));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FbParser parser = new FbParser(tokens);
        Declaration d = parser.program();
        if (d != null) {
          d.eval(pp);
          pw.flush();
        }
      } catch (FileNotFoundException e) {
        Err.error("I couldn't read from " + args[i] + ". Nevermind.");
      }
    }
  }
}
