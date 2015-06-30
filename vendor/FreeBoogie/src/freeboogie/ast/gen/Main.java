package freeboogie.ast.gen;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

import freeboogie.util.Err;

/**
 * The entry point of the AST generator. The usage is:
 * <pre>java freeboogie.ast.gen.Main [-b defaultBase] grammar templates</pre>.
 * 
 * @author rgrig
 * @author reviewed by TODO
 */
public class Main {
  private static final Logger log = Logger.getLogger("freeboogie.ast.gen");
  
  private static String defaultBase = "Ast";

  /**
   * Reads in a grammar file and uses that information to expand the macros in a
   * template file.
   * 
   * @param args <code>args[0]</code> is the grammar file and
   *          <code>args[1..]</code> are template files
   */
  public static void main(String[] args) {
    if (args.length == 0) { 
      Err.fatal("Syntax: java freeboogie.ast.gen.Main" 
        + " [-b defaultBaseName] grammar templates", 1);
    }
    
    // Setup logging.
    try {
      Handler logh = new FileHandler("ast_gen.log");
      logh.setFormatter(new SimpleFormatter());
      log.addHandler(logh);
      log.setUseParentHandlers(false);
      log.setLevel(Level.WARNING); // for release
      //log.setLevel(Level.ALL); // for debug
    } catch (IOException e) {
      System.err.println("I can't create a log file. Nevermind.");
    }
    
    int arg_idx = 0;
    Grammar grammar = null;

    if (args[arg_idx].equals("-b")) {
      if (++arg_idx == args.length)
        Err.fatal("You must give a default base name after '-b'");
      defaultBase = args[arg_idx++];
    }

    // read the grammar
    try {
      AgParser agParser = new AgParser();
      agParser.setInputStream(new FileInputStream(args[arg_idx++]));
      agParser.parseAg();
      grammar = agParser.getGrammar();
      grammar.makeConsistent(defaultBase);
    } catch (IOException e) {
      Err.fatal("I can't read the abstract grammar.", 2);
    }

    for (; arg_idx < args.length; ++arg_idx) {
      // process a template
      try {
        TemplateParser template = new TemplateParser(args[arg_idx]);
        template.process(grammar);
      } catch (FileNotFoundException e) {
        Err.error("I can't find " + args[arg_idx] + ". I'll skip this template.");
      } catch (IOException e) {
        Err.error("I couldn't process (completely) template " + args[arg_idx]);
      }
    }
  }
}
