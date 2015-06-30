package freeboogie;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;

import freeboogie.ast.*;
import freeboogie.ast.utils.PrettyPrinter;
import freeboogie.dumpers.FlowGraphDumper;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import freeboogie.tc.SymbolTable;
import freeboogie.tc.TypeChecker;
import freeboogie.tc.UsageToDefMap;
import freeboogie.util.Closure;
import freeboogie.util.ClosureR;
import freeboogie.util.Err;

/**
 * Used to print information in the symbol table.
 * (Java is incredibly verbose for this kind of stuff.)
 *
 * @author rgrig 
 * @author reviewed by TODO
 * @param <U> the usage type
 * @param <D> the definition type
 */
class Printer<U extends Ast, D extends Ast> extends Closure<D> {
  private String name;
  private UsageToDefMap<U, D> map;
  private ClosureR<D, String> nameGetter;
  
  /**
   * Constructs a printer.
   * @param n the type of element that is printed
   * @param m the usage-def map
   * @param g a function that gets a user readable name from a definition
   */
  public Printer(String n, UsageToDefMap<U, D> m, ClosureR<D, String> g) {
    name = n; map = m; nameGetter = g;
  }

  @Override
  public void go(D t) {
    System.out.println(name + " " + nameGetter.go(t));
    System.out.println("  definition at " + t.loc());
    System.out.print("  usages at");
    for (U u : map.usages(t))
      System.out.print(" " + u.loc());
    System.out.println();
  }
}

/**
 * The main entry point of the application.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Main {
  
  private static Logger log = Logger.getLogger("freeboogie"); 
  
  /**
   * The main entry point of the application.
   * @param args the command line arguments
   */
  public static void main(String[] args) {
    try {
      FileHandler logh = new FileHandler("freeboogie.log");
      logh.setFormatter(new SimpleFormatter());
      log.addHandler(logh);
      log.setLevel(Level.ALL);
    } catch (IOException e) {
      Err.warning("Can't create log file. Nevermind.");
      log.setLevel(Level.OFF);
    }
    
    // parse command line arguments
    Options opt = new Options();
    opt.regBool("-pp", "pretty print");
    opt.regBool("-pst", "print symbol table");
    opt.regBool("-pfg", "print flow graphs");
    //opt.regBool("-ppi", "print implementations per procedure");
    
    opt.regInt("-v", 4, "verbosity level: 0, 1, 2, 3, 4");
    opt.parse(args);
    Err.setVerbosity(opt.intVal("-v"));
    
    // process files one by one
    PrintWriter pw = new PrintWriter(System.out);
    PrettyPrinter pp = new PrettyPrinter(pw);
    FlowGraphDumper fgd = new FlowGraphDumper();
    TypeChecker tc = new TypeChecker();
    for (String file : opt.otherArgs()) {
      try {
        FbLexer lexer = new FbLexer(new ANTLRFileStream(file));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FbParser parser = new FbParser(tokens);
        parser.fileName = file;
        Declaration d = parser.program();
        if (d == null) continue; // errors while parsing or empty file
        
        // pretty print?
        if (opt.boolVal("-pp")) {
          d.eval(pp);
          pw.flush();
        }
        
        // typecheck
        tc.process(d);
        
        // print symbol table?
        if (opt.boolVal("-pst")) {
          SymbolTable st = tc.getST();
          st.funcs.iterDef(new Printer<AtomFun, Function>("function", st.funcs,
            new ClosureR<Function, String>() {
              @Override public String go(Function p) {
                return p.getSig().getName();
              }}));
          st.ids.iterDef(new Printer<AtomId, Declaration>("identifier", st.ids,
            new ClosureR<Declaration, String>() {
              @Override public String go(Declaration p) {
                if (p instanceof VariableDecl) 
                  return ((VariableDecl)p).getName();
                else if (p instanceof ConstDecl)
                  return ((ConstDecl)p).getId();
                assert false;
                return null; // dumb compiler
              }}));
          st.procs.iterDef(new Printer<CallCmd, Procedure>("procedure", st.procs,
            new ClosureR<Procedure, String>() {
              @Override public String go(Procedure p) {
                return p.getSig().getName();
              }}));
          st.types.iterDef(new Printer<UserType, TypeDecl>("type", st.types,
            new ClosureR<TypeDecl, String>() {
              @Override public String go(TypeDecl p) {
                return p.getName();
            }}));
        }
        
        // print flow graph?
        if (opt.boolVal("-pfg")) fgd.process(d, tc);
        
        // print implementations per proc?
      } catch (FileNotFoundException e) {
        Err.error("I couldn't read from " + file + ". Nevermind.");
      } catch (Exception e) {
        Err.error("Unexpected error while processing " + file);
      }
    }
  }

}
