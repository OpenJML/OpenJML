package freeboogie.util;

/**
 * Provides basic facilities for reporting errors.
 * 
 * TODO: make the error reporting functions format the result;
 *       at least, they should make sure no more than 70 characters 
 *       per line are used
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Err {
  
  /**
   * The possible verbosity levels. 
   */
  public enum Level {
    /** No output. */
    BATCH,
    
    /** Report only errors that make me stop. */
    FATAL,
    
    /** Report all problems. */
    ERROR,
    
    /** Report a minor problem. */
    WARNING,
    
    /** Give hints of what should be done to fix the problem. */
    HELP
  }
  
  // TODO: can this be nicer?
  private static final Level[] levels = {
    Level.BATCH, Level.FATAL, Level.ERROR, Level.WARNING, Level.HELP
  };
  
  /** The current verbosity level. */ 
  public static Level verboseLevel = Level.HELP;
  
  /**
   * Set the verbosity using a number.
   * @param v the numeric verbosity level
   */
  public static void setVerbosity(int v) {
    if (v < 0 || v >= levels.length)
      fatal("Incorrect verbosity level.");
    verboseLevel = levels[v];
  }
  
  /**
   * Displays a help message.
   * @param h the help message
   */
  public static void help(String h) {
    if (verboseLevel.compareTo(Level.HELP) >= 0)
      System.err.println(h);
  }
  
  /**
   * Displays a warning.
   * @param w the warning
   */
  public static void warning(String w) {
    if (verboseLevel.compareTo(Level.WARNING) >= 0)
      System.err.println(w);
  }
  
  /**
   * Displays an error message.
   * @param e the error message
   */
  public static void error(String e) {
    if (verboseLevel.compareTo(Level.ERROR) >= 0)
      System.err.println(e);
  }
  
  /**
   * Displays a fatal error end exits with code 1.
   * @param m the error message
   */
  public static void fatal(String m) {
    fatal(m, 1);
  }

  /**
   * Displays a fatal error and exits with the specified code.
   * @param m the error message
   * @param code the exit code
   */
  public static void fatal(String m, int code) {
    System.err.println(m);
    System.exit(code);
  }
  
  /** Aborts execution. */
  public static void notImplemented() {
    new Exception().printStackTrace();
    System.exit(255);
  }
}
