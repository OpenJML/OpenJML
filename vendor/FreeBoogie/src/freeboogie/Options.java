package freeboogie;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import freeboogie.util.Err;

/**
 * Parses options. Right now it supports simple boolean and integer
 * options. It prints a list of registered options when it sees "-help". 
 * 
 * In the future it might support arbitrary strings and perhaps
 * keep track of dependencies between options.
 * 
 * TODO: Introduce the notion of legal values for integer options
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Options {
  
  private class Opt<T> {
    /** Make a structure
     * @param n name
     * @param h help
     * @param d default
     */
    public Opt(String n, String h, T d) { name = n; help = h; def = d; }
    /** name */ public String name;
    /** help */ public String help;
    /** default */ public T def;
  }
  
  // the following two are used to make the help message
  private ArrayList<Opt<Boolean>> boolOpt; // boolean options
  private ArrayList<Opt<Integer>> intOpt; // integer options
  
  private HashMap<String, Boolean> boolVal; // boolean values
  private HashMap<String, Integer> intVal; // integer values
  private LinkedList<String> otherVal; // things that don't look like options

  /** Constructs an object. Nothing fancy. */
  public Options() {
    boolOpt = new ArrayList<Opt<Boolean>>();
    intOpt = new ArrayList<Opt<Integer>>();
    boolVal = new HashMap<String, Boolean>();
    intVal = new HashMap<String, Integer>();
    otherVal = new LinkedList<String>();
  }
  
  /**
   * Register {@code name} as a boolean option. The default value is always
   * {@code false} and becomes {@code true} if {@code name} appears in the
   * arguments.
   * @param name the boolean option
   * @param help help string
   */
  public void regBool(String name, String help) {
    boolOpt.add(new Opt<Boolean>(name, help, false));
    boolVal.put(name, false);
  }
  
  /**
   * Register {@code name} as an integer option.
   * @param name the integer option
   * @param def the default value if none is specified by the user
   * @param help help string
   */
  public void regInt(String name, int def, String help) {
    intOpt.add(new Opt<Integer>(name, help, def));
    intVal.put(name, def);
  }

  /**
   * Query the value of the boolean option {@code name}.
   * @param name the boolean option to query
   * @return the value of {@code name}
   */
  public boolean boolVal(String name) {
    return boolVal.get(name);
  }
  
  /**
   * Query the value of the integer option {@code name}.
   * @param name the integer option to query
   * @return the value of {@code name}
   */
  public int intVal(String name) {
    return intVal.get(name);
  }
  
  /**
   * Query what non-option arguments appeared on the command line.
   * @return the non-option arguments (usually file names)
   */
  public List<String> otherArgs() {
    return otherVal;
  }
  
  private void printHelp() {
    // TODO: better formatting
    for (Opt<Boolean> o : boolOpt) {
      System.out.print(o.name + "\t");
      System.out.print(o.help + " ");
      System.out.println("(default: " + o.def + ")");
    }
    for (Opt<Integer> o : intOpt) {
      System.out.print(o.name + "\t");
      System.out.print(o.help + " ");
      System.out.println("(default: " + o.def + ")");
    }
  }
  
  /**
   * Parse {@code args}.
   * @param args the arguments to parse
   */
  public void parse(String[] args) {
    for (int i = 0; i < args.length; ++i) {
      if (args[i].equals("-help")) printHelp();
      else if (boolVal.containsKey(args[i])) {
        boolVal.put(args[i], true);
      } else if (intVal.containsKey(args[i])) {
        if (i + 1 >= args.length)
          Err.fatal("Option " + args[i] + " should be followed by a number.");
        try {
          intVal.put(args[i], Integer.parseInt(args[i+1]));
        } catch (NumberFormatException fe) {
          Err.fatal("Option " + args[i] + " should be followed by a number.");
        }
        ++i;
      } else {
        otherVal.add(args[i]); 
      }
    }
  }
}
