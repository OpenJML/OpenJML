package freeboogie.backend;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.logging.Logger;

/**
 * Used to interact with Simplify.
 * 
 * TODO keep track whether the prover is alive or is known to be dead
 * TODO Abstract the prompt-based interaction in another class
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class SimplifyProver implements Prover {
  
  private static final Logger log = Logger.getLogger("freeboogie.backend");
  
  private Process prover;
  private List<String> cmd;
  
  private BufferedReader in;
  private PrintStream out;
  
  // a |marker| is used to mark the beginning of an assumption frame
  private Deque<Term> assumptions;
  private Term marker; 
  
  private SmtTermBuilder builder;
  
  /**
   * Creates a new {@code SimplifyProver}. It also tries to start the prover. 
   * @param cmd the command to use to start the prover
   * @throws ProverException if the prover cannot be started
   */
  public SimplifyProver(String[] cmd) throws ProverException {
    this.cmd = Arrays.asList(cmd);
    assumptions = new ArrayDeque<Term>();
    marker = new Term(null);
    assumptions.add(marker);
    restartProver();
    
    // TODO some of this stuff is probably common to multiple provers
    //      so move it into the builder
    builder = new SmtTermBuilder();
    builder.def("not", new Sort[]{Sort.PRED}, Sort.PRED);
    builder.def("and", Sort.PRED, Sort.PRED);
    builder.def("or", Sort.PRED, Sort.PRED);
    builder.def("implies", new Sort[]{Sort.PRED, Sort.PRED}, Sort.PRED);
    builder.def("iff", new Sort[]{Sort.PRED, Sort.PRED}, Sort.PRED);
    builder.def("var_int", String.class, Sort.VARINT);
    builder.def("var_bool", String.class, Sort.VARBOOL);
    builder.def("var_pred", String.class, Sort.PRED);
    builder.def("const_int", BigInteger.class, Sort.INT);
    builder.def("const_bool", Boolean.class, Sort.BOOL);
    builder.def("forall_int", new Sort[]{Sort.VARINT, Sort.PRED}, Sort.PRED);
    builder.def("<", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def("<=", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def(">", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def(">=", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def("eq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def("eq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.PRED);
    // TODO register all stuff with the builder
    // TODO should I leave the user (vcgen) responsible for adding the
    //      excluded middle for boolean variables? i think that's in the
    //      escjava background predicate anyway
    builder.pushDef(); // mark the end of the prover builtin definitions
  }
  
  // TODO This is quite incomplete now
  private void printTerm(Term t, StringBuilder sb) {
    SmtTerm st = (SmtTerm)t;
    if (st.id.startsWith("var")) { 
      sb.append((String)st.data);
    } else if (st.id.startsWith("forall")) {
      sb.append("(FORALL (");
      printTerm(st.children[0], sb);
      sb.append(") ");
      printTerm(st.children[1], sb);
      sb.append(")");
    } else if (st.id.equals("const_int")) {
      sb.append(st.data);
    } else if (st.id.equals("const_bool")) {
      if ((Boolean)st.data)
        sb.append("|true|");
      else
        sb.append("|false|");
    } else if (st.id.startsWith("eq")) {
      sb.append("(EQ ");
      printTerm(st.children[0], sb);
      sb.append(" ");
      printTerm(st.children[1], sb);
      sb.append(")");
    } else {
      sb.append("(");
      sb.append(st.id.toUpperCase());
      for (Term c : st.children) {
        sb.append(" ");
        printTerm(c, sb);
      }
      sb.append(")");
    }
  }
  
  private void sendTerm(Term t) {
    StringBuilder sb = new StringBuilder();
    printTerm(t, sb);
    log.info("backend> " + sb);
    out.print(sb);
  }
  
  private void sendAssume(Term t) {
    out.print("(BG_PUSH ");
    sendTerm(t);
    out.print(")\n");
    out.flush();
  }
  
  private void checkIfDead() throws ProverException {
    try {
      int ev = prover.exitValue();
      throw new ProverException("Prover exit code: " + ev);
    } catch (IllegalThreadStateException e) {
      // the prover is still alive
    }
  }
  
  private void waitPrompt() throws ProverException {
    try {
      int c;
      boolean firstonline = true;
      while ((c = in.read()) != -1) {
        if (firstonline && c == '>') return;
        firstonline = c == '\n' || c == '\r';
      }
    } catch (IOException e) {
      throw new ProverException("Can't read what Simplify says.");
    }
  }
  
  /* @see freeboogie.backend.Prover#assume(freeboogie.backend.Term) */
  public void assume(Term t) throws ProverException {
    sendAssume(t);
    assumptions.add(t);
    checkIfDead();
  }

  /* @see freeboogie.backend.Prover#getBuilder() */
  public TermBuilder getBuilder() {
    return builder;
  }

  /* @see freeboogie.backend.Prover#getDetailedAnswer() */
  public ProverAnswer getDetailedAnswer() {
    // TODO Auto-generated method stub
    return null;
  }

  /* @see freeboogie.backend.Prover#isSat(freeboogie.backend.Term) */
  public boolean isSat(Term t) throws ProverException {
    waitPrompt();
    log.fine("Got prompt, sending query.");
    sendTerm(builder.mk("not", t));
    out.println();
    out.flush();
    
    // wait for prompt or for Valid, Invalid, Unknown
    try {
      StringBuilder sb = new StringBuilder();
      while (true) {
        int c = in.read();
        if (c == '\n' || c == '\r') {
          String line = sb.toString();
          log.info("simplify> " + line);
          if (line.contains("Valid")) return false;
          if (line.contains("Invalid") || line.contains("Unknown"))
            return true;
          sb.setLength(0);
          continue;
        }
        if (c == '>' && sb.length() == 0)
          throw new ProverException("The prover seems a bit confused.");
        if (c == -1)
          throw new ProverException("Prover died.");
        sb.append((char)c);
      }
    } catch (IOException e) {
      throw new ProverException("Failed to read prover answer.");
    }
  }

  /* @see freeboogie.backend.Prover#pop() */
  public void pop() throws ProverException {
    while (assumptions.getLast() != marker) retract();
    assumptions.removeLast();
  }

  /* @see freeboogie.backend.Prover#push() */
  public void push() {
    assumptions.push(marker);
  }

  /* @see freeboogie.backend.Prover#restartProver() */
  public void restartProver() throws ProverException {
    log.fine("exec: " + cmd);
    ProcessBuilder pb = new ProcessBuilder(cmd);
    try {
      prover = pb.start();
      in = new BufferedReader(new InputStreamReader(prover.getInputStream()));
      out = new PrintStream(prover.getOutputStream());
      out.println("(PROMPT_ON)"); // make sure prompt is ON
      for (Term t : assumptions) if (t != marker) sendAssume(t);
      out.flush();
    } catch (Exception e) {
      throw new ProverException("Cannot start prover." + cmd);
    }
  }

  /* @see freeboogie.backend.Prover#retract() */
  public void retract() {
    Term last;
    do last = assumptions.getLast(); while (last == marker);
    out.print("(BG_POP)");
    out.flush();
  }
  
  /**
   * Runs some basic tests.
   * @param args the command line arguments
   * @throws Exception thrown if something goes wrong
   */
  public static void main(String[] args) throws Exception {
    Prover p = new SimplifyProver(args);
    TermBuilder b = p.getBuilder();
    Term x = b.mk("var_pred", "x");
    Term y = b.mk("var_pred", "y");
    Term q = b.mk("not", b.mk("iff", 
      b.mk("iff", b.mk("and", x, y), b.mk("or", x, y)),
      b.mk("iff", x, y)
    ));
    System.out.println("false = " + p.isSat(q));
  }
}
