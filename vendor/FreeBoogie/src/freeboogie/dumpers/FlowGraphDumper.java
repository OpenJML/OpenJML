package freeboogie.dumpers;

import freeboogie.ast.*;
import freeboogie.tc.SimpleGraph;
import freeboogie.tc.TypeChecker;
import freeboogie.util.Closure;
import freeboogie.util.Pair;

/**
 * Dumps flow graphs for all implementations in dot format.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // unused parameters
public class FlowGraphDumper extends Transformer {
  private TypeChecker tc; // used to get the flowgraphs for implementations
  
  /**
   * Print to standard output the flowgraphs for the implementations in
   * {@code ast}, by using the {@code t} to get the flowgraphs.
   * @param ast
   * @param t
   */
  public void process(Declaration ast, TypeChecker t) {
    tc = t;
    ast.eval(this);
  }

  @Override
  public void see(Implementation implementation, Signature sig, Body body, Declaration tail) {
    SimpleGraph<Block> fg = tc.getFlowGraph(implementation);
    System.out.println("digraph \"" + implementation.getSig().getName() + "@" + implementation.loc() + "\" {");
    if (body.getBlocks() != null)
      System.out.println("  " + body.getBlocks().getName() + " [style=bold];");
    fg.iterNode(new Closure<Block>() {
      @Override public void go(Block t) {
        System.out.println("  " + t.getName() + " [shape=box];");
      }});
    fg.iterEdge(new Closure<Pair<Block,Block>>() {
      @Override public void go(Pair<Block,Block> t) {
        System.out.println("  " + t.first.getName() + " -> " + t.second.getName() + ";");
      }});
    System.out.println("}");
    if (tail != null) tail.eval(this);
  }
}
