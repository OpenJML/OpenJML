package freeboogie.tc;

import java.util.Map;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import freeboogie.util.Closure;
import freeboogie.util.Pair;

/**
 * Represents a graph of objects of type {@code N}. The implementation
 * uses adjacency lists and hash tables.
 *
 * @author rgrig 
 * @author reviewed by TODO
 * @param <N> the type of the graph node
 */
public class SimpleGraph<N> {
  private HashMap<N,HashSet<N>> parents;
  private HashMap<N,HashSet<N>> children;
  
  /** Construct an empty graph. */
  public SimpleGraph() {
    parents = new HashMap<N,HashSet<N>>();
    children = new HashMap<N,HashSet<N>>();
  }
  
  /**
   * Adds a node to the graph. Does nothing if the node is already
   * in the graph.
   * @param n the node to add to the graph
   */
  public void node(N n) {
    assert parents.size() == children.size();
    if (parents.containsKey(n)) return;
    parents.put(n, new HashSet<N>());
    children.put(n, new HashSet<N>());
  }
  
  /**
   * Adds an edge to the graph.
   * @param from the source
   * @param to the target
   */
  public void edge(N from, N to) {
    node(from); node(to);
    parents.get(to).add(from);
    children.get(from).add(to);
  }
  
  /**
   * Where can you go from {@code from}? The user shall not modify the
   * return value.
   * @param from the source, must be in this graph
   * @return the tips of the out-edges
   */
  public Set<N> to(N from) {
    return children.get(from);
  }
  
  /**
   * From where can you get to {@code to}? The user shall not modify the
   * return value.
   * @param to the target, must be in this graph
   * @return the sources of the in-edges
   */
  public Set<N> from(N to) {
    return parents.get(to);
  }
  
  /**
   * Execute {@code f} on all nodes, in a random order.
   * @param f the function to execute on all nodes
   */
  public void iterNode(Closure<N> f) {
    for (N n : parents.keySet()) f.go(n);
  }
  
  /**
   * Execute {@code f} on all edges, in a random order.
   * @param f the function to execute on all nodes
   */
  public void iterEdge(Closure<Pair<N,N>> f) {
    for (Map.Entry<N, HashSet<N>> a : parents.entrySet())
      for (N b : a.getValue()) f.go(new Pair<N,N>(b, a.getKey()));
  }
}
