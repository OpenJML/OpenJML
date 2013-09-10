package org.jmlspecs.openjml.flowspecs;

import java.util.*;

/**
 * This lass provides a adjacency matrix implementation. In this package it is used
 * to check that the provided typing hierarchy is valid.
 *
 * @author John L. Singleton <jsinglet@gmail.com>
 */
public class AdjacencyMatrix<T> {

    private int matrix[][];
    private Map<T, Integer> vertexIndex = new HashMap<T, Integer>();

    /**
     * Constructs a adjacency matrix of {@code vertexes.size() x vertexes.size()}. Note that
     * any objects in this collection must implement {@link #hashCode()} for this implementation
     * to work correctly.
     *
     * @param vertexes
     */
    public AdjacencyMatrix(List<T> vertexes) {
        this(vertexes.size());

        // build the vertex lookup table.
        for (int i = 0; i < vertexes.size(); i++) {
            this.vertexIndex.put(vertexes.get(i), i);
        }
    }

    public AdjacencyMatrix(int dims) {
        this(dims, dims);
    }

    public AdjacencyMatrix(int rows, int cols) {
        setMatrix(initMatrix(rows, cols));
    }

    public List<T> getVertexList() {
        return new ArrayList(vertexIndex.keySet());
    }

    public Set<T> getVertexSet() {
        return vertexIndex.keySet();
    }

    public List<T> getAdjacentVertexes(T vertex) {

        List<T> adjacent = new ArrayList<T>();

        // we have to copy this here.

        Set<T> vertexes = new HashSet(getVertexSet());
        vertexes.remove(vertex);

        for (T v : vertexes) {
            if (hasEdge(vertex, v)) {
                adjacent.add(v);
            }
        }

        return adjacent;
    }

    private void setMatrix(int matrix[][]) {
        this.matrix = matrix;
    }

    private int[][] getMatrix() {
        return this.matrix;
    }

    private int[][] initMatrix(int rows, int cols) {

        int newMatrix[][] = new int[rows][cols];

        for (int i = 0; i < newMatrix.length; i++) {
            Arrays.fill(newMatrix[i], 0);
        }

        return newMatrix;
    }


    private void indexCheck(T o1, T o2) {
        if (vertexIndex.keySet().contains(o1) == false || vertexIndex.keySet().contains(o2) == false) {
            throw new NoSuchElementException("Tried to access a vertex not present during initialization");
        }
    }

    public void addEdge(int from, int to) {
        getMatrix()[from][to] = 1;
    }


    /**
     * Adds an edge from {@code from} to {@code to}. Note that you should only use this method if
     * you initialized this instance of AdjacencyMatrix with {@link #AdjacencyMatrix(java.util.List)}.
     *
     * @param from
     * @param to
     */
    public void addEdge(T from, T to) {

        indexCheck(from, to);

        addEdge(vertexIndex.get(from), vertexIndex.get(to));
    }

    public boolean hasEdge(int from, int to) {
        return getMatrix()[from][to] == 1;
    }

    public boolean hasEdge(T from, T to) {

        indexCheck(from, to);

        return hasEdge(vertexIndex.get(from), vertexIndex.get(to));
    }


}
