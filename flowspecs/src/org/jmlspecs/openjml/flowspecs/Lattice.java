package org.jmlspecs.openjml.flowspecs;

import java.util.Set;

public class Lattice<T> {

    AdjacencyMatrix<T> backingMatrix;

    public Lattice(AdjacencyMatrix<T> backingMatrix) {
        this.backingMatrix = backingMatrix;
    }

    public boolean isSubclass(T c1, T c2) {
        return backingMatrix.hasEdge(c1, c2);
    }
    
    public Set<T> getVertexes(){
        return backingMatrix.getVertexSet();
    }
    
    public T getTop(){
        Set<T> vertexes = backingMatrix.getVertexSet();
        
        T top = null;
        int topEdges = 0;

        for(T v : vertexes){
            if(top==null){
                top = v;
                topEdges = backingMatrix.getAdjacentVertexes(v).size();
                continue;
            }

            if(backingMatrix.getAdjacentVertexes(v).size() < topEdges){
                top = v;
                topEdges = backingMatrix.getAdjacentVertexes(v).size();
            }
        }

        return top;

    }
}
