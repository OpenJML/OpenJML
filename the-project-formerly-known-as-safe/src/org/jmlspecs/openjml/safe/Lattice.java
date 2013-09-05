package org.jmlspecs.openjml.safe;

import java.util.Set;

public class Lattice<T> {

    AdjacencyMatrix<T> backingMatrix;

    public Lattice(AdjacencyMatrix<T> backingMatrix) {
        this.backingMatrix = backingMatrix;
    }

    public boolean isSubclass(T c1, T c2) {
        return backingMatrix.hasEdge(c1, c2);
    }

    public T getBottom(){
        Set<T> vertexes = backingMatrix.getVertexSet();

        T bottom = null;
        int bottomEdges = 0;

        for(T v : vertexes){
            if(bottom==null){
                bottom = v;
                bottomEdges = backingMatrix.getAdjacentVertexes(v).size();
                continue;
            }

            if(backingMatrix.getAdjacentVertexes(v).size() < bottomEdges){
                bottom = v;
                bottomEdges = backingMatrix.getAdjacentVertexes(v).size();
            }
        }

        return bottom;

    }
}
