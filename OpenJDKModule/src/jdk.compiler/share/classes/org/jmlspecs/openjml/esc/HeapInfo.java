package org.jmlspecs.openjml.esc;

import java.util.Set;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Map;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import org.jmlspecs.openjml.JmlTree;


public class HeapInfo {
    
    public HeapInfo(int heapID, HeapInfo previousHeap) {
        this.heapID = heapID;
        this.previousHeaps.add(previousHeap);
    }
    
    public int heapID;
    
    JmlTree.JmlStatementHavoc havocStatement = null;
    
    JCTree.JCBlock methodAxiomsBlock;
    
    public Set<HeapInfo> previousHeaps = new HashSet<>();
    
    
    public Map<Symbol.MethodSymbol, MethodInfo> methodInfo = new HashMap<>();
    
    static public class MethodInfo {
        
    }
}
