package org.jmlspecs.openjml.esc;

import java.util.Set;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Map;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.tree.JCTree;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;


public class HeapInfo {
    
    public HeapInfo(int heapID, HeapInfo previousHeap, Name label) {
        this.heapID = heapID;
        this.label = label;
        if (previousHeap != null) this.previousHeaps.add(previousHeap);
    }
    
    public int heapID;
    
    /** The label just before the state change (in which the havocs are to be evaluated) */
    public Name label;
    
    public JCTree.JCExpression condition = null;
    
    // havocs might be: JCIdent, JCFieldAccess, JCArrayAccess, Loop specs, method call
    Object havocs = null;
    
    JCTree.JCBlock methodAxiomsBlock;
    
    public Set<HeapInfo> previousHeaps = new HashSet<>();
    
    
    public Map<Symbol.MethodSymbol, MethodInfo> methodInfo = new HashMap<>();
    
    static public class MethodInfo {
        
    }
    
    public String toString() {
        return ("HeapInfo[id=" + heapID + " [" + Utils.join(",",previousHeaps) +"]");
    }
}
