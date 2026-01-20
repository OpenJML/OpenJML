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


/** Instances of this class keep track of information about the state of the heap as program
 * execution progresses. The heap changes (and a new HeapInfo constructed) whenever an assignment
 * or method call changes anything in the existing heap. Allocating new objects is not considered
 * a heap change, nor is a new local declaration or a change to a local variable -- all because a 
 * (pure) function executed on the heap has the same value after any of these changes, whereas
 * assignment to an object field or array element does change the heap.
 * 
 * Heaps are distinguished by a 'heapID' which is a unique integer. The integers monotonically
 * increase, but that is just to keep them unique. The ordering is unimportant.
 * 
 * The heap is important for two reasons. First, the result of a (pure) function depends on the 
 * heap (except for no_state) function -- that is, the heap is an implicit parameter to the function.
 * We could model such functions in two ways: either by making the heap an explicit argument to the 
 * function, or giving the function an encoded name that contains the heap id. At this writing, 
 * OpenJML uses the latter.
 * 
 * The second reason is that a function executed on one heap differs from a function executed on an
 * earlier heap only if the function depends on heap locations that differ between the two heaps.
 * What a function depends on is given by the function's 'read' (or 'accessible') clause;
 * the difference between two successive heaps is given by the location set stored in the 'havocs'
 * field of the HeapInfo of the later heap, and so difference between two heaps is the accumulated
 * location set of the individual heap steps in between the two heaps.
 */
public class HeapInfo {
    
    public HeapInfo(int heapID, HeapInfo previousHeap, Name label) {
        this.heapID = heapID;
        this.label = label;
        if (previousHeap != null) this.previousHeaps.add(previousHeap);
    }
    
    /** A unique (within the translation of a given method) identifying ID for the heap */
    public int heapID;
    
    /** The label just before the state change (in which the havocs are to be evaluated), if any */
    public Name label;
    
    /** The precondition under which the location set in 'havocs' is well-defined */
    public JCTree.JCExpression condition = null;
    
    /** The differences between this heap and its predecessor */
    // havocs might be: JCIdent, JCFieldAccess, JCArrayAccess, Loop specs, method call
    public Object havocs = null;
    
    /** A reference to the block (which already exist in the translation) into which new function definitions
     * for this heap can be placed.
     */
    public JCTree.JCBlock methodAxiomsBlock;
    
    /** The collection of immediate predecessor heaps to this one. Usually one, but more than one for if, switch, and try
     * control flows.
     */
    public Set<HeapInfo> previousHeaps = new HashSet<>();
    
    /** Detail of the HeapInfo, just used for debugging */
    public String toString() { // FIXME - perhaps we just want the previous heap IDs?
        return ("HeapInfo[id=" + heapID + " [" + Utils.join(",",previousHeaps) +"]");
    }
}
