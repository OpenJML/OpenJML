package org.jmlspecs.openjml.flowspecs;

import java.util.Iterator;
import java.util.Stack;

import com.sun.tools.javac.tree.JCTree.JCExpression;

//TODO these types need to be cleaned up.
public class FlowStack {

    private Stack<FlowEscalation> stack = new Stack<FlowEscalation>();
    
    // TODO refactor this to seperate the checker from the visitor
    private JmlFlowSpecs flow;

    public FlowStack(JmlFlowSpecs flow) {
        this.flow = flow;
    }

    public FlowEscalation exit() {
        return stack.pop();
    }

    public boolean isEmpty(){
        return stack.isEmpty();
    }
    
    public SecurityType enter(JCExpression e) {

        SecurityType thisType = flow.attribExpr(e, flow.env);

        stack.push(new FlowEscalation(thisType, e));

        return thisType;
    }

    /**
     * Computes the upper bound of a flow within a call stack of flows.
     * 
     * @return the bounding SecurityType
     */
    public SecurityType currentTypeBoundary() {

        Iterator<FlowEscalation> it = stack.iterator();

        SecurityType lastType = null;

        while (it.hasNext()) {

            SecurityType thisType = it.next().getType();

            if (lastType == null) {
                lastType = thisType;
            }

            lastType = flow.upperBound(thisType, lastType);
        }
        return lastType;
    }

}
