package org.jmlspecs.openjml.flowspecs;

import java.util.Iterator;
import java.util.Stack;

import com.sun.tools.javac.tree.JCTree.JCExpression;


//TODO these types need to be cleaned up.
public class FlowStack<T extends SecurityType> extends Stack<T> {

    //TODO refactor this to seperate the checker from the visitor
    private JmlFlowSpecs flow;
    
    public FlowStack(JmlFlowSpecs flow){
        this.flow = flow;
    }
    
    public SecurityType exit(){
        return this.pop();
    }
    
    public SecurityType enter(JCExpression...e){ 
    
        SecurityType lastType = null;
        
        for(JCExpression currentExpression : e){
           
            T thisType = (T) flow.attribExpr(currentExpression, flow.env);
            
            if(lastType==null){
                lastType = thisType;
            }
            
           lastType = flow.upperBound(thisType, lastType);
        }
        
        this.push((T) lastType);
        
        return lastType;
    }
    
    /**
     * Computes the upper bound of a flow within a call stack of flows.
     *  
     * @return the bounding SecurityType
     */
    public SecurityType currentTypeBoundary(){
        
        Iterator<T> it = this.iterator();
        
        SecurityType lastType = null;
        
        while(it.hasNext()){
            
            T thisType = it.next();
            
            if(lastType==null){
                lastType = thisType;
            }
            
            lastType = flow.upperBound(thisType, lastType);
        }

        return lastType;
        
    }
    
    
    
    
    
}
