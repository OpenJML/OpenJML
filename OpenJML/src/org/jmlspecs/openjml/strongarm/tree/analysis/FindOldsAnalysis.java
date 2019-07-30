package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.strongarm.Strongarm;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

public class FindOldsAnalysis extends JmlTreeAnalysis {

    private Set<String> idents = new HashSet<>();
    
    public FindOldsAnalysis(Context context) {
        super(context);
    }
    
    @Override
    public void scan(JCTree node) {
        super.scan(node);
    }

    
    @Override
    public void visitIdent(JCIdent tree){
        if(tree==null) return;
        if(tree.toString().equals(Strings.THIS)) return;
        
        idents.add(tree.toString());
    }
    
    @Override
    public void visitSelect(JCFieldAccess tree) {        
        idents.add(tree.toString());
        scan(tree.selected);
    }
    
    
    private void handleField(JCFieldAccess access){

        if(access.selected instanceof JCIdent){
            JCIdent selected = (JCIdent)access.selected;            
        }
        
        if(access.selected instanceof JCFieldAccess){
            handleField((JCFieldAccess)access.selected);
        }
    }
    
    class Disjoints {

        
    
    }
    
    public static int indexOfSubstring(ArrayList<String> ids, String s){
        for(int i=0; i<ids.size(); i++){
            if(ids.get(i).startsWith(s)){
                return i;
            }
        }
        
        return -1;
    }
   

    public static Set<String> analyze(JCTree tree, Context ctx){
        
        FindOldsAnalysis analysis = new FindOldsAnalysis(ctx);
                
        analysis.scan(tree);
        
        Set<String> possibleIdents = analysis.idents;
        
        ArrayList<String> idents = new ArrayList<String>(possibleIdents);
        
        // first, sort from longest to shortest
        Collections.sort(idents, (String o1, String o2) -> new Integer(o2.length()).compareTo(o1.length()));
        
        ArrayList<String> reps = new ArrayList<String>();
        ArrayList<ArrayList<String>> sets = new ArrayList<ArrayList<String>>();
        
        for(String ident : idents){
            // first, try to find something in rep that this string is a 
            // substring of
            int idx = indexOfSubstring(reps, ident);
            
            // if it's not found, add it to reps. 
            if(idx==-1){
                int next = reps.size();
                reps.add(ident);
                //
                sets.add(new ArrayList<String>());
                sets.get(next).add(ident);
            }else{
                sets.get(idx).add(ident);                
            }            
        }
        
        // now for each set, larger than 1, get the last element.
        Set<String> olds = new HashSet<String>();
        
        for(ArrayList<String> set : sets){
            if(set.size() > 1){
                olds.add(set.get(set.size()-1));
            }
        }
        
        return olds;
        
    }
}
