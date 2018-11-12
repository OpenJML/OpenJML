package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.esc.BasicBlocker2.VarMap;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.utils.Pair;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import org.jmlspecs.openjml.esc.BasicBlockerParent;


public class SubstitutionCache {

    private HashMap<VarSymbol, ArrayList<Pair<String,JCTree>>> ds = new HashMap<VarSymbol, ArrayList<Pair<String,JCTree>>>();
    private Map<BasicBlock,VarMap> blockmaps;    
    private JmlTreeUtils treeutils;
    private HashMap<VarSymbol,JCIdent> _cache = new HashMap<VarSymbol,JCIdent>();
    
    
    public SubstitutionCache(Map<BasicBlock,VarMap> blockmaps, JmlTreeUtils treeutils){
        this.blockmaps = blockmaps;
        this.treeutils = treeutils;
    }
    
    // the goal here is to always match a given ident name 
    public VarSymbol getPremapIdent(JCTree i, BasicBlock b){

        if(i instanceof JCIdent){
            JCIdent id = (JCIdent)i;
            return (VarSymbol)id.sym;
        }else if(i instanceof JCFieldAccess){
            JCFieldAccess fa = (JCFieldAccess)i;
            return (VarSymbol)fa.sym;
        }
        
        return null;
        
//          //if(_cache.get(i))
//
//        
//        VarMap blockMap  = blockmaps.get(b);
//        
//        //blockMap.getName(i);
//        
//        
//        Set<VarSymbol> syms2 = blockMap.keySet();
//blockMap.get
//        for(VarSymbol s : syms2){
//            JCIdent with    = treeutils.makeIdent(0, s);
//        }
//    
//        
//        return null;

//        
//        return subs;
    }
    
    public ArrayList<JCTree> getSubstitutionsAlongPathForIdent(JCIdent ident, ArrayList<BasicBlock> path)
    {
        Set<String> s = new HashSet<String>();
        
        for(BasicBlock b : path){
            s.add(b.id().toString());
        }
        
       return getSubstitutionsAlongPathForIdent(ident, s);
    }
    
    
    public ArrayList<JCTree> getSubstitutionsAlongPathForIdent(VarSymbol premap, Set<String> path)
    {
        
        // first, get the subset for this ident
        ArrayList<Pair<String,JCTree>> possibleMatches = ds.get(premap);
        
        ArrayList<JCTree> subs = new ArrayList<JCTree>();
        
        if(possibleMatches!=null){        
            // get possible substitutions along this path
            Iterator<Pair<String,JCTree>> it = possibleMatches.iterator();
            
            try {
            while(it.hasNext()){
                Pair<String,JCTree> p = it.next();
                
                if(path.contains(p.fst)){
                    subs.add(p.snd);
                }
                
            }
            // this happens under stress -- not sure why. 
            // TODO - refactor this. 
            }catch(ConcurrentModificationException e){
                return subs;
            }
        
        }
        
        return subs;
    }
    
    public ArrayList<JCTree> getSubstitutionsAlongPathForIdent(JCIdent ident, Set<String> path)
    {
        VarSymbol premap =  (VarSymbol)ident.sym;
        
        return getSubstitutionsAlongPathForIdent(premap, path);
    }
    
    public ArrayList<JCTree> getSubstitutionsAlongPath(JCIdent ident, ArrayList<BasicBlock> path)
    {
        
        return getSubstitutionsAlongPath((VarSymbol)ident.sym, path);
    }
    
    public ArrayList<JCTree> getSubstitutionsAlongPath(VarSymbol premap, ArrayList<BasicBlock> path)
    {
        Set<String> sPath = new HashSet<String>();
        
        for(BasicBlock b : path){
            sPath.add(b.id().toString());
        }
        
        return getSubstitutionsAlongPathForIdent(premap, sPath);
    }
    
    
    public void addSubstitutionAtBlock(JCTree premapIdent, JCTree sub, BasicBlock block){
        
        VarSymbol premap =  getPremapIdent(premapIdent, block);
       
        if(premap==null){
            return;
        }
        
        
        if(ds.get(premap)==null){
            ds.put(premap, new ArrayList<Pair<String, JCTree>>());
        }

        if(block==null || block.id() == null){
            return;
        }
        
        ds.get(premap).add(new Pair<String, JCTree>(block.id().toString(), sub));
        
    }
    
    public void addSubstitutionAtBlock(VarSymbol premap, JCTree sub, BasicBlock block){
        
        if(premap==null){
            return;
        }

        
        if(ds.get(premap)==null){
            ds.put(premap, new ArrayList<Pair<String, JCTree>>());
        }
        
        ds.get(premap).add(new Pair<String, JCTree>(block.id().toString(), sub));
        
    }
    
    
    public void addSubstitutionAtBlock(JCStatement stmt, BasicBlock block){
        
        if(stmt instanceof JmlStatementExpr){
            
            JmlStatementExpr expr = (JmlStatementExpr)stmt;
            
            if(expr.expression instanceof JCBinary){
                JCBinary e = (JCBinary)expr.expression;
                addSubstitutionAtBlock(e.lhs, e, block);
            }
            
            else if (expr.expression instanceof JmlBBFieldAssignment){
                JmlBBFieldAssignment e = (JmlBBFieldAssignment)expr.expression;
                addSubstitutionAtBlock((JCIdent)e.args.head, e, block);
            }
            
            
            else if(expr.label!=Label.CASECONDITION){
                //throw new UnsupportedOperationException("Didn't expect tree type of: " + stmt.getClass());
            }
            
        }else if(stmt instanceof JmlVariableDecl){
        
           JmlVariableDecl d = (JmlVariableDecl)stmt;
           
           if(d.init == null && d.ident==null){ // we don't learn anything. 
               return;
           }
           
           addSubstitutionAtBlock(d.ident, d.init, block);
           

        } 
        
    }
    
    public String toString(){
        
        StringBuffer sb = new StringBuffer();
        
        sb.append("====Substitution Cache====\n");
        sb.append(String.format("%20s %140s %30s\n", "VarSym", "Substitution", "@ Block"));
        
        Set<VarSymbol> keys = ds.keySet();
        try {
            for(VarSymbol s : keys){
                List<Pair<String,JCTree>> v = ds.get(s);
                
                for(Pair<String,JCTree> vv : v){
                    sb.append(String.format("%20s %140s %30s\n", s.toString(), vv.snd.toString(), vv.fst));
                }
                sb.append("=======================================================================================================================================================\n");
            }
        }catch(Exception e){
            sb.append("Encountered an error while processing the substitution cache. Table may be incomplete.");
        }
        
        
        return sb.toString();
    }
    
   
}
