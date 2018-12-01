package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.io.File;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.strongarm.Strongarm;
import org.jmlspecs.openjml.strongarm.TraceElement;
import org.jmlspecs.openjml.strongarm.gui.BasicBlockExecutionDebuggerConfigurationUtil;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log.WriterKind;

import jpaul.DataStructs.Pair;
import jpaul.Graphs.ArcBasedDiGraph;
import jpaul.Graphs.DiGraph;

public class ToDiGraphAnalysis extends JmlTreeAnalysis {
    
    private Collection<Pair<SpecBlockVertex,SpecBlockVertex>> arcs; 
    private Map<JmlSpecificationCase, SpecBlockVertex> vertexCache = new HashMap<JmlSpecificationCase, SpecBlockVertex>();
    
    
    public ToDiGraphAnalysis(Context context) {
        super(context);
        
        arcs = new LinkedHashSet<Pair<SpecBlockVertex,SpecBlockVertex>>();
    }

    
    public void printGraph(){        
        if(verbose){
            for(Pair<SpecBlockVertex,SpecBlockVertex> p : arcs){
                log.getWriter(WriterKind.NOTICE).println(String.format("%s ===> %s",p.left.toString(), p.right.toString()));
            }
                        
            if(BasicBlockExecutionDebuggerConfigurationUtil.debugBasicBlockExecution()){
                toDOTAnalysis();
            }
        
        }
        
        
    }
    
    private void toDOTAnalysis(){
        
        StringBuffer buff = new StringBuffer();
        
        buff.append("digraph BST {\n");
       
        // vertexes       
        for(Pair<SpecBlockVertex,SpecBlockVertex> p : arcs){
            
            String labelLeft = p.left.basedOn.toString();
            String labelRight = p.right.basedOn.toString();
            
            labelLeft  = labelLeft.replaceAll("\"", "\\\"");
            labelRight = labelRight.replaceAll("\"", "\\\"");
            
            labelLeft  = labelLeft.replaceAll("\\\\r", "r");
            labelRight = labelRight.replaceAll("\\\\r", "r");
            
            
            buff.append(String.format("%d [label=\"%s\", fontsize=\"9\", fontname=\"courier\"];\n",p.left.hashCode(), labelLeft));
            buff.append(String.format("%d [label=\"%s\", fontsize=\"9\", fontname=\"courier\"];\n",p.right.hashCode(), labelRight));
        }
        
        
        for(Pair<SpecBlockVertex,SpecBlockVertex> p : arcs){        
            buff.append(String.format("%d -> %d [label=\"%s\", fontsize=\"9\", fontname=\"courier\", fontcolor=\"red\"];\n", p.left.hashCode(), p.right.hashCode(), ""));
        }      
               
        buff.append("\n}");
        
        System.out.println(buff.toString());
        
        try {
            File f = File.createTempFile("sample", ".dot");
            File t = File.createTempFile("sample", ".pdf");
            
            PrintWriter out = new PrintWriter(f);

            out.write(buff.toString());
            out.close();
            
            Runtime r = Runtime.getRuntime();
            
            
            System.out.println(String.format("/usr/local/bin/dot -Tpdf %s -o %s", f.getAbsolutePath(), t.getAbsolutePath()));
            r.exec(String.format("/usr/local/bin/dot -Tpdf %s -o %s", f.getAbsolutePath(), t.getAbsolutePath())).waitFor();
            r.exec(String.format("/usr/bin/open %s", t.getAbsolutePath()));
           
            
        } catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        
    }
    
    public boolean findChild(SpecBlockVertex root, JmlSpecificationCase next){
        
        
        if(vertexCache.get(next)==null){
            vertexCache.put(next,  new SpecBlockVertex(next));
        }
        
        SpecBlockVertex vertex = vertexCache.get(next);
        
        // we can use this.
        if(next.clauses !=null && (next.clauses.head instanceof JmlMethodClauseExpr ||  next.clauses.head instanceof JmlMethodClauseStoreRef)){
            arcs.add(new Pair<SpecBlockVertex,SpecBlockVertex>(root, vertex));
            System.out.println("Adding Child Edge: " + next.toString());
            return true;
        }else if(next.clauses.head instanceof JmlMethodClauseGroup){
            JmlMethodClauseGroup group = (JmlMethodClauseGroup)next.clauses.head;
            return findChild(root,group);
        }
        return false;
    }
    
        
    
    
    
    public boolean findChild(SpecBlockVertex root, JmlMethodClauseGroup next){
               
        boolean found = false;
        
        for(List<JmlSpecificationCase> cases = next.cases; cases.nonEmpty(); cases = cases.tail){
            found = findChild(root, cases.head);
            if(found){
                break;
            }
        }
        
        
        return found;
        
    }
    
    
    
    
    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        
//        root = vertexCache.get(tree);
//        System.out.println("Spec Case: " + root.basedOn.toString());
//
//        
//        for(List<JmlSpecificationCase> cases = tree.cases; cases.nonEmpty(); cases = cases.tail){
//                findChild(root, cases.head);
//        } 
//        
        currentGroup.push(tree);
        
        super.visitJmlMethodClauseGroup(tree);
        
        JmlMethodClauseGroup group = currentGroup.pop();
        
        ArrayList<SpecBlockVertex> localRoots = blockRoots.get(group);
        
        while(localRoots!=null && localRoots.contains(roots.peek())){
            roots.pop();
        }
        
        
    }


    private Stack<SpecBlockVertex> roots = new Stack<SpecBlockVertex>();
    private Map<JmlMethodClauseGroup,ArrayList<SpecBlockVertex>> blockRoots = new HashMap<JmlMethodClauseGroup,ArrayList<SpecBlockVertex>>();
    private Stack<JmlMethodClauseGroup> currentGroup = new Stack<JmlMethodClauseGroup>();
    private JmlSpecificationCase lastCase = null;
    
    
    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase block) {

        
        if(vertexCache.containsKey(block)==false){
            vertexCache.put(block, new SpecBlockVertex(block));
        }
       
        SpecBlockVertex blockVertex = vertexCache.get(block);
        
        if(roots.size()==0){
            roots.push(blockVertex);
        }else{
            
            if(block.clauses!=null && ((block.clauses.head instanceof JmlMethodClauseExpr) || (block.clauses.head instanceof JmlMethodClauseStoreRef))){
                
                if(blockRoots.get(currentGroup.peek())!=null && blockRoots.get(currentGroup.peek()).contains(roots.peek())){
                    roots.pop();
                }
                
                SpecBlockVertex root = roots.peek();
                arcs.add(new Pair<SpecBlockVertex,SpecBlockVertex>(root, blockVertex));
                
                roots.push(blockVertex);
                
                
                if(blockRoots.get(currentGroup.peek())==null){
                    blockRoots.put(currentGroup.peek(), new ArrayList<SpecBlockVertex>());
                }
                
                blockRoots.get(currentGroup.peek()).add(blockVertex);
                
            }        
        }
        super.visitJmlSpecificationCase(block);
        
        
    }
    
    private boolean contains(SpecBlockVertex peek, JmlMethodClause head) {

        //TODO improve this by using reference equality
        if(head.toString().contains(peek.basedOn.toString())){
            return true;
        }
    
        return false;
    }


    public static DiGraph<SpecBlockVertex> analyze(JCTree tree) {

        ToDiGraphAnalysis analysis = new ToDiGraphAnalysis(Strongarm._context);
        analysis.doAnalysis(tree);

        analysis.printGraph();
        DiGraph<SpecBlockVertex> dg = new ArcBasedDiGraph<SpecBlockVertex>(analysis.arcs);

        return dg;
        
    }


    private void doAnalysis(JCTree tree) {
        scan(tree);
        
    }
    
    
    
    
}
