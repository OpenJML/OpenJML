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
import org.jmlspecs.openjml.strongarm.Strongarm;
import org.jmlspecs.openjml.strongarm.gui.BasicBlockExecutionDebuggerConfigurationUtil;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log.WriterKind;

import jpaul.DataStructs.Pair;
import jpaul.Graphs.ArcBasedDiGraph;
import jpaul.Graphs.DiGraph;
import jpaul.Graphs.SCComponent;

public class ToReductionGraph extends JmlTreeAnalysis {
    
    private Collection<SpecBlockVertex> vertexes;    
    
    public ToReductionGraph(Context context) {
        super(context);
        
        vertexes = new ArrayList<SpecBlockVertex>();        
    }
    
    public void printGraph(Collection<Pair<SpecBlockVertex,SpecBlockVertex>> arcs, AdjacencyMatrix<SpecBlockVertex> weights){        
        if(BasicBlockExecutionDebuggerConfigurationUtil.debugBasicBlockExecution()){
            toDOTAnalysis(arcs, weights);
        }
    }
    
    private void toDOTAnalysis(Collection<Pair<SpecBlockVertex,SpecBlockVertex>> arcs, AdjacencyMatrix<SpecBlockVertex> weights){
        
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
        
        // edges
        for(Pair<SpecBlockVertex,SpecBlockVertex> p : arcs){        
            buff.append(String.format("%d -> %d [label=\"%d\", fontsize=\"9\", fontname=\"courier\", fontcolor=\"red\"];\n", p.left.hashCode(), p.right.hashCode(), weights.weight(p.left, p.right)));
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
            e.printStackTrace();
        }        
    }
        
    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase block) {

        if(block.clauses!=null && ((block.clauses.head instanceof JmlMethodClauseExpr) || (block.clauses.head instanceof JmlMethodClauseStoreRef))){
            
            vertexes.add(new SpecBlockVertex(block));
        }        

        super.visitJmlSpecificationCase(block);
    }
    
    private Collection<SpecBlockVertex> getVertexes(){
        return this.vertexes;
    }
    
    public Pair<DiGraph<SpecBlockVertex>,AdjacencyMatrix<SpecBlockVertex>> toDiGraph(Collection<SpecBlockVertex> vs){
        
        Collection<Pair<SpecBlockVertex,SpecBlockVertex>> edges = new LinkedHashSet<Pair<SpecBlockVertex,SpecBlockVertex>>();
        AdjacencyMatrix<SpecBlockVertex> matrix = new AdjacencyMatrix<SpecBlockVertex>();
        
        for(SpecBlockVertex v1 : vs){
            for(SpecBlockVertex v2 : vs){
                if(v1==v2){
                    continue;
                }
                
                int weight = v1.intersection(v2).size();
                
                if(weight > 0){
                    edges.add(new Pair<SpecBlockVertex,SpecBlockVertex>(v1, v2));
                    matrix.add(v1, v2, weight);
                }
                
            }
        }
        
        DiGraph<SpecBlockVertex> dg = new ArcBasedDiGraph<SpecBlockVertex>(edges);
        
        if(verbose){
            printGraph(edges, matrix);
        }
        
        return new Pair<DiGraph<SpecBlockVertex>,AdjacencyMatrix<SpecBlockVertex>>(dg,matrix);
    }
    

    
    
    public static DiGraph<SpecBlockVertex> analyze(JCTree tree) {

        ToReductionGraph analysis = new ToReductionGraph(Strongarm._context);
        analysis.doAnalysis(tree);
        
        // step 1 -- convert to a graph
        Pair<DiGraph<SpecBlockVertex>,AdjacencyMatrix<SpecBlockVertex>> pair = analysis.toDiGraph(analysis.getVertexes());
        
        DiGraph<SpecBlockVertex>         G = pair.left;
        AdjacencyMatrix<SpecBlockVertex> W = pair.right;

        // step 2 -- find connected components.
        Set<SCComponent<SpecBlockVertex>> scc = SCComponent.buildScc(G);
        
        
        
        return null;
        
    }


    private void doAnalysis(JCTree tree) {
        scan(tree);
        
    }
    
    
    
    
}
