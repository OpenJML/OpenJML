package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.strongarm.InferenceAbortedException;
import org.jmlspecs.openjml.strongarm.JDKListUtils;
import org.jmlspecs.openjml.strongarm.Strongarm;
import org.jmlspecs.openjml.strongarm.gui.BasicBlockExecutionDebuggerConfigurationUtil;
import org.jmlspecs.openjml.strongarm.transforms.PropsInSubtree;
import org.jmlspecs.openjml.strongarm.tree.ContractComparator;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

import jpaul.DataStructs.Pair;
import jpaul.Graphs.ArcBasedDiGraph;
import jpaul.Graphs.DiGraph;
import jpaul.Graphs.ForwardNavigator;
import jpaul.Graphs.SCComponent;

public class ToReductionGraph extends JmlTreeAnalysis {
    
    private Collection<SpecBlockVertex> vertexes;    
    private Collection<Pair<SpecBlockVertex,SpecBlockVertex>> residualEdges;
    private Collection<SpecBlockVertex> residualVertexes;    
    private SpecBlockVertex residualRoot;
    
    private Collection<Pair<SpecBlockVertex,SpecBlockVertex>> lastEdges;
    private AdjacencyMatrix<SpecBlockVertex> lastMatrix;

    
    public ToReductionGraph(Context context) {
        super(context);
        
        vertexes = new ArrayList<SpecBlockVertex>();        
        residualEdges = new LinkedHashSet<Pair<SpecBlockVertex,SpecBlockVertex>>();
        residualVertexes = new HashSet<SpecBlockVertex>();
        residualRoot = new SpecBlockVertex(true);
        
    }
    
    public void printGraph(Collection<Pair<SpecBlockVertex,SpecBlockVertex>> arcs, AdjacencyMatrix<SpecBlockVertex> weights){        
        if(BasicBlockExecutionDebuggerConfigurationUtil.debugBasicBlockExecution()){
           //toDOTAnalysis(arcs, weights);
        }
    }

    private String toDOT(Collection<Pair<SpecBlockVertex,SpecBlockVertex>> arcs, AdjacencyMatrix<SpecBlockVertex> weights){

        StringBuffer buff = new StringBuffer();
        
        buff.append("digraph BST {\n");
       
        // vertexes       
        for(Pair<SpecBlockVertex,SpecBlockVertex> p : arcs){
            
            String labelLeft = p.left.toString();
            String labelRight = p.right.toString();
            
            labelLeft  = labelLeft.replaceAll("\"", "\\\"");
            labelRight = labelRight.replaceAll("\"", "\\\"");
            
            labelLeft  = labelLeft.replaceAll("\\\\r", "r");
            labelRight = labelRight.replaceAll("\\\\r", "r");
            
            
            buff.append(String.format("%d [label=\"%s\", fontsize=\"9\", fontname=\"courier\"];\n",p.left.hashCode(), labelLeft));
            buff.append(String.format("%d [label=\"%s\", fontsize=\"9\", fontname=\"courier\"];\n",p.right.hashCode(), labelRight));
        }
        
        // edges
        for(Pair<SpecBlockVertex,SpecBlockVertex> p : arcs){   
            if(weights!=null){
                buff.append(String.format("%d -> %d [label=\"%d\", fontsize=\"9\", fontname=\"courier\", fontcolor=\"red\"];\n", p.left.hashCode(), p.right.hashCode(), weights.weight(p.left, p.right)));
            }else{
                buff.append(String.format("%d -> %d [label=\"\", fontsize=\"9\", fontname=\"courier\", fontcolor=\"red\"];\n", p.left.hashCode(), p.right.hashCode()));                
            }
        }      
               
        buff.append("\n}");

        
        return buff.toString();
    }

    public void saveAsDot(Collection<Pair<SpecBlockVertex,SpecBlockVertex>> arcs, AdjacencyMatrix<SpecBlockVertex> weights) throws IOException{
        saveAsDot(arcs, weights, File.createTempFile("sample", ".dot"), true);
    }
    public void saveAsDot(Collection<Pair<SpecBlockVertex,SpecBlockVertex>> _arcs, AdjacencyMatrix<SpecBlockVertex> _weights, File f, boolean view){
        
        String dot = null;
        
        Collection<Pair<SpecBlockVertex,SpecBlockVertex>> arcs; 
        AdjacencyMatrix<SpecBlockVertex> weights;
        
        
        if(_arcs==null && _weights==null) {
            arcs = lastEdges;
            weights = lastMatrix;
        }else{
            arcs = _arcs;
            weights = _weights;
        }
        
        dot = toDOT(arcs, weights);
        
        try {
            File t = File.createTempFile("sample", ".pdf");
            
            PrintWriter out = new PrintWriter(f);

            out.write(dot);
            out.close();
            
            if(view) {            
                Runtime r = Runtime.getRuntime();
                
                r.exec(String.format("/usr/local/bin/dot -Tpdf %s -o %s", f.getAbsolutePath(), t.getAbsolutePath())).waitFor();
                r.exec(String.format("/usr/bin/open %s", t.getAbsolutePath()));
            }
            
        } catch (Exception e) {
            e.printStackTrace();
        }        
    }
        
    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase block) {

        if(block.clauses!=null && ((block.clauses.head instanceof JmlMethodClauseExpr) || (block.clauses.head instanceof JmlMethodClauseStoreRef))){
            
            // remove any trivial unsat cases
            SpecBlockVertex vertex = new SpecBlockVertex(block);
            if(vertex.contains("requires false;")
                    || vertex.contains("requires (false);")
                    || vertex.contains("ensures (false);")
                    || vertex.contains("ensures false;")
                    ){
                
            }else{
                vertexes.add(vertex);
            }
        }        

        super.visitJmlSpecificationCase(block);
    }
    
    public Collection<SpecBlockVertex> getVertexes(){
        return this.vertexes;
    }
    
    private SpecBlockVertex getResidualRoot(){
        return residualRoot;
    }
    
    private Collection<SpecBlockVertex> getResidualVertexes() {
        return residualVertexes;
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
        
        lastEdges = edges;
        lastMatrix = lastMatrix;
        
        if(verbose){
            printGraph(edges, matrix);
        }
        
        return new Pair<DiGraph<SpecBlockVertex>,AdjacencyMatrix<SpecBlockVertex>>(dg,matrix);
    }
    

    
    public void mergeSCC(DiGraph<SpecBlockVertex> G, AdjacencyMatrix<SpecBlockVertex> W, Set<SCComponent<SpecBlockVertex>> scc){

        Iterator<SCComponent<SpecBlockVertex>> it = scc.iterator();
        
        SpecBlockVertex maxLeft;
        SpecBlockVertex maxRight;

        
        // for each connected component, perform the merge procedure.
        while(it.hasNext())
        {
            SCComponent<SpecBlockVertex> component = it.next();
            
            // step 1 -- find the node with the largest weight if all weights are zero, remove 
            //           this edge and continue 
            maxLeft  = null;
            maxRight = null;
            int maxWeight = -1;
            
            for(SpecBlockVertex v1 : component.vertices()){
                for(SpecBlockVertex v2 : component.vertices()){
                    if(v1==v2){
                        continue;
                    }
                    
                    int weight = W.weight(v1, v2);
                    
                    if(maxWeight==-1){
                        maxLeft = v1;
                        maxRight = v2;
                        maxWeight = weight;
                    }else if(weight > maxWeight){
                        maxLeft = v1;
                        maxRight = v2;
                        maxWeight = weight;                        
                    }
                }
            }
            if(maxWeight == 0){
                it.remove();
                continue;
            }
            
            
            // step 2 -- merge the two vertexes with the highest weight
            Set<JmlMethodClause> intersection = maxLeft.intersection(maxRight);
            maxLeft.removeAll(intersection);
            maxRight.removeAll(intersection);
            
            // step 3 -- in the residual graph, create a conjunction node, with edges to the two merged nodes
            SpecBlockVertex root = new SpecBlockVertex(true);
            root.addAll(intersection);
            residualEdges.add(new Pair<SpecBlockVertex,SpecBlockVertex>(root, maxLeft));
            residualEdges.add(new Pair<SpecBlockVertex,SpecBlockVertex>(root, maxRight));
            
            // connect it to the root 
            residualEdges.add(new Pair<SpecBlockVertex,SpecBlockVertex>(residualRoot, root));
                        
            getResidualVertexes().add(maxLeft);
            getResidualVertexes().add(maxRight);
            
            // remove the merged nodes
            getVertexes().remove(maxLeft);
            getVertexes().remove(maxRight);
            
        }
        
    }
    
    
    public static DiGraph<SpecBlockVertex> analyze(JCTree tree) throws InferenceAbortedException {

        ToReductionGraph analysis = new ToReductionGraph(Strongarm._context);
        analysis.doAnalysis(tree);
        
        
        Set<SCComponent<SpecBlockVertex>> scc;
        
        
        do {

            Strongarm.dieIfNeeded();
            
            // step 1 -- convert to a graph
            Pair<DiGraph<SpecBlockVertex>,AdjacencyMatrix<SpecBlockVertex>> pair = analysis.toDiGraph(analysis.getVertexes());
            
            DiGraph<SpecBlockVertex>         G = pair.left;
            AdjacencyMatrix<SpecBlockVertex> W = pair.right;
    
            // step 2 -- find connected components.
            scc = SCComponent.buildScc(G);
            
            analysis.mergeSCC(G, W, scc);
                        
        }while(scc.size() > 0);        
        
        // step 3 -- at this point, we have a disjoint forest in the initial graph, add the remaining 
        //           disjoint nodes to the residual graph
        for(SpecBlockVertex v : analysis.getVertexes()){

            Strongarm.dieIfNeeded();
            
            if(analysis.getResidualVertexes().contains(v)==false){
                
                // it's not in the residual graph, so add it here
                analysis.residualEdges.add(new Pair<SpecBlockVertex, SpecBlockVertex>(analysis.getResidualRoot(), v));
                analysis.getResidualVertexes().add(v);
                
            }
        }
        
        if(verbose){
            analysis.printGraph(analysis.residualEdges, null);
        }
        
        DiGraph<SpecBlockVertex> dg = new ArcBasedDiGraph<SpecBlockVertex>(analysis.residualEdges);

        
        return dg;
        
    }

    public static List<JmlMethodClause> minimizeClauses(Collection<JmlMethodClause> clauses){
        return JDKListUtils.toList(clauses);
    }
    
    public static List<JmlMethodClause> processChild(ForwardNavigator<SpecBlockVertex> it , SpecBlockVertex child, List<JmlMethodClause> contract, JmlTreeUtils treeutils, JmlTree.Maker M, boolean minimizeExpressions){
        
        
        // base case -- nothing else to look at
        if(it.next(child)==null || it.next(child).size()==0){            
            return JDKListUtils.toList(child.clauses);

        }
        
        // the root node (and some other nodes) never has it's own clauses
        
        
        // the current vertex is an AND
        List<JmlMethodClause> rootClauses = null;
        if(child.isConjunction()){
            if(minimizeExpressions){
                rootClauses = minimizeClauses(child.getClauses());      
            }else{
                rootClauses = JDKListUtils.toList(child.getClauses());
            }
            
            if(rootClauses!=null){
                rootClauses = JDKListUtils.sort(rootClauses, new ContractComparator());
            }

        }
        
        
        // any children are or'd together 
        
        // step 1 - convert to specification cases
        Collection<JmlSpecificationCase> cases = it.next(child)
        .stream()
        .map(v -> processChild(it, v, contract,  treeutils,  M, minimizeExpressions))
        .filter(clauses -> clauses!=null && clauses.size() > 0)
        .map(v -> M.JmlSpecificationCase(null, false, null, null, v, null))
        .collect(Collectors.toList());
        
        // make sure we don't encounter the same cases twice.
        Set<String> stringCases = new HashSet<String>();
        
        cases = cases.stream().filter( c -> {
            if(stringCases.contains(c.toString())){
                return false;
            }
            
            stringCases.add(c.toString());
            return true;
        })
        .collect(Collectors.toList());
        
        // step 2 - convert to a list-based representation 
        List<JmlSpecificationCase> listCases = JDKListUtils.toList(cases);
        
        // step 3 - create the group
        JmlMethodClauseGroup group = M.JmlMethodClauseGroup(listCases);
        
        // step 4 - prepend the specification case from the root
        
        if(contract==null){
            if(rootClauses!=null){
                return rootClauses.append(group);
            }else{
                return List.of((JmlMethodClause)group);
            }
        }
        
        if(rootClauses!=null){            
            return JDKListUtils.appendAll(contract, rootClauses).append(group);
        }else{
            return contract.append(group);
        }
        
    }
    
    public static List<JmlMethodClause> toContract(JmlMethodDecl methodDecl, JCTree contract, DiGraph<SpecBlockVertex> G, JmlTreeUtils treeutils, JmlTree.Maker M, boolean minimizeExpressions)
    {
          
        ForwardNavigator<SpecBlockVertex> it = G.getForwardNavigator();
        
        // Each spec has one universal root
        Optional<SpecBlockVertex> root = G.getRoots()
                .stream()
                .filter(v -> v.isConjunction() && v.clauses.size()==0)
                .findFirst();
        
        // if there IS no root, we can't perform the transformation. 
        if(root.isPresent()){            
            // Convert to the contract form
            List<JmlMethodClause> newContract = processChild(it, root.get(), null, treeutils, M, minimizeExpressions);
            
            
            // now that we have the contract, make sure each rooted group has postconditions. 
            // if it doesn't eliminate it.
            List<JmlSpecificationCase> replacedCases = null;

            if(newContract !=null && newContract.head !=null && newContract.head instanceof JmlMethodClauseGroup){
            
                for(List<JmlSpecificationCase> cases = ((JmlMethodClauseGroup)newContract.head).cases; cases.nonEmpty(); cases = cases.tail)
                {
                    boolean  viable = PropsInSubtree.viable(cases.head);
                    
                    if(viable){
                        if(replacedCases == null){
                            replacedCases = List.of(cases.head);
                        }else{
                            replacedCases = replacedCases.append(cases.head);
                        }
                    }
                }
                
                ((JmlMethodClauseGroup)newContract.head).cases = replacedCases;
            }

            
            
            return newContract;
        }
        
        return null;
    }
    
    public void doAnalysis(JCTree tree) {
        scan(tree);
        
    }

}
