package org.jmlspecs.openjml.sa;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

public class MethodDependencies extends JmlTreeScanner {
    
    
    protected Log log;
    protected Utils utils;
    protected Context context;
    
    public Map<Symbol.MethodSymbol, java.util.Set<Symbol.MethodSymbol>> deps =
            new HashMap<>();
    
    public Map<Symbol.MethodSymbol,Integer> order = new HashMap<>();
    
    public Set<Symbol.MethodSymbol> skipped = new HashSet<>();
    
    Symbol.MethodSymbol currentMethod;
    
    /** Creates a new copier, whose new nodes are generated from the given factory*/
    public MethodDependencies(Context context) {
        super();
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.context = context;
    }
    
    public static String toString(Symbol.MethodSymbol m) {
        return m.owner.toString()+ "." + m.toString();
    }
    
    public static void find(Context context, Queue<Env<AttrContext>> envs) {
        MethodDependencies dep = new MethodDependencies(context);
        for (Env<AttrContext> env: envs) dep.scan(env.tree);
        for (Symbol.MethodSymbol msym: dep.deps.keySet()) dep.setOrder(msym);
        java.util.List<Symbol.MethodSymbol> list = new ArrayList<>(dep.deps.keySet());
        Collections.sort(list, (s1,s2)->dep.order.get(s1).compareTo(dep.order.get(s2)));
        Set<Symbol.MethodSymbol> sk = new HashSet<>(dep.skipped);
        System.out.println("----------- All methods that are skipped or depend on a skipped method");
        for (Symbol.MethodSymbol m: list) {
            boolean bm = dep.skipped.contains(m);
            if (!sk.contains(m)) {
                boolean any = false;
                for (Symbol.MethodSymbol mm: dep.deps.get(m)) {
                    if (sk.contains(mm)) {
                        any = true;
                        boolean b = dep.skipped.contains(mm);
                        System.out.println("*** " + (b?"SK ":"") + dep.order.get(mm) + " " + toString(mm));
                    }
                }
                if (any) {
                    sk.add(m);
                    System.out.println((bm?"SK ":"") + dep.order.get(m) + " " + toString(m));
                }
            } else {
                System.out.println((bm?"SK ":"") + dep.order.get(m) + " " + toString(m));
            }
        }
        System.out.println("----------- All methods with dependencies");
        for (Symbol.MethodSymbol m: list) {
            System.out.print(dep.order.get(m) + " " + toString(m) + " :");
            for (Symbol.MethodSymbol mm: dep.deps.get(m)) System.out.print(" " + toString(mm));
            System.out.println();
        }
    }
    
    public void record(Symbol.MethodSymbol parent, Symbol.MethodSymbol child) {
        java.util.Set<Symbol.MethodSymbol> children = deps.get(parent);
        if (children == null) deps.put(parent,children = new HashSet<Symbol.MethodSymbol>());
        children.add(child);
    }
    
    public int setOrder(Symbol.MethodSymbol msym) {
        Integer i = order.get(msym);
        if (i != null) return i;
        order.put(msym, -1);
        if (deps.get(msym) == null) return -1;
        int j = 0;
        for (Symbol.MethodSymbol m: deps.get(msym)) {
            int k = setOrder(m);
            if (j <= k) j = k + 1;
        }
        order.put(msym, j);
        return j;
    }
    
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        Symbol.MethodSymbol save = currentMethod;
        currentMethod = that.sym;
        deps.put(that.sym,new HashSet<Symbol.MethodSymbol>());
        boolean sk = JmlEsc.skip(that);
        if (sk) skipped.add(that.sym);
        super.visitJmlMethodDecl(that);
        currentMethod = save;
    }
    
    public void visitApply(JCMethodInvocation tree) {
        JCExpression meth = tree.meth;
        Symbol.MethodSymbol msym = null;
        if (meth instanceof JCIdent) msym = (Symbol.MethodSymbol)((JCIdent)meth).sym;
        if (meth instanceof JCFieldAccess) msym = (Symbol.MethodSymbol)((JCFieldAccess)meth).sym;
        if (msym != null && currentMethod != null) record(currentMethod, msym);
    }
    

}
