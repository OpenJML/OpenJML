import org.openjml.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.tree.JCTree.*;
import org.jmlspecs.openjml.JmlTree.*;
import java.util.*;

public class Run {
    
    public static void main(String... args) {
      try {
        IAPI api = IAPI.make();
        api.setASTListener(new Listener());
        System.out.println("ABOUT TO EXECUTE");
        api.execute("--check", "-cp", "data", "./data/A.java");
        System.out.println("DOING ESC");
        api = IAPI.make();
        api.setASTListener(new Listener());
        var x = api.execute("--check", "-cp", "data", "data/Q.java");
        System.out.println("RES " + x);
        for (var d: Walk.topclass.defs) {
          if (d instanceof JmlMethodDecl m) {
            var r = api.doESC(m);
            System.out.println("RES " + m.sym + " " + r.result());
          }
        }
        System.out.println("DOING CLASS");
        api.doESC((JmlClassDecl)Walk.topclass);

        System.out.println("DONE");
      } catch (Exception e) {
          System.out.println("EXCEPTION: " + e);
      }
    }
}

class Listener implements IAPI.IASTListener {
    static Map<Context,Integer> contexts = new HashMap<>();
    @Override public void notify(Context context, javax.tools.JavaFileObject jfo, org.jmlspecs.openjml.JmlTree.JmlCompilationUnit cu) { 
        Integer i = contexts.get(context);
        if (i == null) contexts.put(context, (i = contexts.size()+1));
        System.out.println("ASTListener: " + i + " " + jfo + " " + cu.sourcefile); 
        cu.accept(new Walk());
    } 
}

class Walk extends org.jmlspecs.openjml.visitors.JmlTreeScanner {

    static public JCClassDecl topclass;

    public void visitClassDef(JCClassDecl tree) {
        System.out.println("CLASS " + tree.name + " " + tree.sym + " " + tree.sym.owner);
        topclass = tree;
        super.visitClassDef(tree);
    }


    public void visitMethodDef(JCMethodDecl tree) {
        System.out.println("METHOD " + tree.name + " " + tree.sym + " " + tree.sym.owner);
	super.visitMethodDef(tree);
    }


}

