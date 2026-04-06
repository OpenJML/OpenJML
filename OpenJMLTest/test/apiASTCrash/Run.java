import org.openjml.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.tree.JCTree.*;
import org.jmlspecs.openjml.JmlTree.*;

public class Run {
    
    public static void main(String... args) {
        IAPI api = IAPI.make();
        IAPI.setASTListener(new IAPI.IASTListener() { 
            @Override public void notify(Context context, javax.tools.JavaFileObject jfo, org.jmlspecs.openjml.JmlTree.JmlCompilationUnit cu) { System.out.println("ASTListener: " + context + " " + jfo + " " + cu); } 
        });
        //IAPI.setASTListener(new Listener());
        //System.out.println("ABOUT TO EXECUTE");
	//api.execute("--check", "-cp", "data", "./data/A.java");
        //System.out.println("PARSE TREES");
        //var cu = api.parseCompilationUnitString("Q.java","public class Q {}");
        //System.out.println(cu);
        System.out.println("DONE");
    }
}

class Listener implements IAPI.IASTListener {
    @Override public void notify(Context context, javax.tools.JavaFileObject jfo, org.jmlspecs.openjml.JmlTree.JmlCompilationUnit cu) { 
        System.out.println("ASTListener: " + context + " " + jfo + " " + cu); 
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

