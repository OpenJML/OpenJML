package org.jmlspecs.openjml.visitors;

import static org.jmlspecs.openjml.JmlTree.*;
import static com.sun.tools.javac.tree.JCTree.*;
import org.jmlspecs.openjml.JmlTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.tree.EndPosTable;
import javax.tools.JavaFileObject;
import org.jmlspecs.openjml.Utils;

/** A purely debugging check. Walks an AST immediately after parsing (at the end of JmlCompiloer.parse, JmlCompiler.parseSpecs) to check that
 * various invariants hold.
 * relationships between the fields of the toplevel JmlCompilationUnit of the source and spec files
 * that every node in the AST has consistent start, preferred, and end positions
 * that the class, method, fields declarations have their fields set
 * @author davidcok
 *
 */
public class JmlCheckParsedAST extends JmlTreeScanner {
    
    protected Utils utils;
    JCTree parent = null;
    JmlCompilationUnit toplevel;
    int positionSoFar = 0; // tracks position of nodes from beginning to end of source file
    JavaFileObject sourcefile;
    EndPosTable endPosTable;
    boolean ok = true;
    
    public static boolean check(Context context, JmlCompilationUnit cu, JavaFileObject file) {
        if (!Utils.isJML()) return true; // Only do checks when acting as openJML
        var prev = Log.instance(context).useSource(file);
        try {
            var visitor = new JmlCheckParsedAST(context);
            visitor.scanMode = JmlTreeScanner.AST_JAVA_MODE;
            visitor.check(cu.endPositions != null); // Check this now as endPosTable is needed in every node
            visitor.endPosTable = cu.endPositions;
            visitor.sourcefile = file;
            visitor.toplevel = cu;
            visitor.scan(cu);
            return visitor.ok;
        } finally {
            Log.instance(context).useSource(prev);
        }
    }
    
    private void check(boolean shouldBeTrue) {
        if (!shouldBeTrue) {
            ok = false;
            var a = new AssertionError("Invalid invariant in JmlCheckParsedAST: " + sourcefile);
            a.printStackTrace(System.out);
            throw a;
        }
    }
    
    protected JmlCheckParsedAST(Context context) {
        this.utils = Utils.instance(context);
    }
    
    
    @Override
    public void scan(JCTree t) {  // FIXME - need work on ordering the positions
        if (t == null) return;
        int spos = t.getStartPosition();
        int ppos = t.getPreferredPosition();
        int epos = t.getEndPosition(endPosTable);
//        if (spos != com.sun.tools.javac.util.Position.NOPOS) { // FIXME - remove when we have cleaned out all NOPOS
//            if (!(positionSoFar <= spos) || !(spos <= ppos) || !(ppos <= epos)) System.out.println("POSA " + positionSoFar + " " + spos + " " + ppos + " " + epos + " " + t.getClass() + " " + t + " " + parent.getClass() + " " + parent + " " + System.identityHashCode(t));
//            check(positionSoFar <= spos);
//            check(spos <= ppos);
//            check(ppos <= epos);
//            positionSoFar = spos;
//            if (parent != null) {
//                if (!(parent.getStartPosition() <= spos) || !(epos <= parent.getEndPosition(endPosTable))) System.out.println("POSP " + positionSoFar + " " + spos + " " + ppos + " " + epos + " " + t.getClass() + " " + t + " " + parent.getClass() + " " + parent + " " + System.identityHashCode(t));
//                check(parent.getStartPosition() <= spos);
//                check(epos <= parent.getEndPosition(endPosTable));
//            }
//        } else {
//            //System.out.println("POS " + positionSoFar + " " + spos + " " + t.getClass());
//        }
        var savedParent = parent;
        parent = t;
        super.scan(t);
        parent = savedParent;
//        if (epos != com.sun.tools.javac.util.Position.NOPOS) { // FIXME - remove when we have cleaned out all NOPOS
//            check(positionSoFar <= epos);
//            positionSoFar = epos;
//        }
    }
    
    @Override
    public void visitTopLevel(JCCompilationUnit cu) {
        JmlCompilationUnit jcu = (JmlCompilationUnit)cu;
        // FIXME - need to review the distinctions of these three cases
        if (jcu.sourceCU == null) {
            // A spec AST for a binary file
            //System.out.println("Checking a binary AST " + jcu.sourcefile);
            var specCU = jcu;
            check(specCU.type == null);
            check(specCU.specsCompilationUnit == specCU);
            check(specCU.sourceCU == null);
            check(specCU.sourcefile != null);
            check(utils.isSpecFile(specCU.sourcefile));
            check(specCU.topLevelEnv == null);
            check(specCU.defs != null);
            // specCU.pid -- the package declaration maybe null or may not be
            check(specCU.packge != null); // package symbol is set from binary
            check(specCU.modle != null); // module is set from binary
            check(specCU.locn == null);
            
            // not checking: getTag()
            // not checking: toplevelScope, namedImportScope, starImportScope -- should all be null
            // not checking: lineMap, docComments
        } else if (jcu == jcu.specsCompilationUnit && jcu.sourceCU == jcu) {
            // javaCU and specCU are the same
            //System.out.println("Checking a source&spec AST " + jcu.sourcefile);
            var javaCU = jcu;
            check(javaCU.type == null);
            check(javaCU.specsCompilationUnit == javaCU);
            check(javaCU.sourceCU == javaCU);
            check(javaCU.sourcefile != null);
            check(!utils.isSpecFile(javaCU.sourcefile));
            check(javaCU.topLevelEnv == null);
            check(javaCU.defs != null);
            // javaCU.pid -- the package declaration maybe null or may not be
            check(javaCU.packge == null); // package symbol not yet set
            check(javaCU.modle == null);
            check(javaCU.locn == null);
            
            // not checking: getTag()
            // not checking: toplevelScope, namedImportScope, starImportScope -- should all be null
            // not checking: lineMap, docComments
        } else if (!jcu.isSpecs()) {
            // the .java file of a .java and .jml pair -- the .jml file is checked separately
            //System.out.println("Checking a source AST of a source/spec pair" + jcu.sourcefile);
            var javaCU = jcu;
            var specCU = jcu.specsCompilationUnit;
            check(javaCU.type == null);
            check(javaCU.specsCompilationUnit == specCU);
            check(specCU.sourceCU == javaCU);
            check(javaCU.sourceCU == javaCU);
            check(javaCU.sourcefile != null);
            check(!utils.isSpecFile(javaCU.sourcefile));
            check(javaCU.topLevelEnv == null);
            check(javaCU.defs != null);
            // javaCU.pid -- the package declaration maybe null or may not be
            check(javaCU.packge == null); // package symbol not yet set
            check(javaCU.modle == null);
            check(javaCU.locn == null);
            
            // not checking: getTag()
            // not checking: toplevelScope, namedImportScope, starImportScope -- should all be null
            // not checking: lineMap, docComments
        } else {
            // the .jml file of a .java and .jml pair  -- the .java file is checked separately
            //System.out.println("Checking a spec AST of a source/spec pair" + jcu.sourcefile);
            var javaCU = jcu.sourceCU;
            var specCU = jcu;
            check(specCU.type == null);
            check(specCU.specsCompilationUnit == specCU);
            check(specCU.sourceCU == javaCU);
            check(specCU.sourcefile != null);
            check(utils.isSpecFile(specCU.sourcefile));
            check(specCU.topLevelEnv == null);
            check(specCU.defs != null);
            // specCU.pid -- the package declaration maybe null or may not be
            check(specCU.packge == null); // package symbol not yet set
            check(specCU.modle == null);
            check(specCU.locn == null);
            
            // not checking: getTag()
            // not checking: toplevelScope, namedImportScope, starImportScope -- should all be null
            // not checking: lineMap, docComments
            
        }
//        super.visitTopLevel(cu); // FIXME - need to cleanup everything before enabling this again
    }
    
    @Override
    public void visitClassDef(JCClassDecl node) {
        JmlClassDecl classDecl = (JmlClassDecl)node;
        check(classDecl.type == null);
        check(classDecl.sym == null);
        check(classDecl.sourcefile == this.sourcefile);
        check(classDecl.specsDecl == null);
        check(classDecl.env == null);
        //check(classDecl.typeSpecs != null); // FIXME - what about this?
 //       check(classDecl.toplevel == this.toplevel);   FIXME
        
        // not checking docComment, lineAnnotations
        super.visitClassDef(node);
    }

    @Override
    public void visitMethodDef(JCMethodDecl node) {
        JmlMethodDecl methodDecl = (JmlMethodDecl)node;
        check(methodDecl.type == null);
        check(methodDecl.sym == null);
        check(methodDecl.sourcefile == this.sourcefile);
        check(methodDecl.specsDecl == null);
        
        // not checking docComment
        super.visitMethodDef(node);
    }

    @Override
    public void visitVarDef(JCVariableDecl node) {
        // Visited for all variable declarations, not just fields
        JmlVariableDecl variableDecl = (JmlVariableDecl)node;
        check(variableDecl.type == null);
        check(variableDecl.sym == null);
        check(variableDecl.sourcefile == this.sourcefile); // Perhaps true only for fields
        check(variableDecl.specsDecl == null);
        // fieldSpecs -- may or may not be null
        
        // not checking docComment
        super.visitVarDef(node);
    }
    
    @Override
    public void visitBlock(JCBlock node) {
        JmlBlock block = (JmlBlock)node;
        if (parent instanceof JmlClassDecl cd) {
            check(block.sourcefile == cd.sourcefile);
            check(block.isInitializerBlock);
            // FIXME - blockSpecs, specificationCases, _this ?
        } else {
            // check(block.sourcefile == null); // FIXME
            check(!block.isInitializerBlock);
        }
        super.visitBlock(node);
    }

}
