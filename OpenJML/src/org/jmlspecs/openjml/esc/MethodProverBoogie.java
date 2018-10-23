package org.jmlspecs.openjml.esc;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.utils.ExternalProcess;

import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;

public class MethodProverBoogie extends MethodProverSMT {

    protected JmlSpecs specs;
    
    public MethodProverBoogie(JmlEsc jmlesc) {
        super(jmlesc);
        this.specs = JmlSpecs.instance(context);
    }

    // FIXME: REVIEW THIS
    /** Perform an ESC check of the method using boogie+Z3 */
    public IProverResult prove(JmlMethodDecl decl) {
        boolean print = true; //true;
        PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
        if (print && decl.name.toString().equals("<init>")) {
            noticeWriter.println("SKIPPING PROOF OF " + decl.name);
            return null;
        }

        utils.progress(0,2,"Starting proof of " + utils.qualifiedMethodSig(decl.sym)+ " with prover ??? " );

        if (print) {
            noticeWriter.println(Strings.empty);
            noticeWriter.println("--------------------------------------");
            noticeWriter.println(Strings.empty);
            noticeWriter.println("STARTING PROOF OF " + decl.sym.owner.getQualifiedName() + "." + decl.sym);
            noticeWriter.println(JmlPretty.write(decl.body));
        }

        JmlMethodDecl tree = (JmlMethodDecl)decl;
        JmlClassDecl currentClassDecl = (JmlClassDecl)JmlEnter.instance(context).getEnv((ClassSymbol)decl.sym.owner).tree;

        // Get the denested specs for the method - FIXME - when might they be null?
        if (tree.sym == null) {
            log.error("jml.internal.notsobad", "Unexpected null symbol for " + decl.name);
        }
        JmlMethodSpecs denestedSpecs = tree.sym == null ? null : specs.getDenestedSpecs(tree.sym);

        JmlAssertionAdder assertionAdder = new JmlAssertionAdder(context,true,false);
        JCBlock newblock = assertionAdder.convertMethodBody(tree,currentClassDecl);
        noticeWriter.println(JmlPretty.write(newblock));

        BoogieProgram program = new Boogier(context).convertMethodBody(newblock, decl, denestedSpecs, currentClassDecl, assertionAdder);
        String filename = "boogie_" + decl.getName() + ".bpl";
        StringWriter sw = new StringWriter();
        String programString;
        try {
            program.write(sw);
            FileWriter fw = new FileWriter(filename);
            programString = sw.toString();
            fw.append(programString);
            fw.close();
        } catch (IOException e) {
            noticeWriter.println("Could not write boogie output file"); // FIXME - error
            return null;
        }
        noticeWriter.println(programString);

        String boogie = Options.instance(context).get("openjml.prover.boogie");
        ExternalProcess p = new ExternalProcess(context,null,
                boogie,
                "/nologo",
                "/proverWarnings:1",
                "/coalesceBlocks:0",
                "/removeEmptyBlocks:0",
                filename);
        try {
            p.start();
            int exitVal = p.readToCompletion();
            noticeWriter.println("Boogie exit val " + exitVal); // FIXME - guard or delete verbose output
            String out = p.outputString.toString();
            noticeWriter.println("OUTPUT: " + out);
            noticeWriter.println("ERROR: " + p.errorString.toString());
            if (out.contains("This assertion might not hold")) {
                int k = out.indexOf('(');
                int kk = out.indexOf(',');
                int line = Integer.parseInt(out.substring(k+1,kk));
                k = 0;
                while (--line > 0) k = 1 + programString.indexOf('\n',k);
                kk = 1 + programString.indexOf("\"",programString.indexOf(":reason",k));
                int kkk = programString.indexOf('"',kk);
                String reason = programString.substring(kk,kkk);
                kk = 4 + programString.indexOf(":id",k);
                kkk = programString.indexOf('}',kk);
                String id = programString.substring(kk,kkk);
                JmlStatementExpr assertStat = program.assertMap.get(id);
                Label label = Label.find(reason);
                // FIXME - defensive chjeck assertStat not null

                kk = out.lastIndexOf(BasicBlockerParent.RETURN);
                if (kk < 0) kk = out.lastIndexOf(BasicBlockerParent.THROW);
                int terminationPos = 0;
                if (kk >= 0) {
                    kkk = out.lastIndexOf(BasicBlockerParent.blockPrefix,kk) + BasicBlockerParent.blockPrefix.length();
                    try {
                        terminationPos = Integer.parseInt(out.substring(kkk,kk));
                    } catch (NumberFormatException e) {
                        noticeWriter.println("NO RETURN FOUND"); // FIXME
                        // continue
                    }
                }
                if (terminationPos == 0) terminationPos = decl.pos;
                JavaFileObject prev = null;
                int pos = assertStat.pos;
                if (pos == Position.NOPOS || pos == decl.pos) pos = terminationPos;
                if (assertStat.source != null) prev = log.useSource(assertStat.source);
                String extra = Strings.empty;
                JCExpression optional = assertStat.optionalExpression;
                if (optional != null) {
                    if (optional instanceof JCTree.JCLiteral) extra = ": " + ((JCTree.JCLiteral)optional).getValue().toString();
                }
                log.warning(pos,"esc.assertion.invalid",label,decl.getName(),extra);
            	String loc = utils.locationString(pos);
                // TODO - above we include the optionalExpression as part of the error message
                // however, it is an expression, and not evaluated for ESC. Even if it is
                // a literal string, it is printed with quotes around it.
                if (prev != null) log.useSource(prev);
                if (assertStat.associatedPos != Position.NOPOS) {
                    if (assertStat.associatedSource != null) prev = log.useSource(assertStat.associatedSource);
                    log.warning(assertStat.associatedPos, 
                    		Utils.testingMode ? "jml.associated.decl" :"jml.associated.decl.cf",loc);
                    if (assertStat.associatedSource != null) log.useSource(prev);
                }

                //                    if (label == Label.POSTCONDITION || label == Label.SIGNALS) {
                //                        log.warning(terminationPos,"esc.assertion.invalid",label,decl.getName() + cf, Strings.empty);
                //                        log.warning(assertStat.pos, "jml.associated.decl");
                //                    } else if (label == Label.ASSIGNABLE) {
                //                        log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, Strings.empty);
                //                        log.warning(assertStat.associatedPos, "jml.associated.decl");
                //                    } else if (label != Label.EXPLICIT_ASSERT && label != Label.EXPLICIT_ASSUME){
                //                        log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, Strings.empty); 
                //                        if (assertStat.pos != assertStat.associatedPos && assertStat.associatedPos != Position.NOPOS){
                //                            log.warning(assertStat.associatedPos, "jml.associated.decl");
                //                        }
                //                    } else {
                //                        log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, Strings.empty); 
                //                    }

                return null;
            } else if (out.contains(" 0 errors")) {
                return null;
            } else {
                log.error(0,"jml.internal","Unknown result returned from prover"); // FIXME - use a different message
            }
        } catch (Exception e) {
            System.out.println("EXCEPTION: " + e); // FIXME
            return null;
        }

        return null;
    }

}
