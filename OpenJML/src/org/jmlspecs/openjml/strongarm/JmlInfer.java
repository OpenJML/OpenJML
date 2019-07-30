package org.jmlspecs.openjml.strongarm;

import static com.sun.tools.javac.code.Flags.ENUM;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.ext.OptionsInfer;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

/**
 * This class is the main driver for executing contract inference on a Java/JML AST.
 * The structure of the driver is heavily based on the other drivers (JmlRac and JmlEsc).
 * 
 * @author John L. Singleton
 */

public abstract class JmlInfer<T extends JmlInfer<?>> extends JmlTreeScanner {

        
        /** The compilation context, needed to get common tools, but unique to this compilation run*/
        @NonNull Context context;

        /** Used to obtain cached symbols, such as basic types */
        @NonNull Symtab syms;
        
        /** The tool to log problem reports */ 
        @NonNull Log log;
        
        /** The OpenJML utilities object */
        @NonNull Utils utils;
        
        final protected JmlTreeUtils           treeutils;
        
        final protected JmlTree.Maker M;

        
        /** true if compiler options are set to a verbose mode */
        boolean verbose;
        
        /** Just for debugging contract inference */
        public static boolean inferdebug = false; 
        
        /** The assertion adder instance used to translate */
        public JmlAssertionAdder assertionAdder;
        
        /** the contracts will be printed to stdout **/
        public boolean printContracts = false;
        
        /** the contracts will be printed to the filesystem **/
        public boolean persistContracts = false;
        
        /** the contracts will be weaved into the source code **/
        public boolean weaveContracts = false;
        
        /** the contracts will have a INFERRED key **/
        public boolean printKey       = true;
        
        private static final String inferenceKey = "INFERRED";
        
        protected boolean didInfer = false;
        
        /** a container to hold the inferred specs -- this will be saved/flushed between visits to classes **/
        public ArrayList<JCMethodDecl> inferredSpecs = new ArrayList<JCMethodDecl>();
        
        public Path persistPath;
        
        public String currentFilename;
        
        public JCClassDecl lastClass;
        
        /** The JmlInfer constructor, which initializes all the tools and other fields. */
        public JmlInfer(Context context) {
            this.context = context;
            this.syms = Symtab.instance(context);
            this.log = Log.instance(context);
            this.utils = Utils.instance(context);
            this.inferdebug = JmlOption.isOption(context, OptionsInfer.INFER_DEBUG);      
            
            this.treeutils = JmlTreeUtils.instance(context);
            this.M = JmlTree.Maker.instance(context);
            
            
            // verbose will print all the chatter
            this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
                
            // print contracts will print the derived contracts
            this.printContracts = JmlOption.isOption(context, JmlOption.SHOW);
            // we will save contracts
            this.persistContracts = JmlOption.isOption(context,  OptionsInfer.INFER_PERSIST);
            
            this.weaveContracts = JmlOption.value(context,  OptionsInfer.INFER_PERSIST).equalsIgnoreCase("java");

            
            // but to where?
            if(this.persistContracts && this.weaveContracts == false){
                
                if(JmlOption.isOption(context, OptionsInfer.INFER_PERSIST_PATH)){  // -infer-persist-path dominates
                     persistPath = Paths.get(JmlOption.value(context,  OptionsInfer.INFER_PERSIST_PATH));
                }else if(JmlOption.isOption(context, JmlOption.SPECS)){         // followed by -specspath
                    persistPath = Paths.get(JmlOption.value(context,  JmlOption.SPECS));                    
                }else{                                                          // failing those options, we default to wherever the class source is
                    persistPath = null;
                }
            
                
            }else{
                this.persistContracts = false;
            }
                
            
            this.printKey = Boolean.parseBoolean(JmlOption.value(context, OptionsInfer.INFER_TAG));
            

        }
        
      
        /** this allows subclasses to have their own keys **/
        public abstract Context.Key<T> getKey();
        
        

        /** Initializes assertionAdder **/
        public boolean check(JCTree tree) {
            this.assertionAdder = new JmlAssertionAdder(context, false, false, true);
            this._JML_ERROR = false;
            try {
                
                if(tree instanceof JmlClassDecl){
                    JmlClassDecl cd = (JmlClassDecl)tree;
                    
                    if(skipExplicit(cd)){
                        markClassSkipped(cd, "(skipped because of SkipInfer annotation on a class-level element).");
                        return false;
                    }
                }
                
                assertionAdder.convert(tree); // get at the converted tree through the map
                tree.accept(this);
                return true;
            } 
            catch(StackOverflowError so){
                Exception e = new Exception("Stack Overflow in OpenJML");
                if(tree instanceof JmlClassDecl){
                    JmlClassDecl cd = (JmlClassDecl)tree;

                    JmlInferPostConditions.emitStrongarmFatalError(cd.sourcefile.toString(), e);
                    this._JML_ERROR = true;
                    tree.accept(this);

                }else{
                    JmlInferPostConditions.emitStrongarmFatalError(tree.toString(), e);
                    this._JML_ERROR = true;
                    tree.accept(this);

                    
                }
            }
            catch (Exception e) {
                JmlInferPostConditions.emitStrongarmFatalError(tree.toString(), e);
                ///log.error("jml.internal","Should not be catching an exception in JmlInfer.check");
            }
            
            return false;
            
        }
        
        private boolean _JML_ERROR = false;
        
        /** Visit a class definition */
        @Override
        public void visitClassDef(JCClassDecl node) {
            // inference only works on method bodies (so there is nothing to infer)
            if (node.sym.isInterface()) return;  
       
            // The super class takes care of visiting all the methods
            utils.progress(1,1,"Inferring contracts for methods in " + utils.classQualifiedName(node.sym) ); //$NON-NLS-1$
            super.visitClassDef(node);
            utils.progress(1,1,"Completed inferring contracts for methods in " + utils.classQualifiedName(node.sym) ); //$NON-NLS-1$
            
            lastClass = node;
        }
        
        public Path filenameForSource(String source){
        
            // the java source
            Path java = Paths.get(source);
            
            // the jml source
            Path jml = Paths.get(java.toString().substring(0, java.toString().toLowerCase().lastIndexOf(".java")) + ".jml");
            
            if(persistPath!=null){
                return persistPath.resolve(jml);
            }else{
                return jml;
            }
        }
        
        public Path jsonFilenameForSource(String source, JmlMethodDecl methodDecl){
            
            // the java source
            Path java = Paths.get(source);
            
            // the dot source
            Path dot = Paths.get(java.toString().substring(0, java.toString().toLowerCase().lastIndexOf(".java")) + "." + methodDecl.sym.name.toString() + ".json");
            
            if(persistPath!=null){
                return persistPath.resolve(dot);
            }else{
                return dot;
            }
        }
        
        public void weaveContract(String contract, String file, int position){
         // for each of these things, seek to the position the method begins, then write it out
            
            String mode = "rw";
            
            try {
                File tempFile = File.createTempFile(file,".tmp");
                tempFile.deleteOnExit();
                
                RandomAccessFile ra = new RandomAccessFile(file, mode);
                RandomAccessFile temp = new RandomAccessFile(tempFile, "rw");
                
                long fileSize = ra.length();
                
                FileChannel sourceChannel = ra.getChannel();
                FileChannel targetChannel = temp.getChannel();
                
                sourceChannel.transferTo(position, (fileSize - position), targetChannel);
                sourceChannel.truncate(position);
                
                ra.seek(position);
                
                // go backwards until we get a newline character.
                long newlinePosition = -1;
                
                StringBuffer buff = new StringBuffer();
                
                while(ra.getFilePointer() >= 2){                    
                    ra.seek(ra.getFilePointer()-1);
                                        
                    int c = ra.read();
                    
                    if(c==10){
                        newlinePosition = ra.getFilePointer();
                        break;
                    }
                    
                    buff.append((char)c);
                    
                    ra.seek(ra.getFilePointer()-1);
                    
                }
                
                // first normalize the lines of the contract.
                {
                    StringBuffer contractBuffer = new StringBuffer();
                    
                    String[] parts = contract.split(System.lineSeparator());
                    for(int i=0; i< parts.length; i++){
                        if(i==0){
                            contractBuffer.append(parts[i]);
                            contractBuffer.append(System.lineSeparator());
                            continue;
                        }
                        
                        contractBuffer.append(buff.toString() + "  ");
                        contractBuffer.append(parts[i]);
                        contractBuffer.append(System.lineSeparator());
                        
                    }
                    
                    contract = contractBuffer.toString();
                }
                
                ra.seek(position);                
                ra.writeBytes(contract);
                
                if(newlinePosition!=-1){
                    ra.writeBytes(buff.toString());
                }
                
                long newOffset = ra.getFilePointer();
                
                targetChannel.position(0L);
                sourceChannel.transferFrom(targetChannel, newOffset, (fileSize - position));
                sourceChannel.close();
                targetChannel.close();

                
            } catch (IOException e) {
                log.error("jml.internal","Unable to write path " + e.getMessage());

            }   
        }
        
        public void weaveContracts(String source, JmlClassDecl node){
            
            // first, sort the inferredSpecs so that the later line numbers are FIRST.  
            inferredSpecs.sort((m1, m2) -> new Integer(m2.pos).compareTo(m1.pos)); 
            
         
            // for each of these things, seek to the position the method begins, then write it out
            String file = node.sourcefile.getName();
            
            for(JCMethodDecl m : inferredSpecs){
                if(m instanceof JmlMethodDecl){
                    
                    utils.progress(1,1,"[INFER] Weaving Specs for: " + m.sym.toString()); 
                    int pos = m.pos;
                    
                    if(m.mods != null && m.mods.pos != -1){
                        pos = m.mods.pos;
                    }
                    String contract = null;
                    
                    if(printKey){
                        contract = SpecPretty.write(((JmlMethodDecl)m).cases, true, true, this.inferenceKey);
                    }else{
                        contract = SpecPretty.write(((JmlMethodDecl)m).cases, true);                        
                    }
                    
                    try {
                        contract = contract.replaceAll("\\*\\/", "@*/");
                        
                        // figure out how much in to go
                        int sep = 0;
                        for(sep = contract.indexOf('\n')+1; sep<contract.length(); sep++){
                            if(contract.charAt(sep)!=' '){
                            break;
                            }
                        }
                        
                        sep = sep - contract.indexOf('\n') - 1;
                                            
                        Pattern regex = Pattern.compile("^((\\s){" + sep +  "})", Pattern.MULTILINE);
                        Matcher match = regex.matcher(contract);
    
                        contract = match.replaceAll("@ ");
                        
                        contract = contract.replaceAll(" @\\*\\/", "@*/");
                    }catch(Exception e){}
                    
                    weaveContract(contract, file, pos);
                }               
            }
                              
            
        }
        
        public void flushContracts(String source, JmlClassDecl node){
            
            if(this.persistContracts){
                writeContracts(source, node);
            }else if(this.weaveContracts){
                weaveContracts(source, node);
            }
            
            // flush the specs
            inferredSpecs.clear();
        }
            
        public void writeContracts(String source, JmlClassDecl node){
        
           
            com.sun.tools.javac.util.List JDKList;

            if(lastClass==null){ return; }
            utils.progress(1,1,"[INFER] Persisting contracts for methods in " + utils.classQualifiedName(lastClass.sym) ); 

            if((node.mods.flags & Flags.ENUM) !=0){
                utils.progress(1,1,"[INFER] Won't wrote enum class methods in " + utils.classQualifiedName(lastClass.sym) ); 
                return;
            }
            
            
            Path writeTo = filenameForSource(source);
            
            // make the path
            writeTo.toFile().getParentFile().mkdirs();
            
            utils.progress(1,1,"[INFER] Persisting specs to: " + writeTo.toString()); 

            try {
                
                if(importsAdded(node)==false){
                    addImports(node);
                }
                
                promoteFields(node);
                
                String spec = null;
                
                if(printKey){
                    spec = SpecPretty.write(node,  true, true, inferenceKey);
                }else{
                    spec = SpecPretty.write(node,  true);                    
                }
                
                Files.write(writeTo, spec.getBytes());
                                
            } catch (IOException e1) {
                log.error("jml.internal","Unable to write path " + writeTo.toString());
            }
            
        }
        private boolean isPrivate(JmlVariableDecl var){ 
            return (var.mods.flags & Flags.PRIVATE) == Flags.PRIVATE || (var.mods.flags & Flags.PROTECTED) == Flags.PROTECTED;
            }
        private void promoteFields(JmlClassDecl node){
            
            for(List<JCTree> defs = node.defs; defs.nonEmpty(); defs = defs.tail){
                if(defs.head instanceof JmlVariableDecl){
                    JmlVariableDecl var = (JmlVariableDecl) defs.head;
                    
                    if(isPrivate(var) && var.toString().contains("@SpecPublic")==false){
                        
                        JCExpression t = M.Ident("org.jmlspecs.annotation.SpecPublic");        
                        JCAnnotation ann = M.Annotation(t, List.<JCExpression> nil());
            
                        
                        if(var.mods.annotations==null){
                          var.mods.annotations = List.of(ann);                
                      }else{
                          var.mods.annotations = var.mods.annotations.append(ann);
          
                      }
                    }
                }else if(defs.head instanceof JmlClassDecl){
                    promoteFields((JmlClassDecl)defs.head);
                }
            }
        }
        
        private boolean importsAdded(JmlClassDecl node){
            
            List<JCTree> defs = null;

            
            for(List<JCTree> stmts = node.toplevel.defs ; stmts.nonEmpty(); stmts = stmts.tail){
                
                if(stmts.head instanceof JmlImport && ((JmlImport)stmts.head).qualid.toString().contains("org.jmlspecs.annotation.*")){
                    continue;
                }

                if(defs == null){
                    defs = List.of(stmts.head);
                }else{
                    defs = defs.append(stmts.head);
                }
            }

            node.toplevel.defs = defs;
            return false;
        }

        private void addImports(JmlClassDecl node){
            
            List<JCTree> defs = null;

            JCIdent im = M.Ident("org.jmlspecs.annotation.*");

            
            for(List<JCTree> stmts = node.toplevel.defs ; stmts.nonEmpty(); stmts = stmts.tail){
                                
                if(stmts.head instanceof JmlClassDecl){
                    if(defs == null){
                        defs = List.of((JCTree)M.JmlImport(im, false, false));
                    }else{
                        defs = defs.append(M.JmlImport(im, false, false));
                    }
                }
         
                if(defs == null){
                    defs = List.of(stmts.head);
                }else{
                    defs = defs.append(stmts.head);
                }
            
            }
            
            node.toplevel.defs = defs;
            
            
        }

        
        /** When we visit a method declaration, we translate and prove the method;
         * we do not walk into the method any further from this call, only through
         * the translation mechanism.  
         */
        @Override
        public void visitMethodDef(@NonNull JCMethodDecl decl) {
            
            if (decl.body == null) return; 
            if (!(decl instanceof JmlMethodDecl)) {
                log.warning(decl.pos(),"jml.internal","Unexpected non-JmlMethodDecl in JmlInfer - not doing inference " + utils.qualifiedMethodSig(decl.sym)); //$NON-NLS-2$
                return;
            }

            JmlMethodDecl methodDecl = (JmlMethodDecl)decl;

            if (skipExplicit(methodDecl)) {
                markMethodSkipped(methodDecl," (excluded by skipinfer)"); //$NON-NLS-1$
                return;
            }

            // Do any nested classes and methods first (which will recursively call
            // this method)
            super.visitMethodDef(methodDecl);

            if (!filter(methodDecl)) {
                markMethodSkipped(methodDecl," (excluded by -method)"); //$NON-NLS-1$ 
                return;
            }
            utils.progress(1,1,"Starting...."); 
            doMethod(methodDecl);
            return;        
        }
        
        public boolean skipExplicit(JmlClassDecl decl) {
            if (decl.mods != null) {
                for (JCTree.JCAnnotation a : decl.mods.annotations) {
                    if (a != null && a.type.toString().equals("org.jmlspecs.annotation.SkipInfer")) { // FIXME - do this without converting to string
                        return true;
                    }
                }
            }
            return false;
        }
        
        public boolean skipExplicit(JmlMethodDecl methodDecl) {
            if (methodDecl.mods != null) {
                for (JCTree.JCAnnotation a : methodDecl.mods.annotations) {
                    if (a != null && a.type.toString().equals("org.jmlspecs.annotation.SkipInfer")) { // FIXME - do this without converting to string
                        return true;
                    }
                }
            }
            return false;
        }
        
        public boolean skipNoCode(JmlMethodDecl methodDecl){
            boolean isConstructor = methodDecl.sym.isConstructor();
            boolean canInfer = ((methodDecl.mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
            
            // skip constructors and other types of methods that lack code         
            if ((methodDecl.sym.owner == syms.objectType.tsym && isConstructor) || !canInfer){
                return true;
            }
            
            return false;
        }
        
        public void markMethodSkipped(JmlMethodDecl methodDecl, String reason) {
            utils.progress(1,1,"Skipping contract inference of " + utils.qualifiedMethodSig(methodDecl.sym) + reason); //$NON-NLS-1$ //$NON-NLS-2$
        }
        
        public void markClassSkipped(JmlClassDecl classDecl, String reason) {
            utils.progress(1,1,"Skipping contract inference of " + utils.classQualifiedName(classDecl.sym) + reason); //$NON-NLS-1$ //$NON-NLS-2$
        }
        

        public abstract void inferContract(@NonNull JmlMethodDecl methodDecl);
        public abstract String inferenceType();
        
        protected void doMethod(@NonNull JmlMethodDecl methodDecl) {
            
            if (skipExplicit(methodDecl)) {                
                markMethodSkipped(methodDecl," (because of SkipInfer annotation)");
                return;
            }

            // skip constructors and other types of methods that lack code         
            if (skipNoCode(methodDecl)){
                markMethodSkipped(methodDecl," (because it was a type of program construct that lacks inferable code)");
                return;
            }

            // TODO -- do it in extended class?
//            if(skipImplicit(methodDecl)){
//                markMethodSkipped(methodDecl," (because postcondition was already available annotation)");
//                return;                
//            }
            
            
            try{
                // also, let's not try to infer synthentic methods. 
                   {
                       if(methodDecl.toString().contains("public <init>")){
                          return;                        
                       }
                   }
                    
            }catch(Exception e){}
               
            
            
            utils.progress(1,1,"Starting " + inferenceType() + " inference of " + utils.qualifiedMethodSig(methodDecl.sym));
            
            if (verbose) {
                log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                log.getWriter(WriterKind.NOTICE).println("--------------------------------------"); //$NON-NLS-1$
                log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                log.getWriter(WriterKind.NOTICE).println("STARTING INFERENCE OF " + utils.qualifiedMethodSig(methodDecl.sym) + " (" +  JDKListUtils.countLOC(methodDecl.body) + " LOC)"); //$NON-NLS-1$
                log.getWriter(WriterKind.NOTICE).println(JmlPretty.write(methodDecl.body));
            }
                        
            
            //
            //
            // We need to be able to tell the difference between a OpenJML error and a Strongarm error. For this reason we 
            // will say we "start" the inference, but abort because of an error. 
            //
            //
            if(this._JML_ERROR){
            
                if (verbose) {
                    log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                    log.getWriter(WriterKind.NOTICE).println("--------------------------------------"); //$NON-NLS-1$
                    log.getWriter(WriterKind.NOTICE).println(Strings.empty);
                    log.getWriter(WriterKind.NOTICE).println("Inference ABORTED (OPENJML ERROR) " + utils.qualifiedMethodSig(methodDecl.sym) + " (" +  JDKListUtils.countLOC(methodDecl.body) + " LOC)"); //$NON-NLS-1$
                    log.getWriter(WriterKind.NOTICE).println(JmlPretty.write(methodDecl.body));
                }
                
                
                
                
                
                return;
            }
            
            didInfer = false;
            
            inferContract(methodDecl);
                        
            
            if(methodDecl.cases != null && methodDecl.methodSpecsCombined != null && didInfer){
                inferredSpecs.add(methodDecl);
            }
            
        }
            
        /** Return true if the method is to be checked, false if it is to be skipped.
         * A warning that the method is being skipped is issued if it is being skipped
         * and the verbosity is high enough.
         * */
        public boolean filter(JCMethodDecl methodDecl) {
            String fullyQualifiedName = utils.qualifiedName(methodDecl.sym);
            String simpleName = methodDecl.name.toString();
            if (methodDecl.sym.isConstructor()) {
                String constructorName = methodDecl.sym.owner.name.toString();
                fullyQualifiedName = fullyQualifiedName.replace("<init>", constructorName);
                simpleName = simpleName.replace("<init>", constructorName);
            }
            String fullyQualifiedSig = utils.qualifiedMethodSig(methodDecl.sym);

            String methodsToDo = JmlOption.value(context,JmlOption.METHOD);
            if (methodsToDo != null && !methodsToDo.isEmpty()) {
                match: {
                    if (fullyQualifiedSig.equals(methodsToDo)) break match; // A hack to allow at least one signature-containing item in the methods list
                    for (String methodToDo: methodsToDo.split(",")) { //$NON-NLS-1$  //FIXME - this does not work when the methods list contains signatures containing commas
                        if (fullyQualifiedName.equals(methodToDo) ||
                                methodToDo.equals(simpleName) ||
                                fullyQualifiedSig.equals(methodToDo)) {
                            break match;
                        }
                        try {
                            if (Pattern.matches(methodToDo,fullyQualifiedName)) break match;
                        } catch(PatternSyntaxException e) {
                            // The methodToDo can be a regular string and does not
                            // need to be legal Pattern expression
                            // skip
                        }
                    }
                    if (utils.jmlverbose > Utils.PROGRESS) {
                        log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it does not match " + methodsToDo);  //$NON-NLS-1$//$NON-NLS-2$
                    }
                    return false;
                }
            }
            
            String excludes = JmlOption.value(context,JmlOption.EXCLUDE);
            if (excludes != null) {
                for (String exclude: excludes.split(",")) { //$NON-NLS-1$
                    if (fullyQualifiedName.equals(exclude) ||
                            fullyQualifiedSig.equals(exclude) ||
                            simpleName.equals(exclude) ||
                            Pattern.matches(exclude,fullyQualifiedName)) {
                        if (utils.jmlverbose > Utils.PROGRESS)
                            log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it is excluded by " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                        return false;
                    }
                }
            }

            return true;
        }
        
}
