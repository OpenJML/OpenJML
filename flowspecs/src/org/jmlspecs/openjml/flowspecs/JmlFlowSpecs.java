package org.jmlspecs.openjml.flowspecs;

import static com.sun.tools.javac.code.Kinds.VAL;
import static com.sun.tools.javac.code.Kinds.VAR;
import static com.sun.tools.javac.code.TypeTags.ERROR;
import static com.sun.tools.javac.code.TypeTags.VOID;

import java.io.File;
import java.net.MalformedURLException;
import java.util.EnumMap;
import java.util.Iterator;

import org.dom4j.DocumentException;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.flowspecs.LatticeParser.LatticeParserException;

import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.Resolve;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCDoWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCForLoop;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCSwitch;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Pair;
import com.sun.tools.javac.util.PropagatedException;

public class JmlFlowSpecs extends JmlEETreeScanner {

    /**
     * The key used to register an instance of JmlFlowSpecs in the compilation
     * context
     */
    protected static final Context.Key<JmlFlowSpecs> flowspecsKey = new Context.Key<JmlFlowSpecs>();

    protected final FlowStack                        flowStack;

    /**
     * The method used to obtain the singleton instance of JmlEsc for this
     * compilation context
     */
    public static JmlFlowSpecs instance(Context context) {
        JmlFlowSpecs instance = context.get(flowspecsKey);
        if (instance == null) {
            instance = new JmlFlowSpecs(context);

            context.put(flowspecsKey, instance);
        }
        return instance;
    }

    public static final String     defaultLatticeFile    = "security.xml";

    public EnumMap<JmlToken, Name> tokenToAnnotationName = new EnumMap<JmlToken, Name>(
                                                                 JmlToken.class);

    private Lattice<SecurityType>        lattice;

    /**
     * The compilation context, needed to get common tools, but unique to this
     * compilation run
     */
    @NonNull
    Context                        context;

    /** Used to obtain cached symbols, such as basic types */
    @NonNull
    Symtab                         syms;

    /** The tool to log problem reports */
    @NonNull
    Log                            log;

    /** The OpenJML utilities object */
    @NonNull
    Utils                          utils;

    /** true if compiler options are set to a verbose mode */
    boolean                        verbose;

    /** Just for debugging flowspecs */
    public static boolean          flowspecsdebug        = true;                 // May
                                                                                  // be
                                                                                  // set
                                                                                  // externally
                                                                                  // to
                                                                                  // enable
                                                                                  // debugging
                                                                                  // while
                                                                                  // testing

    /**
     * The JmlEsc constructor, which initializes all the tools and other fields.
     */
    public JmlFlowSpecs(Context context) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.rs = Resolve.instance(context);
        // FIXME - this is WRONG.
        this.env = new Env(null, null);
        this.flowStack = new FlowStack(this);
        Names names = Names.instance(context);

        for (JmlToken t : JmlToken.modifiers) {
            if (t.annotationType == null) {
                // No class for this token, but we won't complain
                // The result is to silently ignore the token (TODO)
            } else {
                String s = t.annotationType.getName();
                Name n = names.fromString(s);
                tokenToAnnotationName.put(t, n);
            }
        }

        this.verbose = flowspecsdebug
                || JmlOption.isOption(context, "-verbose") // The Java verbose
                                                           // option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
    }

    public void check(JCTree tree) {

        //
        // Loads the security lattice and kicks off the type checking
        //
        File latticeFile = new File(defaultLatticeFile);

        if (latticeFile.exists()) {
            progress(1, 1, String.format("Loading secuirty lattice from %s",
                    latticeFile.getName()));
            LatticeParser p = new LatticeParser(new File(defaultLatticeFile));
            try {
                lattice = p.parse();
                progress(1, 1, "Done.");

                tree.accept(this);

            } catch (MalformedURLException | DocumentException
                    | LatticeParserException e) {
                log.error("jml.flowspecs.lattice.error");
            }
        } else {
            log.error("jml.flowspecs.missing.lattice");
        }
    }

    //
    // Main typechecking logic
    //

    /**
     * Reports progress to the registered IProgressListener; also checks if the
     * progress listener has received a user-cancellation, in which case this
     * method throws an exception to terminate processing
     * 
     * @param ticks
     *            amount of work to report
     * @param level
     *            level of the message (lower levels are more likely to be
     *            printed)
     * @param message
     *            the progress message
     */
    public void progress(int ticks, int level, String message) {
        org.jmlspecs.openjml.Main.IProgressListener pr = context
                .get(org.jmlspecs.openjml.Main.IProgressListener.class);
        boolean cancelled = pr == null ? false : pr.report(ticks, level,
                String.format("[FLOWSPECS] - %s", message));
        if (cancelled) {
            throw new PropagatedException(new Main.JmlCanceledException(
                    JmlOption.FLOWSPECS + " operation cancelled"));
        }
    }

    @Override
    public void visitLiteral(JCLiteral tree) {
        //
        // We don't need to implement this since we just assume any literal
        // we encounter has the same type as the thing that came before it. It
        // is
        // provided here only for documentation and debugging purposes.
        //
    }

    @Override
    public void enterExec(JCExpressionStatement tree) {}

    @Override
    public void exitExec(JCExpressionStatement tree) {}

    @Override
    public void enterIdent(JCIdent tree) {}

    @Override
    public void exitIdent(JCIdent tree) {}

    @Override
    public void enterBlock(JCBlock tree) {
        progress(1, 1, String.format(
                "Entering Block\n----------------\n%s\n----------------",
                tree.toString()));

    }

    @Override
    public void exitBlock(JCBlock tree) {
    }

    @Override
    public void visitVarDef(JCVariableDecl tree) {

        SecurityType lt = resolveType(tree.sym);
        result = lt;

        if (tree.init != null) {
            SecurityType rt = attribExpr(tree.init, env, lt);
            result = check(tree, lt, rt);
        } else {
            result = lt;
        }
    }

    @Override
    public void enterVarDef(JCVariableDecl tree) {}

    @Override
    public void exitVarDef(JCVariableDecl tree) {}

    @Override
    public void enterTopLevel(JCCompilationUnit tree) {}

    @Override
    public void exitTopLevel(JCCompilationUnit tree) {}

    @Override
    public void enterJmlMethodClauseDecl(JmlMethodClauseDecl tree) {}

    @Override
    public void exitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {}

    @Override
    public void visitBinary(JCBinary tree) {

        SecurityType left = attribExpr(tree.lhs, env);
        SecurityType right = attribExpr(tree.rhs, env);

        result = check(tree, left, right);
    }

    @Override
    public void visitReturn(JCReturn tree) {

        //
        // We don't have to perform the same checks Java performs here.
        // We just need to make sure the types match (or may be weakened) if
        // they exist.
        //
        Symbol m = env.enclMethod.sym;
        if (tree.expr != null & m.type.getReturnType().tag != VOID) {

            // if the expr is a literal we just always let it pass
            if (tree.expr instanceof JCLiteral == false) {
                SecurityType returnType = attribExpr(tree.expr, env);
                SecurityType methodType = resolveType(m);

                check(tree, returnType, methodType);
            }

        }

        result = null;
    }

    @Override
    public void visitIdent(JCIdent tree) {
        result = resolveType(tree.sym);
    }

    private SecurityType resolveType(Symbol s) {

        SecurityType t = null;
        if (s != null) {
            for (Attribute.Compound c : s.getAnnotationMirrors()) {

                // Case 1, they have an annotation of SOME kind specificed
                if (c.type.tsym.flatName().equals(
                        tokenToAnnotationName.get(JmlToken.LEVEL))
                        || c.type.tsym.flatName().equals(
                                tokenToAnnotationName.get(JmlToken.CHANNEL))) {

                    // Our parser promises us this will exist.
                    String label = extractSpecFromAnnotationValues(c);

                    // do a little more work to figure out the type;
                    if (c.type.tsym.flatName().equals(
                            tokenToAnnotationName.get(JmlToken.CHANNEL))) {

                        // TODO write mapping between channels and levels (no
                        // really, this has to be done)

                    } else {
                        t = new SecurityType(label);
                    }

                }
            }
        }
        // Case 2, we need to infer it.
        if (t == null) {
            t = lattice.getTop();
        }

        return t;
    }

    private String extractSpecFromAnnotationValues(Attribute.Compound c) {

        String r = null;

        for (Pair<MethodSymbol, Attribute> p : c.values) {
            if (p.fst.toString().equals("value()")) {
                r = p.snd.toString().toUpperCase().replaceAll("\"", "");
                break;
            }
        }
        return r;
    }

    @Override
    public void visitApply(JCMethodInvocation tree) {
        // TODO - does a constructor call make a difference? self calls?

        if (tree.meth instanceof JCIdent
                && ((JCIdent) tree.meth).sym instanceof MethodSymbol
                && tree.getArguments().size() > 0) {

            JCIdent methodIdent = (JCIdent) tree.meth;
            MethodSymbol methodSymbol = (MethodSymbol) methodIdent.sym;

            Iterator<VarSymbol> referenceIterator = methodSymbol
                    .getParameters().iterator();
            VarSymbol referenceSymbol = referenceIterator.hasNext() ? referenceIterator
                    .next() : null;

            for (int i = 0; i < tree.getArguments().size(); i++) {

                JCExpression currentExpr = tree.getArguments().get(i);

                SecurityType lt = resolveType(referenceSymbol);
                SecurityType rt = attribExpr(currentExpr, env, lt);

                result = check(tree, lt, rt);

                // - possibly update the reference symbol.
                if (referenceIterator.hasNext())
                    referenceSymbol = referenceIterator.next();

            }

        }

    }

    @Override
    public void visitAssign(JCAssign tree) {

        SecurityType lt = attribTree(tree.lhs, null, VAR, Type.noType);

        SecurityType rt = attribExpr(tree.rhs, env, lt);

        // TODO abstract the checking function
        result = check(tree, lt, rt);
    }

    SecurityType upperBound(SecurityType t1, SecurityType t2) {

        if (t1.equals(t2)) {
            return t1;
        }

        if (lattice.isSubclass(t1, t2)) {
            return t2;
        }

        return t1;
    }

    /**
     * Checks binary expressions. Note that really, no binary expression is
     * unallowed assuming a linear lattice model. If we wish to support fully
     * lattices we will need to modify the lattice class to identify that these
     * elements are uncomparable and therefore generate a type checking error.
     * 
     * Barring that situation, this will just find the upper bound of the two
     * types.
     * 
     * @param tree
     * @param lt
     * @param rt
     * @return
     */
    public SecurityType check(JCBinary tree, SecurityType lt, SecurityType rt) {
        return upperBound(lt, rt);
    }

    public SecurityType check(JCVariableDecl tree, SecurityType dest,
            SecurityType source) {

        // no checking needed
        if (source == null) {
            return dest;
        }

        if (dest.equals(source)) {
            return upperBound(source, dest);
        }

        // ok
        if (lattice.isSubclass(source, dest)) {
            log.warning(tree.pos, "jml.flowspecs.lattice.strengthen",
                    source.toString(), dest.toString());

            return upperBound(source, dest);
        }

        // flow error
        log.error(tree.pos, "jml.flowspecs.lattice.invalidflow",
                source.toString(), dest.toString());

        return SecurityType.wrong();
    }

    public SecurityType check(JCReturn tree, SecurityType returnType,
            SecurityType methodType) {

        if (returnType.level.equals(methodType.level)) {
            return upperBound(returnType, methodType);
        }

        if (lattice.isSubclass(returnType, methodType)) {
            log.warning(tree.pos, "jml.flowspecs.lattice.strengthen",
                    returnType.toString(), methodType.toString());

            return upperBound(returnType, methodType);
        }
        log.error(tree.pos, "jml.flowspecs.lattice.return.invalidflow",
                returnType.toString(), methodType.toString());

        return SecurityType.wrong();
    }

    /**
     * 
     * @param tree
     * @param lt The reference (formal) security type.
     * @param rt The supplied (actual) security type.
     * @return
     */
    public SecurityType check(JCMethodInvocation tree, SecurityType lt,
            SecurityType rt) {
        
        SecurityType upperBound = null;

        if (lt.equals(rt)) {
            upperBound = upperBound(lt, rt);
        }

        else if (lattice.isSubclass(rt, lt)) {
            log.warning(tree.pos, "jml.flowspecs.lattice.strengthen",
                    rt.toString(), lt.toString());
            upperBound = upperBound(lt, rt);
        }else{

            log.error(tree.pos, "jml.flowspecs.lattice.invalidflow", rt.toString(),
                lt.toString());
        }

        //
        // If we've made it here, we need to check the STRONGEST bound
        //
        if (isPossibleImplicitFlow() && upperBound != null) {

            SecurityType flowBound = flowStack.currentTypeBoundary();

            if (upperBound.equals(flowBound) == false
                    && lattice.isSubclass(flowBound, upperBound) == false) {
                log.error(tree.pos, "jml.flowspecs.lattice.invalidflow.cond",
                        flowBound.toString(), upperBound.toString());
            }
        }
        
        return upperBound==null ? SecurityType.wrong() : upperBound;
    }

    public SecurityType check(JCAssign tree, SecurityType lt, SecurityType rt) {

        //
        // Two types of logic are employed here
        //
        // 1) If we are not in a possible high branch, typechecking proceeds as
        // normal.
        // 2) If we ARE in a possible high branch, the LHS of the expression is
        // checked against the upper bound of the flow

        SecurityType upperBound = null;

        if (lt.equals(rt)) {
            upperBound = upperBound(lt, rt);
        }

        else if (lattice.isSubclass(rt, lt)) {
            log.warning(tree.pos, "jml.flowspecs.lattice.strengthen",
                    rt.toString(), lt.toString());
            upperBound = upperBound(lt, rt);
        } else {

            log.error(tree.pos, "jml.flowspecs.lattice.invalidflow",
                    rt.toString(), lt.toString());
        }

        //
        // here we check for implicit flow only if the normal rules would have
        // allowed it
        //
        if (isPossibleImplicitFlow() && upperBound != null) {

            SecurityType flowBound = flowStack.currentTypeBoundary();

            if (lt.level.equals(flowBound.level) == false
                    && lattice.isSubclass(flowBound, lt) == false) {
                log.error(tree.pos, "jml.flowspecs.lattice.invalidflow.cond",
                        flowBound.toString(), lt.toString());

            }
        }

        return upperBound != null ? upperBound : SecurityType.wrong();
    }

    final Resolve    rs;

    /**
     * Visitor argument: the current environment.
     */
    Env<AttrContext> env;

    JCMethodDecl     prevMethod;

    /**
     * Visitor argument: the currently expected proto-kind.
     */
    int              pkind;

    /**
     * Visitor argument: the currently expected proto-type.
     */
    Type             pt;

    /**
     * Visitor argument: the error key to be generated when a type error occurs
     */
    String           errKey;

    /**
     * Visitor result: the computed type.
     */
    SecurityType     result;

    public SecurityType attribExpr(JCTree tree, Env<AttrContext> env, Type pt) {
        return attribTree(tree, env, VAL, pt.tag != ERROR ? pt : Type.noType);
    }

    public SecurityType attribExpr(JCTree tree, Env<AttrContext> env) {
        return attribTree(tree, env, VAL, Type.noType);
    }

    /**
     * Visitor method: attribute a tree, catching any completion failure
     * exceptions. Return the tree's type.
     * 
     * @param tree
     *            The tree to be visited.
     * @param env
     *            The environment visitor argument.
     * @param pkind
     *            The protokind visitor argument.
     * @param pt
     *            The prototype visitor argument.
     */
    SecurityType attribTree(JCTree tree, Env<AttrContext> env, int pkind,
            Type pt) {
        return attribTree(tree, env, pkind, pt, "incompatible.types");
    }

    SecurityType attribTree(JCTree tree, Env<AttrContext> env, int pkind,
            Type pt, String errKey) {
        Env<AttrContext> prevEnv = this.env;
        int prevPkind = this.pkind;
        Type prevPt = this.pt;
        String prevErrKey = this.errKey;
        try {
            this.env = env;
            this.pkind = pkind;
            this.pt = pt;
            this.errKey = errKey;
            tree.accept(this);
            return result;
        } catch (CompletionFailure ex) {
            tree.type = syms.errType;
            return null; // chk.completionError(tree.pos(), ex);
        } finally {
            this.env = prevEnv;
            this.pkind = prevPkind;
            this.pt = prevPt;
            this.errKey = prevErrKey;
        }
    }

    @Override
    public void enterAssign(JCAssign tree) {
    }

    @Override
    public void exitAssign(JCAssign tree) {
    }

    Type check(JCTree tree, Type owntype, int ownkind, int pkind, Type pt) {
        // if (owntype.tag != ERROR && pt.tag != METHOD && pt.tag != FORALL) {
        // if ((ownkind & ~pkind) == 0) {
        // owntype = chk.checkType(tree.pos(), owntype, pt, errKey);
        // } else {
        // log.error(tree.pos(), "unexpected.type",
        // kindNames(pkind),
        // kindName(ownkind));
        // owntype = types.createErrorType(owntype);
        // }
        // }
        // tree.type = owntype;
        return owntype;
    }

    @Override
    public void enterJmlMethodDecl(JmlMethodDecl tree) {
        prevMethod = env.enclMethod;
        env.enclMethod = tree;
    }

    @Override
    public void exitJmlMethodDecl(JmlMethodDecl tree) {
        env.enclMethod = prevMethod;
        prevMethod = null;

    }

    //
    // helper methods for information flow
    //

    private boolean isPossibleImplicitFlow() {

        if (flowStack.isEmpty()) {
            return false;
        }

        return true;
    }

    // TODO
    // Implement flow for WHILE, FOR, ELSE IF, SWITCH, DOWHILE?, and perhaps see
    // if the shortcut
    // a ? true : false is a sugar.

    @Override
    public void enterIf(JCIf tree) {
        flowStack.enter(tree.cond);
    }

    @Override
    public void exitIf(JCIf tree) {
        flowStack.exit();
    }

    @Override
    public void enterWhileLoop(JCWhileLoop tree) {
        flowStack.enter(tree.cond);
    }

    @Override
    public void exitWhileLoop(JCWhileLoop tree) {
        flowStack.exit();
    }

    @Override
    public void enterDoLoop(JCDoWhileLoop tree) {
        flowStack.enter(tree.cond);
    }

    @Override
    public void exitDoLoop(JCDoWhileLoop tree) {
        flowStack.exit();
    }

    @Override
    public void enterForLoop(JCForLoop tree) {
        flowStack.enter(tree.cond);
    }

    @Override
    public void exitForLoop(JCForLoop tree) {
        flowStack.exit();
    }

    @Override
    public void enterSwitch(JCSwitch tree) {
        // TODO make sure this is the right thing to check in a test.
        flowStack.enter(tree.selector);
    }

    @Override
    public void exitSwitch(JCSwitch tree) {
        flowStack.exit();
    }

    // TODO -- implement these correctly.
    @Override
    public void enterConditional(JCConditional tree) {
        flowStack.enter(tree.cond);
    }

    @Override
    public void exitConditional(JCConditional tree) {
        flowStack.exit();
    }

}
