package org.openjml.lsp;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import org.eclipse.lsp4j.DocumentSymbol;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.SymbolKind;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlModifiers;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.ext.Modifiers;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

/**
 * Produces a hierarchical {@link DocumentSymbol} tree from a Java/JML source file.
 *
 * <p>Used for {@code textDocument/documentSymbol} (the VS Code Outline panel).
 *
 * <p>Uses {@link JmlTreeScanner} in its default {@code AST_JML_MODE}, which
 * visits both the regular {@code defs} list and the JML type-spec clauses
 * ({@code ms.clauses}).  This ensures ghost and model declarations are
 * included automatically alongside regular Java members.
 *
 * <p>Ghost and model symbols carry a {@link DocumentSymbol#setDetail detail}
 * of {@code "ghost"} or {@code "model"} so they are visually distinguishable
 * in the outline (rendered in lighter text next to the name).
 *
 * <p>Top-level classes are roots; their fields, constructors, methods, and nested
 * classes are children.  Method bodies are not recursed into — only class-level
 * members are shown.  Synthetic names ({@code this$0}, {@code <clinit>}, etc.)
 * are omitted.
 *
 * <p>Full ranges use the AST's end-position table ({@link JmlCompilationUnit#endPositions});
 * selection ranges locate the identifier name with a short forward scan from the
 * node start position.
 */
public class DocumentSymbolProvider {

    /**
     * Build a document-symbol tree for {@code ast}.
     *
     * @param ast     attributed {@link JmlCompilationUnit} from the {@link ASTCache}
     * @param source  full source text (for offset → line/col conversion)
     * @param jmlOnly if {@code true}, emit only JML-specific symbols (ghost, model) so
     *                the OpenJML outline complements rather than duplicates the Java
     *                outline provided by the Red Hat Java extension.  If {@code false},
     *                emit all symbols (full outline mode for editors without a competing
     *                Java provider).
     * @return top-level symbols (classes, enums, interfaces) with children
     */
    public static List<DocumentSymbol> fromAst(JmlCompilationUnit ast, String source,
                                                boolean jmlOnly) {
        int[] lineOffsets = buildLineOffsets(source);
        SymbolWalker walker = new SymbolWalker(ast, source, lineOffsets, jmlOnly);
        walker.scan(ast);
        return walker.roots;
    }

    /** Convenience overload — defaults to JML-only mode. */
    public static List<DocumentSymbol> fromAst(JmlCompilationUnit ast, String source) {
        return fromAst(ast, source, true);
    }

    // -----------------------------------------------------------------------
    // AST walker
    // -----------------------------------------------------------------------

    private static class SymbolWalker extends JmlTreeScanner {

        private final JmlCompilationUnit cu;
        private final String source;
        private final int[] lineOffsets;

        /** Top-level class symbols (roots of the outline tree). */
        final List<DocumentSymbol> roots = new ArrayList<>();

        /**
         * Stack of class symbols currently being built.  The top of the stack is
         * the innermost class whose members are being collected.
         */
        private final Deque<DocumentSymbol> classStack = new ArrayDeque<>();

        /**
         * Depth inside method/initializer bodies.  When {@code > 0} we are inside
         * a method or block — local variables and anonymous inner classes are skipped.
         */
        private int bodyDepth = 0;

        /** The name of the class at the top of the class stack (used for constructors). */
        private final Deque<String> classNameStack = new ArrayDeque<>();

        /**
         * When {@code true}, emit only JML-specific symbols (ghost, model) so the
         * OpenJML outline complements rather than duplicates a competing Java outline.
         * When {@code false}, emit all symbols for a full standalone outline.
         */
        private final boolean jmlOnly;

        SymbolWalker(JmlCompilationUnit cu, String source, int[] lineOffsets, boolean jmlOnly) {
            super(null);   // null context → AST_JML_MODE by default
            this.cu          = cu;
            this.source      = source;
            this.lineOffsets = lineOffsets;
            this.jmlOnly     = jmlOnly;
        }

        // ---- classes --------------------------------------------------------

        @Override
        public void visitClassDef(JCClassDecl tree) {
            if (tree.name == null || tree.pos < 0) return;
            String name = tree.name.toString();
            if (name.isEmpty()) return;

            // Anonymous / local classes inside method bodies are not shown.
            if (bodyDepth > 0) return;

            // Always create a class symbol and recurse so we can discover JML
            // members inside regular Java classes.  makeClassSymbol returns null
            // for non-JML classes; we use a placeholder in that case and decide
            // whether to keep it after recursion.
            DocumentSymbol sym = makeClassSymbol(tree);
            boolean isJmlClass = (sym != null);
            if (sym == null) {
                // Placeholder: create an undecorated symbol so visitVarDef /
                // visitMethodDef have a parent to attach JML children to.
                Range sel = nameRange(tree.pos, name);
                sym = new DocumentSymbol(name, SymbolKind.Class, fullRange(tree, sel), sel);
            }

            List<DocumentSymbol> parentList = classStack.isEmpty() ? roots : null;
            if (classStack.isEmpty()) roots.add(sym);
            else addChild(sym);
            classStack.push(sym);
            classNameStack.push(name);

            // JmlTreeScanner.visitClassDef (AST_JML_MODE) scans both:
            //   super.visitClassDef(that) → iterates defs (fields, methods, nested classes)
            //   scan(ms.clauses)          → iterates JML type-spec clauses (invariants, etc.)
            // This ensures ghost/model declarations in either location are visited.
            super.visitClassDef(tree);

            classNameStack.pop();
            classStack.pop();

            // In jmlOnly mode: drop plain Java classes that ended up with no JML
            // children — the Red Hat Java extension already covers them.
            if (jmlOnly && !isJmlClass) {
                boolean hasJmlChildren = sym.getChildren() != null && !sym.getChildren().isEmpty();
                if (!hasJmlChildren) {
                    if (classStack.isEmpty()) {
                        roots.remove(sym);
                    } else {
                        DocumentSymbol parent = classStack.peek();
                        if (parent.getChildren() != null) parent.getChildren().remove(sym);
                    }
                }
            }
        }

        // ---- methods / constructors -----------------------------------------

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (classStack.isEmpty() || bodyDepth > 0) return;
            if (tree.pos < 0) return;

            String rawName = tree.name != null ? tree.name.toString() : "";
            boolean isCtor = "<init>".equals(rawName);
            // Skip static initializers (<clinit>) and other synthetics.
            if (!isCtor && (rawName.isEmpty() || rawName.startsWith("<"))) return;

            String name = isCtor ? classNameStack.peek() : rawName;
            if (name == null || name.isEmpty()) return;
            SymbolKind kind = isCtor ? SymbolKind.Constructor : SymbolKind.Method;
            Range sel = nameRange(tree.pos, name);
            DocumentSymbol sym = new DocumentSymbol(name, kind,
                    fullRange(tree, sel), sel);
            if (jmlOnly && !setJmlDetail(sym, tree.mods)) return;  // skip non-JML members
            else if (!jmlOnly) setJmlDetail(sym, tree.mods);
            addChild(sym);

            // Do NOT recurse into the method body — local variables and
            // anonymous classes inside methods are not shown in the outline.
        }

        // ---- fields ---------------------------------------------------------

        @Override
        public void visitVarDef(JCVariableDecl tree) {
            if (classStack.isEmpty() || bodyDepth > 0) return;
            if (tree.name == null || tree.pos < 0) return;
            String name = tree.name.toString();
            if (name.isEmpty() || name.startsWith("this$") || name.startsWith("val$")) return;

            Range sel = nameRange(tree.pos, name);
            DocumentSymbol sym = new DocumentSymbol(name, SymbolKind.Field,
                    fullRange(tree, sel), sel);
            if (jmlOnly && !setJmlDetail(sym, tree.mods)) return;  // skip non-JML members
            else if (!jmlOnly) setJmlDetail(sym, tree.mods);
            addChild(sym);

            // Do NOT recurse into the field initializer.
        }

        // ---- blocks (initializers) ------------------------------------------

        /**
         * Static and instance initializer blocks live directly in {@code defs}.
         * Increment {@code bodyDepth} so that variable declarations inside them
         * are not mistakenly added as class-level members.
         */
        @Override
        public void visitBlock(JCBlock tree) {
            bodyDepth++;
            super.visitBlock(tree);
            bodyDepth--;
        }

        // ---- helpers --------------------------------------------------------

        private void addChild(DocumentSymbol sym) {
            DocumentSymbol parent = classStack.peek();
            if (parent == null) return;
            if (parent.getChildren() == null) parent.setChildren(new ArrayList<>());
            parent.getChildren().add(sym);
        }

        /** Returns null if the class is not a JML model class (should be skipped). */
        private DocumentSymbol makeClassSymbol(JCClassDecl tree) {
            String name = tree.name.toString();
            SymbolKind kind;
            if (tree.sym != null) {
                if (tree.sym.isEnum())           kind = SymbolKind.Enum;
                else if (tree.sym.isInterface()) kind = SymbolKind.Interface;
                else                             kind = SymbolKind.Class;
            } else {
                kind = SymbolKind.Class;
            }
            Range sel = nameRange(tree.pos, name);
            DocumentSymbol sym = new DocumentSymbol(name, kind,
                    fullRange(tree, sel), sel);
            if (tree instanceof JmlClassDecl jmlCd) {
                boolean isJml = setJmlDetail(sym, jmlCd.mods);
                if (jmlOnly && !isJml) return null;  // not a model class; filtered in jmlOnly mode
            } else if (jmlOnly) {
                return null;  // plain JCClassDecl — filtered in jmlOnly mode
            }
            return sym;
        }

        private Range fullRange(JCTree tree, Range selectionRange) {
            Position start = offsetToPos(tree.pos);
            int endOffset  = cu.endPositions != null
                    ? tree.getEndPosition(cu.endPositions) : -1;
            Position end = (endOffset > tree.pos) ? offsetToPos(endOffset) : start;
            // LSP requires selectionRange ⊆ fullRange.  Clamp both ends so
            // the invariant holds even when AST positions are imprecise (e.g.
            // JML ghost/model nodes parsed from comment text).
            if (posLe(selectionRange.getStart(), start)) {
                start = selectionRange.getStart();
            }
            if (posLe(end, selectionRange.getEnd())) {
                end = selectionRange.getEnd();
            }
            return new Range(start, end);
        }

        /** Returns true if a ≤ b in document order. */
        private static boolean posLe(Position a, Position b) {
            if (a.getLine() != b.getLine()) return a.getLine() < b.getLine();
            return a.getCharacter() <= b.getCharacter();
        }

        private Range nameRange(int nodePos, String name) {
            int searchEnd = Math.min(nodePos + 300, source.length() - name.length());
            for (int i = nodePos; i <= searchEnd; i++) {
                if (source.startsWith(name, i)) {
                    boolean okBefore = i == 0
                            || !Character.isJavaIdentifierPart(source.charAt(i - 1));
                    boolean okAfter  = (i + name.length() >= source.length())
                            || !Character.isJavaIdentifierPart(source.charAt(i + name.length()));
                    if (okBefore && okAfter) {
                        return new Range(offsetToPos(i), offsetToPos(i + name.length()));
                    }
                }
            }
            Position p = offsetToPos(nodePos);
            return new Range(p, p);
        }

        private Position offsetToPos(int offset) {
            if (offset <= 0) return new Position(0, 0);
            int lo = 0, hi = lineOffsets.length - 1;
            while (lo < hi) {
                int mid = (lo + hi + 1) / 2;
                if (lineOffsets[mid] <= offset) lo = mid;
                else hi = mid - 1;
            }
            return new Position(lo, offset - lineOffsets[lo]);
        }

        /**
         * Set the {@link DocumentSymbol#setDetail detail} to {@code "(ghost)"} or
         * {@code "(model)"} when the JML modifiers contain those keywords, and
         * return {@code true}.  Returns {@code false} for non-JML declarations so
         * callers can skip them (the Java outline from the Red Hat extension already
         * covers regular Java members; we only show JML additions here).
         *
         * <p>To switch to full-symbol mode (all Java + JML members in one outline),
         * change callers to ignore the return value and remove the {@code return} guards.
         */
        private static boolean setJmlDetail(DocumentSymbol sym,
                                             com.sun.tools.javac.tree.JCTree.JCModifiers mods) {
            if (!(mods instanceof JmlModifiers jmlMods)) return false;
            if (jmlMods.has(Modifiers.GHOST))  { sym.setDetail("(ghost)");  return true; }
            if (jmlMods.has(Modifiers.MODEL))  { sym.setDetail("(model)");  return true; }
            return false;
        }
    }

    // -----------------------------------------------------------------------
    // Line-offset table (shared utility)
    // -----------------------------------------------------------------------

    private static int[] buildLineOffsets(String source) {
        List<Integer> list = new ArrayList<>();
        list.add(0);
        for (int i = 0; i < source.length(); i++) {
            if (source.charAt(i) == '\n') list.add(i + 1);
        }
        int[] arr = new int[list.size()];
        for (int i = 0; i < arr.length; i++) arr[i] = list.get(i);
        return arr;
    }

    private DocumentSymbolProvider() {}
}
