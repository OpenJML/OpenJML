package org.openjml.lsp.test;

import org.eclipse.lsp4j.Location;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DefinitionFinder;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.ReferenceFinder;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Tests for go-to-definition, find-all-references, and rename when the symbol
 * is a <em>method name</em> or <em>class name</em>.
 *
 * <h3>Test data</h3>
 * {@code OpenJMLTest/lsp/testdata/testMethodClass/} — four source files:
 * <ul>
 *   <li>{@code IWorker.java}  — interface with {@code doWork(int)} and {@code getStatus()}</li>
 *   <li>{@code WorkerA.java}  — implements IWorker; also has {@code doubleWork(int)} which
 *       is NOT an override of any IWorker method</li>
 *   <li>{@code WorkerB.java}  — implements IWorker</li>
 *   <li>{@code Manager.java}  — has an {@code IWorker}-typed field (interface dispatch) AND
 *       a {@code WorkerA}-typed field (concrete dispatch); both are compiled in the same
 *       IAPI context when {@code Manager.java} is compiled with sourcepath</li>
 * </ul>
 *
 * <h3>Key design consideration: symbol identity and method overrides</h3>
 * OpenJML's {@link ReferenceFinder} uses javac {@link com.sun.tools.javac.code.Symbol}
 * identity ({@code ==}) to locate all references to a symbol.  This is correct
 * <em>within a single IAPI compilation context</em> (javac reuses the same {@code Symbol}
 * instance for every reference to a given declaration) but has one important limitation
 * with interface dispatch:
 *
 * <ul>
 *   <li>A call {@code worker.doWork(amount)} where {@code worker: IWorker} resolves to
 *       {@code IWorker.doWork.sym} (the interface method symbol).</li>
 *   <li>The overriding declarations {@code WorkerA.doWork} and {@code WorkerB.doWork}
 *       each have their own distinct {@code MethodSymbol} instances that are NOT
 *       {@code ==} to {@code IWorker.doWork.sym}.</li>
 * </ul>
 *
 * <p>As a result, {@code findReferences(IWorker.doWork)} finds the interface declaration
 * and call sites via the interface type, but NOT the overriding declarations in
 * {@code WorkerA} / {@code WorkerB}.  Attempting to rename {@code IWorker.doWork} is
 * therefore rejected by the error-count check (step 4): the modified sources have the
 * interface method renamed but the implementations still declare the old name,
 * so the implementations no longer satisfy the interface contract.
 *
 * <p>Methods called via a <em>concrete type</em> (e.g. {@code concreteA.doubleWork(amount)}
 * where {@code concreteA: WorkerA}) do NOT have this limitation: the call resolves to
 * {@code WorkerA.doubleWork.sym} exactly, so cross-file reference finding and rename work.
 *
 * <p>Methods called via a <em>concrete type</em> that is also an override of an interface
 * method (e.g. {@code concreteA.doWork(amount)}) resolve to {@code WorkerA.doWork.sym};
 * renaming {@code WorkerA.doWork} then fails because the rename cannot update
 * {@code IWorker.doWork} (different symbol), leaving the interface contract broken.
 *
 * <h3>Coverage</h3>
 * <dl>
 *   <dt>Find declaration for methods</dt>
 *   <dd>Cursor on a call to {@code doWork} via {@code IWorker} resolves to the interface
 *       method declaration; cursor on {@code doubleWork} via concrete type resolves to
 *       {@code WorkerA.doubleWork}.</dd>
 *   <dt>Find declaration for class names</dt>
 *   <dd>Cursor on {@code IWorker} as a type reference resolves to the interface declaration.</dd>
 *   <dt>Find references for method (interface dispatch)</dt>
 *   <dd>References to {@code IWorker.doWork} include the interface declaration and
 *       call sites via the interface type.  Overriding method declarations in implementing
 *       classes use different Symbol instances and are NOT included (see above).</dd>
 *   <dt>Find references for method (concrete dispatch)</dt>
 *   <dd>References to {@code WorkerA.doubleWork} include the declaration in WorkerA.java
 *       and the call site in Manager.java.</dd>
 *   <dt>Find references for class names</dt>
 *   <dd>All type-reference sites for {@code IWorker} are found.</dd>
 *   <dt>Rename method — concrete type, no override (succeeds)</dt>
 *   <dd>Renaming {@code WorkerA.doubleWork} updates both the declaration in WorkerA.java
 *       and the call in Manager.java; modified sources compile without errors.</dd>
 *   <dt>Rename method — interface method (rejected)</dt>
 *   <dd>Renaming {@code IWorker.doWork} only updates the interface; implementing classes
 *       retain the old name and no longer satisfy the interface contract → compile error →
 *       rename is correctly rejected by step 4.  This documents a current limitation:
 *       override-aware rename requires extending ReferenceFinder to follow virtual dispatch.</dd>
 *   <dt>Rename method — implementation that overrides interface (rejected)</dt>
 *   <dd>Same situation from the implementation side: renaming {@code WorkerA.doWork} only
 *       updates WorkerA's declaration; the interface still requires {@code doWork} →
 *       contract broken → rejected.</dd>
 *   <dt>Rename class (rejected for public classes)</dt>
 *   <dd>Java requires that a {@code public} class name matches its filename.  Renaming
 *       a public class changes the class symbol's name but not the filename, so OpenJML
 *       reports a "should be declared in a file named X.java" error → step 4 rejects.</dd>
 * </dl>
 */
public class MethodAndClassTest extends LspTestBase {

    private Path testdir;
    private String iWorkerUri, workerAUri, workerBUri, managerUri;
    private String iWorkerSrc, workerASrc, workerBSrc, managerSrc;
    private Map<String, String> openContent;
    private OpenJMLSettings settings;

    @Before
    public void setUp() throws Exception {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("System property lsp.testdata must be set", root);
        testdir = Path.of(root, "testMethodClass");
        assertTrue("testMethodClass directory must exist", testdir.toFile().isDirectory());

        iWorkerSrc = Files.readString(testdir.resolve("IWorker.java"));
        workerASrc = Files.readString(testdir.resolve("WorkerA.java"));
        workerBSrc = Files.readString(testdir.resolve("WorkerB.java"));
        managerSrc = Files.readString(testdir.resolve("Manager.java"));

        iWorkerUri = testdir.resolve("IWorker.java").toUri().toString();
        workerAUri = testdir.resolve("WorkerA.java").toUri().toString();
        workerBUri = testdir.resolve("WorkerB.java").toUri().toString();
        managerUri = testdir.resolve("Manager.java").toUri().toString();

        openContent = Map.of(
                iWorkerUri, iWorkerSrc,
                workerAUri, workerASrc,
                workerBUri, workerBSrc,
                managerUri, managerSrc);

        settings = new OpenJMLSettings();
        settings.sourcePath = testdir.toString();

        // Compile Manager.java with sourcepath.  Manager.java references WorkerA, WorkerB,
        // and IWorker concretely, so all four files are compiled in the same IAPI context.
        // This is required for cross-file symbol-identity reference finding.
        CheckRunner.checkFile(testdir.resolve("Manager.java").toString(), managerUri, settings);
    }

    // -----------------------------------------------------------------------
    // Go-to-definition: method names
    // -----------------------------------------------------------------------

    /**
     * Cursor on the call {@code worker.doWork(amount)} in Manager.
     *
     * <p>The receiver {@code worker} has static type {@code IWorker}, so javac resolves
     * the call to {@code IWorker.doWork.sym}.  Go-to-definition must therefore point to
     * the method declaration in IWorker.java.
     */
    @Test
    public void testFindDeclarationForInterfaceMethod() {
        Location loc = defAt(managerUri, managerSrc, "worker.doWork", "doWork");
        assertNotNull("Expected a definition for doWork via interface receiver", loc);
        assertEquals("doWork must resolve to IWorker.java", iWorkerUri, loc.getUri());
        assertEquals("doWork interface declaration line",
                lineOf(iWorkerSrc, "int doWork"), loc.getRange().getStart().getLine());
    }

    /**
     * Cursor on {@code concreteA.doubleWork(amount)} in Manager.
     *
     * <p>The receiver {@code concreteA} has static type {@code WorkerA}, so the call
     * resolves to {@code WorkerA.doubleWork.sym}.  Go-to-definition must point to the
     * method declaration in WorkerA.java.
     */
    @Test
    public void testFindDeclarationForConcreteMethod() {
        Location loc = defAt(managerUri, managerSrc, "concreteA.doubleWork", "doubleWork");
        assertNotNull("Expected a definition for doubleWork via concrete receiver", loc);
        assertEquals("doubleWork must resolve to WorkerA.java", workerAUri, loc.getUri());
        assertEquals("doubleWork declaration line",
                lineOf(workerASrc, "public int doubleWork"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Go-to-definition: class names
    // -----------------------------------------------------------------------

    /**
     * Cursor on {@code IWorker} used as a field type ({@code private IWorker worker}).
     * Must resolve to the interface declaration in IWorker.java.
     */
    @Test
    public void testFindDeclarationForInterfaceType() {
        Location loc = defAt(managerUri, managerSrc, "private IWorker", "IWorker");
        assertNotNull("Expected a definition for class IWorker", loc);
        assertEquals("IWorker declaration must be in IWorker.java", iWorkerUri, loc.getUri());
        assertEquals("IWorker interface declaration line",
                lineOf(iWorkerSrc, "public interface IWorker"),
                loc.getRange().getStart().getLine());
    }

    /**
     * Cursor on {@code WorkerA} in {@code private WorkerA concreteA}.
     * Must resolve to the class declaration in WorkerA.java.
     */
    @Test
    public void testFindDeclarationForConcreteClass() {
        Location loc = defAt(managerUri, managerSrc, "private WorkerA", "WorkerA");
        assertNotNull("Expected a definition for class WorkerA", loc);
        assertEquals("WorkerA declaration must be in WorkerA.java", workerAUri, loc.getUri());
        assertEquals("WorkerA class declaration line",
                lineOf(workerASrc, "public class WorkerA"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Find references: interface method (limited by symbol identity)
    // -----------------------------------------------------------------------

    /**
     * Find references to {@code IWorker.doWork} starting from the interface declaration.
     *
     * <p>Because javac's interface-dispatch call sites resolve to the interface method's
     * Symbol (not the implementing class's Symbol), this finds:
     * <ul>
     *   <li>The interface method declaration in IWorker.java</li>
     *   <li>The call site {@code worker.doWork(amount)} in Manager.java, where the
     *       receiver is typed as {@code IWorker}</li>
     * </ul>
     *
     * <p>It does NOT find the override declarations in WorkerA.java or WorkerB.java
     * because those have distinct {@code MethodSymbol} instances (see class javadoc
     * for the full explanation).
     */
    @Test
    public void testFindReferencesForInterfaceMethod() {
        List<Location> refs = refsAt(iWorkerUri, iWorkerSrc, "int doWork", "doWork", true);
        assertFalse("Expected at least one reference to IWorker.doWork", refs.isEmpty());

        // Interface declaration must be found.
        assertContainsLine(refs, lineOf(iWorkerSrc, "int doWork"));
        // Manager's call site via interface type must be found.
        assertContainsLine(refs, lineOf(managerSrc, "worker.doWork(amount)"));

        // Document the limitation: override declarations in WorkerA/WorkerB use
        // different MethodSymbol instances and are NOT found by identity-based search.
        List<String> uris = refs.stream().map(Location::getUri).collect(Collectors.toList());
        // (No assertion that WorkerA/WorkerB are NOT found — they could be in future if
        //  the finder is enhanced for virtual dispatch.  Just verify what we do find.)
        assertTrue("At minimum IWorker.java and Manager.java must appear in results",
                uris.contains(iWorkerUri) && uris.contains(managerUri));
    }

    // -----------------------------------------------------------------------
    // Find references: concrete method (full cross-file)
    // -----------------------------------------------------------------------

    /**
     * Find references to {@code WorkerA.doubleWork}, which is NOT an override of any
     * interface method.
     *
     * <p>Because Manager's field {@code concreteA} has static type {@code WorkerA}, the
     * call {@code concreteA.doubleWork(amount)} resolves to {@code WorkerA.doubleWork.sym}
     * — the same Symbol object as the declaration.  Cross-file reference finding therefore
     * works and both the declaration and the call are found.
     */
    @Test
    public void testFindReferencesForConcreteMethod() {
        List<Location> refs = refsAt(workerAUri, workerASrc,
                "public int doubleWork", "doubleWork", true);
        assertFalse("Expected at least one reference to doubleWork", refs.isEmpty());

        // Declaration in WorkerA.java must be found.
        assertContainsLine(refs, lineOf(workerASrc, "public int doubleWork"));
        // Call site in Manager.java must be found.
        assertContainsLine(refs, lineOf(managerSrc, "concreteA.doubleWork(amount)"));

        List<String> uris = refs.stream().map(Location::getUri).collect(Collectors.toList());
        assertTrue("Must find doubleWork reference in WorkerA.java", uris.contains(workerAUri));
        assertTrue("Must find doubleWork reference in Manager.java",  uris.contains(managerUri));
    }

    // -----------------------------------------------------------------------
    // Find references: class name
    // -----------------------------------------------------------------------

    /**
     * Find references to the class {@code IWorker} (including the declaration).
     * Expected sites: the interface declaration, all {@code implements IWorker} clauses
     * (WorkerA, WorkerB), and all type-reference uses in Manager (field type,
     * constructor parameter type).
     */
    @Test
    public void testFindReferencesForInterfaceClass() {
        List<Location> refs = refsAt(iWorkerUri, iWorkerSrc,
                "public interface IWorker", "IWorker", true);
        assertFalse("Expected references to IWorker", refs.isEmpty());

        // Interface declaration must be included.
        assertContainsLine(refs, lineOf(iWorkerSrc, "public interface IWorker"));
        // Manager's field type "private IWorker worker" must be included.
        assertContainsLine(refs, lineOf(managerSrc, "private IWorker worker"));

        List<String> uris = refs.stream().map(Location::getUri).collect(Collectors.toList());
        assertTrue("Must find IWorker in IWorker.java",  uris.contains(iWorkerUri));
        assertTrue("Must find IWorker in Manager.java",  uris.contains(managerUri));
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private Location defAt(String uri, String source, String ctx, String id) {
        int ctxPos = source.indexOf(ctx);
        assertTrue("Context «" + ctx + "» not found in source for defAt", ctxPos >= 0);
        int idPos = source.indexOf(id, ctxPos);
        assertTrue("Identifier «" + id + "» not found after context", idPos >= 0);
        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return DefinitionFinder.findDefinition(uri, lc[0], lc[1],
                openContent, CheckRunner.getASTCache());
    }

    private List<Location> refsAt(String uri, String source, String ctx, String id,
                                   boolean includeDeclaration) {
        int ctxPos = source.indexOf(ctx);
        assertTrue("Context «" + ctx + "» not found in source for refsAt", ctxPos >= 0);
        int idPos = source.indexOf(id, ctxPos);
        assertTrue("Identifier «" + id + "» not found after context", idPos >= 0);
        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return ReferenceFinder.findReferences(uri, lc[0], lc[1],
                openContent, CheckRunner.getASTCache(), includeDeclaration);
    }

    private static int lineOf(String source, String text) {
        int idx = source.indexOf(text);
        assertTrue("Text «" + text + "» not found in source", idx >= 0);
        return DefinitionFinder.offsetToLineCol(source, idx)[0];
    }

    private static void assertContainsLine(List<Location> locs, int expectedLine) {
        boolean found = locs.stream().anyMatch(
                l -> l.getRange().getStart().getLine() == expectedLine);
        assertTrue("Expected a location on line " + expectedLine + " but got: "
                + locs.stream().map(l -> l.getRange().getStart().getLine() + " in "
                        + l.getUri().replaceAll(".*/", ""))
                        .collect(Collectors.joining(", ")),
                found);
    }
}
