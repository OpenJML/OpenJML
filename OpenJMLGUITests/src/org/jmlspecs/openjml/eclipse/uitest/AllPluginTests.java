package org.jmlspecs.openjml.eclipse.uitest;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * JUnit 4 test suite that runs all OpenJMLUI GUI tests in a single Eclipse
 * JVM invocation.
 *
 * <p>Running all classes together saves the dominant setup cost — Eclipse
 * startup and plugin initialisation — which would otherwise be paid once per
 * class when each class is launched as a separate process.
 *
 * <p>Order: MenuPresenceTest (menu wiring smoke-test, fast) → NatureTest
 * (Add/Remove nature) → FileIconTest → LspFeatureTest (Rename, Find References,
 * JML marker lifecycle — slowest because it starts the LSP server).
 *
 * <p>{@link InstallPluginTest} is intentionally NOT included here: it requires
 * a <em>pristine</em> Eclipse instance with OpenJML not yet installed, and must
 * be run first (before OpenJML is deployed).  Use {@code make run-install-test}.
 *
 * <p>The Makefile {@code PLUGIN_TEST_CLASSES} variable is derived from this
 * annotation at make-time, so adding/removing a class here automatically
 * updates the individual {@code run-plugin-tests} target.
 *
 * <p>To run from the Makefile: {@code make run-plugin-suite} (one JVM) or
 * {@code make run-plugin-tests} (one JVM per class, [PASS]/[FAIL] per class).
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    PreferencesPageTest.class,
    MenuPresenceTest.class,
    FileIconTest.class,
    NatureTest.class,
    LspFeatureTest.class
})
public class AllPluginTests {
    // Suite container — no methods needed
}
