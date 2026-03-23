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
 * (Add/Remove nature) → ActionTest (command dispatch and argument extraction) →
 * MarkersTest (JML marker lifecycle, needs OpenJML to run and is the slowest).
 *
 * <p>To run from the Makefile: {@code make run-plugin-tests}<br>
 * To run individual classes:   {@code make run-menu-test}, {@code make run-nature-test}, etc.
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
