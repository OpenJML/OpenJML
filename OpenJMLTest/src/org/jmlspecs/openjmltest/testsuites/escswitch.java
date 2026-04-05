package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.MockJavaFileObject;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.util.List;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escswitch extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--source", "21");
        addOptions("--enable-preview", "--enable-preview");
        expectedExit = 0;
    }

    /** Minimal sealed Result type exercising record-pattern switch and binding-pattern switch. */
    static final String RESULT_SOURCE = """
            package com.example;

            public sealed interface Result<T, E> permits Result.Ok, Result.Err {

                record Ok<T, E>(T value) implements Result<T, E> {}
                record Err<T, E>(E error) implements Result<T, E> {}

                static <T, E extends Throwable> T getChecked(Result<T, E> result) throws E {
                    return switch (result) {
                        case Ok<T, E>(var value) -> value;
                        case Err<T, E>(var error) -> throw error;
                    };
                }

                static <T, E> T get(Result<T, E> result) {
                    return switch (result) {
                        case Ok<T, E> ok -> ok.value();
                        default -> null;
                    };
                }
            }
            """;

    @Test
    public void testResultRegression() throws Exception {
        addOptions("--check-feasibility=none");
        addOptions("--method=getChecked");
        JavaFileObject result = new MockJavaFileObject(
                "com/kevel/util/Result.java",
                RESULT_SOURCE);
        int ex = main.compile(new String[]{}, List.of(result)).exitCode;
        String diags = diagnosticsToString(collector.getDiagnostics());
        assertFalse("Did not expect a catastrophic internal error:\n" + diags,
                diags.contains("A catastrophic JML internal error occurred"));
        assertFalse("Did not expect the previous concat regression:\n" + diags,
                diags.contains("Could not find the concat method"));
        assertFalse("Did not expect the previous null-arg regression:\n" + diags,
                diags.contains("Cannot read field \"type\" because \"a\" is null"));
        assertFalse("Did not expect the previous regression to trigger any internal JML error:\n" + diags,
                diags.contains("An internal JML error occurred"));
        assertTrue("Expected either a clean compile or only the known missing-prover failure, got:\n" + diags,
                ex == 0 || diags.contains("The executable for prover z3_4_3 is not specified"));
    }
}
