# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Basic rules

Claude must never run 'git push

Claude must never run 'git commit' or other commands that change the git history without explicit permission.

Claude must never run any 'git' commands that change files without explicit permission.

## Project Overview

OpenJML is a tool for Java that processes JML (Java Modeling Language) specifications embedded in Java source code. It extends OpenJDK 21 (jdk-21-ga branch) by adding JML parsing, type-checking, static checking (ESC via SMT solvers), and runtime assertion checking (RAC).

The project requires several **sibling repositories** cloned under a common parent directory (e.g., `~/projects/OpenJML21/`):
- `OpenJML/` — this repo (contains `OpenJMLsrc/`, `OpenJMLTest/`, `OpenJMLlsp/`, `OpenJMLUI/`, `OpenJMLFeature/`, `OpenJMLUpdateSite/`, `OpenJMLGUITests/`)
- `JMLAnnotations/` — JML annotation types
- `Specs/` — JML specifications for the Java standard library
- `Solvers/` — bundled SMT solvers (z3, etc.)
- `openjml.github.io/` — website and tutorial files
- `OpenJMLDemo/` — demo programs

## Repository Structure

```
OpenJML/
  OpenJMLsrc/       # Modified OpenJDK 21 source (the main compiler/tool source)
    src/
      java.base/    # Contains org.jmlspecs.annotation.* and org.jmlspecs.runtime.*
      jdk.compiler/ # Contains all OpenJML additions to the compiler
        .../com/sun/tools/javac/
          parser/   # JmlParser, JmlScanner, JmlTokenizer, JmlToken, etc.
          comp/     # JmlAttr, JmlEnter, JmlFlow, JmlCheck, JmlResolve, etc.
          code/     # JmlTypes, etc.
          main/     # JmlCompiler
        .../org/jmlspecs/openjml/
          Main.java         # Tool entry point
          JmlTree.java      # JML AST node definitions
          JmlSpecs.java     # Specification management
          JmlOptions.java   # Option handling
          IJmlClauseKind.java # Extension mechanism for clauses
          Extensions.java   # Registry for JML extensions
          JmlExtension.java # Marker for extension classes
          ext/              # All JML clause/expression extensions
          esc/              # Extended Static Checking (SMT-based)
            JmlEsc.java         # ESC driver
            JmlAssertionAdder.java # Converts specs to assertions
            BasicBlocker2.java  # Basic block form
            MethodProverSMT.java # Invokes SMT solver
            SMTTranslator.java  # Translates to SMT-LIB
          visitors/         # AST visitor infrastructure
          proverinterface/  # IProver, ProverResult interfaces
        .../org/openjml/
          IAPI.java / API.java  # Programmatic API
    openjml         # Shell script: runs openjml (the javac equivalent)
    openjml-java    # Shell script: runs java with OpenJML runtime
    openjml-run     # Shell script: runs a compiled RAC program
    setup-vars      # Sourced script: sets BINJAVA, BINJAVAC, etc.
    setup-exports   # Sourced script: sets OPENJML_EXPORTS (module --add-exports)
    Makefile        # Build targets (wraps OpenJDK build + OpenJML targets)
    jmlruntime.jar  # Runtime library for RAC (built artifact)
    build/          # Build output (created by make)

  OpenJMLTest/      # JUnit test suite for OpenJML
    src/org/jmlspecs/openjmltest/
      JmlTestSuite.java   # Base class for all tests
      TCBase.java         # Type-check tests base
      EscBase.java        # ESC tests base
      RacBase.java        # RAC tests base
      EscBaseFiles.java   # File-based ESC tests
      testsuites/         # Individual test classes (one per feature area)
    test/                 # Input Java files and expected outputs for file-based tests
    unittests/            # Scripts for running tests
      runpar              # Run all test suites in parallel (default 5 jobs)
      runseq              # Run sequentially (JOBS=0 runpar)
      runtests            # Run specific named test suite(s)
    libs/                 # JUnit jars
    Makefile              # Test targets

  OpenJMLlsp/         # LSP server for OpenJML; also contains the VSCode extension
  OpenJMLUI/          # Eclipse LSP UI plugin (LSP client connecting to openjml-lsp)
  OpenJMLFeature/     # Eclipse feature descriptor (wraps OpenJMLUI for the update site)
  OpenJMLUpdateSite/  # Eclipse p2 update site artifacts (published to openjml.org/eclipse-update-site)
  OpenJMLGUITests/    # SWTBot-based automated GUI tests of the OpenJMLUI Eclipse plugin
```

## Building

The build system is OpenJDK's standard make-based system. All build commands run from `OpenJMLsrc/`:

```bash
# Initial setup (once per checkout or after clean)
cd OpenJMLsrc
bash configure

# Build the OpenJML compiler/JDK (development build)
make openjml
# Equivalent to: NOJML=1 WSLENV="${WSLENV:+$WSLENV:}NOJML" make  (NOJML=1 disables JML checking; WSLENV forwards it to Windows PE processes)

# Build the runtime jar (needed for RAC testing)
make jmlruntime.jar

# Full release build (includes version, annotations, tutorial, packaging)
make release

# Update JML annotation files from sibling JMLAnnotations repo
make annotation
```

After a successful build, the built JDK is at `OpenJMLsrc/build/*/jdk/`.

## Running OpenJML (Development Environment)

From `OpenJMLsrc/`, use the wrapper scripts:

```bash
# Type-check with JML
./openjml --check MyFile.java

# Extended static checking
./openjml --esc MyFile.java

# Runtime assertion checking (compile)
./openjml --rac MyFile.java

# Run a RAC-compiled program
./openjml-java -cp . MyClass

# Check version
./openjml --version
```

Environment variables that control behavior:
- `OPENJML_INSTALL` — path to the OpenJML installation (auto-set by scripts)
- `OPENJML_SPECS` — path to the specs directory (defaults to `../../Specs/specs`)
- `OPENJML_SOLVERS` — path to solvers directory (defaults to `../../Solvers`)
- `OPENJML_JVM` — extra JVM options (optional)

The `setup-exports` file sets `OPENJML_EXPORTS`, the `--add-exports` flags needed when using OpenJML programmatically (the internal compiler APIs are heavily encapsulated by the Java module system).

## Running Tests

The working directory for all test execution should be `OpenJMLTest/`.

```bash
# Run all test suites in parallel (5 concurrent jobs by default)
cd OpenJMLTest/unittests
./runpar

# Run with a different number of parallel jobs
JOBS=8 ./runpar

# Run a single named test suite
./runtests escJML

# Run multiple specific test suites
./runtests escJML lblexpression racJML

# Run test suites sequentially
./runseq

# From OpenJMLTest Makefile:
make unittests-par    # parallel
make unittests-seq    # sequential
make release-tests    # smoke tests on current build
make json-tests       # JSON output/input tests
```

Test logs are written to `OpenJMLTest/unittests/log-<suitename>`.

## Test Architecture

Tests are JUnit 4 classes organized by feature area in `OpenJMLTest/src/org/jmlspecs/openjmltest/testsuites/`. Each test suite inherits from a base class:

- **`TCBase`** — type-checking tests: compile a string of Java/JML source and compare diagnostics
- **`EscBase`** — ESC tests: run static checking on inline source and compare messages
- **`EscBaseFiles`** — ESC tests using files from `OpenJMLTest/test/`
- **`RacBase`** — RAC tests: compile and execute a Java program, compare runtime output

Test methods typically call `helpTC(...)`, `helpEsc(...)`, or `helpRac(...)` with inline Java source strings and expected diagnostic messages (file path, line number, column number).

The `unittests/runtests` script compiles test framework files via `make unittestframework` in `OpenJMLTest/unittests/`, then runs them using the custom `OpenJMLTestRunner`.

## Key Architectural Patterns

**Compiler Integration**: OpenJML is implemented as extensions to OpenJDK's `javac`. Rather than creating a separate tool, JML processing is integrated into javac's compilation phases:
- Lexing/parsing: `JmlScanner`/`JmlTokenizer`/`JmlParser` extend their javac counterparts
- Attribution (type-checking): `JmlAttr` extends `Attr`
- Compilation: `JmlCompiler` extends `JavaCompiler`
- Each class is registered via javac's `Context` dependency injection system

**Extension Mechanism**: JML clause kinds and expressions are defined in `org.jmlspecs.openjml.ext/` by subclassing `JmlExtension`. Each extension registers one or more `IJmlClauseKind` instances via `Extensions.allKinds`. The `Extensions` class discovers them at startup via reflection.

**ESC Pipeline**: `JmlEsc` → `JmlAssertionAdder` (converts specs to Java assertions) → `BasicBlocker2` (basic block form) → `SMTTranslator` (SMT-LIB format) → `MethodProverSMT` (invokes external SMT solver, default z3).

**Module System**: Because OpenJML extends OpenJDK internals, running it programmatically requires many `--add-exports` flags (see `setup-exports`). The `OPENJML_EXPORTS` variable captures these. Test compilation and execution must include these flags.

**Specs Separation**: JML specs for the Java standard library live in the sibling `Specs/` repository, not in this repo. The `--specs-path` option points OpenJML to them.
