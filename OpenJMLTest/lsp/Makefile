mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir  := $(dir $(mkfile_path))
LSPTEST     := $(patsubst %/,%,$(mkfile_dir))

## Sibling directories
SRC      := $(LSPTEST)/../../OpenJMLsrc
LSPROOT  := $(LSPTEST)/../../OpenJMLlsp
BUILDJDK := $(firstword $(wildcard $(SRC)/build/*/jdk))
NJAVAC   := $(BUILDJDK)/bin/javac
NJAVA    := $(BUILDJDK)/bin/java

## LSP4J version must match the one in OpenJMLlsp/Makefile
LSP4J_VERSION := 0.21.1
GSON_VERSION  := 2.10.1

## Classpath components
JUNITDIR  := $(LSPTEST)/../libs
JUNIT_CP  := $(JUNITDIR)/junit-4.13.2.jar:$(JUNITDIR)/hamcrest-core-1.3.jar:$(JUNITDIR)/junit-jupiter-api-5.5.2.jar:$(JUNITDIR)/apiguardian-api-1.1.0.jar:$(JUNITDIR)/opentest4j-1.3.0.jar
## LSP4J jars are needed at compile time (for LSP Diagnostic types) and at run
## time (for type references).  The Gson jar is included but Gson classes are
## never loaded at runtime because tests call CheckRunner directly rather than
## going through the LSP4J JSON-RPC Launcher — avoiding the conflict between
## the Gson jar and the Gson 2.11.0 bundled inside jdk.compiler.
LSP4J_CP  := $(LSPROOT)/libs/org.eclipse.lsp4j-$(LSP4J_VERSION).jar:$(LSPROOT)/libs/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar:$(LSPROOT)/libs/gson-$(GSON_VERSION).jar
LSP_JAR   := $(LSPROOT)/build/openjml-lsp.jar

## Build output
CLASSES := $(LSPTEST)/build/classes

## Source and test trees (infrastructure in src/, test cases in test/)
INFRA_SRCS := $(shell find $(LSPTEST)/src  -name '*.java')
TEST_SRCS  := $(shell find $(LSPTEST)/test -name '*.java')

.PHONY: all compile run-tests clean .FORCE

all: run-tests

## Build the LSP server jar if not already up to date
$(LSP_JAR): .FORCE
	$(MAKE) -C $(LSPROOT) jar

## Compile test infrastructure and test cases.
## NOJML= disables JML processing in the extended javac so that spec-path
## lookup is skipped during compilation.
compile: $(LSP_JAR)
	@mkdir -p $(CLASSES)
	@( . $(SRC)/setup-exports; \
	   NOJML= \
	   $(NJAVAC) $$OPENJML_EXPORTS \
	     -cp $(LSP_JAR):$(LSP4J_CP):$(JUNIT_CP) \
	     -d $(CLASSES) \
	     $(INFRA_SRCS) $(TEST_SRCS) )

## Run the LSP tests with JUnit's built-in console runner.
## Tests call CheckRunner directly; the LSP4J JSON-RPC Launcher is not used,
## so Gson classes are never loaded and the jdk.compiler Gson conflict is avoided.
run-tests: compile
	@( cd $(LSPTEST); \
	   . $(SRC)/setup-exports; \
	   OPENJML_INSTALL="$(BUILDJDK)" \
	   OPENJML_SPECS="$(SRC)/../../Specs/specs" \
	   OPENJML_SOLVERS="$(SRC)/../../Solvers" \
	   "$(NJAVA)" $$OPENJML_JVM $$OPENJML_EXPORTS \
	     -cp "$(CLASSES):$(LSP_JAR):$(LSP4J_CP):$(JUNIT_CP)" \
	     org.junit.runner.JUnitCore \
	     org.openjml.lsp.test.DiagnosticsTest )

clean: .FORCE
	rm -rf $(LSPTEST)/build

.FORCE:
