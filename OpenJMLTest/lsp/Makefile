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
LSP4J_VERSION := 1.0.0
GSON_VERSION  := 2.11.0

## Classpath components
JUNITDIR  := $(LSPTEST)/../libs
JUNIT_CP  := $(JUNITDIR)/junit-4.13.2.jar:$(JUNITDIR)/hamcrest-core-1.3.jar:$(JUNITDIR)/junit-jupiter-api-5.5.2.jar:$(JUNITDIR)/apiguardian-api-1.1.0.jar:$(JUNITDIR)/opentest4j-1.3.0.jar
## LSP4J jars needed at compile time (for LSP Diagnostic types) and at runtime.
## Gson is intentionally excluded: jdk.compiler bundles Gson internally, and putting
## a separate Gson jar on the classpath creates a split-package conflict that the JVM
## rejects.  The GSON_EXPORTS flags (below) expose jdk.compiler's Gson instead.
LSP4J_CP  := $(LSPROOT)/libs/org.eclipse.lsp4j-$(LSP4J_VERSION).jar:$(LSPROOT)/libs/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar
LSP_JAR   := $(LSPROOT)/build/openjml-lsp.jar

## jdk.compiler bundles Gson internally but does not export its packages.
## Export all Gson packages so that LSP4J (and our RawLspClient / WorkspaceService)
## can access jdk.compiler's Gson at both compile and run time.
## This mirrors the approach in OpenJMLlsp/openjml-lsp.
GSON_EXPORTS := \
  --add-exports=jdk.compiler/com.google.gson=ALL-UNNAMED \
  --add-exports=jdk.compiler/com.google.gson.annotations=ALL-UNNAMED \
  --add-exports=jdk.compiler/com.google.gson.internal=ALL-UNNAMED \
  --add-exports=jdk.compiler/com.google.gson.internal.bind=ALL-UNNAMED \
  --add-exports=jdk.compiler/com.google.gson.internal.bind.util=ALL-UNNAMED \
  --add-exports=jdk.compiler/com.google.gson.internal.reflect=ALL-UNNAMED \
  --add-exports=jdk.compiler/com.google.gson.internal.sql=ALL-UNNAMED \
  --add-exports=jdk.compiler/com.google.gson.reflect=ALL-UNNAMED \
  --add-exports=jdk.compiler/com.google.gson.stream=ALL-UNNAMED

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
	   $(NJAVAC) $$OPENJML_EXPORTS $(GSON_EXPORTS) \
	     -cp $(LSP_JAR):$(LSP4J_CP):$(JUNIT_CP) \
	     -d $(CLASSES) \
	     $(INFRA_SRCS) $(TEST_SRCS) )

## Run the LSP tests with JUnit's built-in console runner.
run-tests: compile
	@( cd $(LSPTEST); \
	   . $(SRC)/setup-exports; \
	   OPENJML_INSTALL="$(BUILDJDK)" \
	   OPENJML_SPECS="$(SRC)/../../Specs/specs" \
	   OPENJML_SOLVERS="$(SRC)/../../Solvers" \
	   "$(NJAVA)" $$OPENJML_JVM $$OPENJML_EXPORTS $(GSON_EXPORTS) \
	     -Dlsp.testdata=$(LSPTEST)/testdata \
	     -cp "$(CLASSES):$(LSP_JAR):$(LSP4J_CP):$(JUNIT_CP)" \
	     org.junit.runner.JUnitCore \
	     org.openjml.lsp.test.DiagnosticsTest \
	     org.openjml.lsp.test.EscStatusTest \
	     org.openjml.lsp.test.MultiFileEscTest \
	     org.openjml.lsp.test.LspProtocolTest )

clean: .FORCE
	rm -rf $(LSPTEST)/build

.FORCE:
