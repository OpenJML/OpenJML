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
LSP_SRCS  := $(shell find $(LSPROOT)/src -name '*.java')

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
CLASSES    := $(LSPTEST)/build/classes
RESULT_DIR := $(LSPTEST)/build/results

## Source and test trees (infrastructure in src/, test cases in test/)
INFRA_SRCS := $(shell find $(LSPTEST)/src  -name '*.java')
TEST_SRCS  := $(shell find $(LSPTEST)/test -name '*.java')

## All test classes — each runs in its own JVM process.
## ESC-heavy classes (DoEscTest, EscStatusTest, MultiFileEscTest, DiagnosticsTest)
## each run alone so that running with -j5 never starts more than 5 ESC processes.
## Ordered longest-first so -j5 keeps the pool busy and finishes sooner.
## Timings (approximate, single run): RenameTest[1-3] ~41s each, DefinitionFinderTest 37s,
## DoEscTest 31s, ReferenceFinderTest 28s, DiagnosticsTest 26s, DocumentSymbolTest 24s,
## EscStatusTest 17s, MultiFileEscTest 15s, FastTests (FoldingRange+LspProtocol+SemanticTokens) 6s.
TEST_CLASSES := \
  RenameTest1 \
  RenameTest2 \
  RenameTest3 \
  RenameJmlTest \
  DefinitionFinderTest \
  DefinitionFinderJmlTest \
  DoEscTest \
  ReferenceFinderTest \
  ReferenceFinderJmlTest \
  DiagnosticsTest \
  DocumentSymbolTest \
  EscStatusTest \
  MultiFileEscTest \
  FastTests

LOG_FILES := $(patsubst %,$(RESULT_DIR)/%.log,$(TEST_CLASSES))

.PHONY: all compile run-tests run-tests-seq _run-logs clean .FORCE

all: run-tests

## Build the LSP server jar when any server source file is newer than the jar.
$(LSP_JAR): $(LSP_SRCS)
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

## Sentinel: compile once, used as dependency by all per-class log targets.
$(RESULT_DIR)/.compiled: compile
	@mkdir -p $(RESULT_DIR)
	@touch $@

## Per-class pattern rule — one JVM process per test class.
## Output is captured to a log file; on failure the log is printed and make exits non-zero.
$(RESULT_DIR)/%.log: $(RESULT_DIR)/.compiled
	@echo "[TEST] $*"
	@_start=$$(date +%s); \
	if ( cd $(LSPTEST); \
	      . $(SRC)/setup-exports; \
	      OPENJML_INSTALL="$(BUILDJDK)" \
	      OPENJML_SPECS="$(SRC)/../../Specs/specs" \
	      OPENJML_SOLVERS="$(SRC)/../../Solvers" \
	      "$(NJAVA)" $$OPENJML_JVM $$OPENJML_EXPORTS $(GSON_EXPORTS) \
	        -Dlsp.testdata=$(LSPTEST)/testdata \
	        -cp "$(CLASSES):$(LSP_JAR):$(LSP4J_CP):$(JUNIT_CP)" \
	        org.junit.runner.JUnitCore \
	        org.openjml.lsp.test.$* \
	    ) > $@ 2>&1; \
	then \
	  _elapsed=$$(( $$(date +%s) - _start )); \
	  grep -E "^OK|Tests run" $@ | tail -1 | sed "s/^/[PASS] $* ($${_elapsed}s): /"; \
	else \
	  _elapsed=$$(( $$(date +%s) - _start )); \
	  echo "[FAIL] $* ($${_elapsed}s) — log: $@"; \
	  cat $@; \
	  exit 1; \
	fi

## Run all test classes in parallel (default: 5 concurrent JVMs).
## Override with: make run-tests JOBS=3
JOBS ?= 5

## Two-phase: compile first (serial), then dispatch log targets in parallel.
_run-logs: $(LOG_FILES)

run-tests: $(RESULT_DIR)/.compiled
	@$(MAKE) --no-print-directory -j$(JOBS) _run-logs
	@echo "All LSP tests passed."

## Sequential fallback — useful for debugging; shows [PASS]/[FAIL] per class.
run-tests-seq: $(RESULT_DIR)/.compiled
	@rm -f $(LOG_FILES)
	@$(MAKE) --no-print-directory -j1 _run-logs
	@echo "All LSP tests passed (sequential)."

## Run a single test group, e.g.: make test-RenameTest1
## Multiple groups: make test-RenameTest1 test-FastTests
test-%: .FORCE $(RESULT_DIR)/.compiled
	@$(MAKE) --no-print-directory -B $(RESULT_DIR)/$*.log

clean: .FORCE
	rm -rf $(LSPTEST)/build
	$(MAKE) -C $(LSPROOT) clean

.FORCE:
