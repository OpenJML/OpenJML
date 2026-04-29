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

## Classpath components
JUNITDIR  := $(LSPTEST)/../libs
JUNIT_CP  := $(JUNITDIR)/junit-4.13.2.jar:$(JUNITDIR)/hamcrest-core-1.3.jar:$(JUNITDIR)/junit-jupiter-api-5.5.2.jar:$(JUNITDIR)/apiguardian-api-1.1.0.jar:$(JUNITDIR)/opentest4j-1.3.0.jar
## LSP4J jars needed at compile time (for LSP Diagnostic types) and at runtime.
## Gson is intentionally excluded: jdk.compiler bundles and exports Gson, and putting
## a separate Gson jar on the classpath would create a split-package conflict.
LSP4J_CP  := $(LSPROOT)/libs/org.eclipse.lsp4j-$(LSP4J_VERSION).jar:$(LSPROOT)/libs/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar
LSP_JAR   := $(LSPROOT)/build/openjml-lsp.jar
LSP_SRCS  := $(shell find $(LSPROOT)/src -name '*.java')

## Build output
CLASSES    := $(LSPTEST)/build/classes
RESULT_DIR := $(LSPTEST)/build/results

## Coverage support.
## When COV is set (to any value, including empty) the JaCoCo agent is attached
## to each test JVM.  Each test class writes its own exec file
## (cov/lsp-ClassName.exec) to avoid concurrent-write races between parallel
## JVMs.  The files land in the shared OpenJMLTest/cov/ directory so the parent
## cov-report target merges them together with the unit-test exec files.
## When running standalone (cov-test / cov-report here), they land in
## $(LSPTEST)/cov/ and the standalone cov-report reads from there.
COV_DIR   := $(LSPTEST)/../cov
COV_AGENT := $(LSPTEST)/../jacoco/lib/jacocoagent.jar
COV_CLI   := $(LSPTEST)/../jacoco/lib/jacococli.jar
## JAVA_AGENT is intentionally a recursively-expanded variable (=, not :=) so
## that $* (the test-class stem) is substituted at rule-firing time.
ifdef COV
  JAVA_AGENT = -javaagent:$(COV_AGENT)=destfile=$(COV_DIR)/lsp-$*.exec
else
  JAVA_AGENT =
endif

## Source and test trees (infrastructure in src/, test cases in test/)
INFRA_SRCS := $(shell find $(LSPTEST)/src  -name '*.java')
TEST_SRCS  := $(shell find $(LSPTEST)/test -name '*.java')

## All test classes — each runs in its own JVM process.
## Ordered longest-first so -j5 keeps the pool busy and finishes sooner.
## Approximate sequential timings: PropertiesFileOptionsTest 121s, FastTests 108s,
## RenameTest1 75s, RenameTest2 71s, ReferenceFinderJmlTest 54s, DoEscTest 53s,
## DiagnosticsTest 49s, EscStatusTest 44s, MethodAndClassTest 40s,
## DefinitionFinderJmlTest 34s,
## CommandDispatchTest 31s, DocumentSymbolTest 31s,
## RenameJmlTest 24s, RenameTest3 24s,
## RenameTest4 23s, RacTest 23s, RenameJmlTest2 22s,
## MultiFileEscTest 19s, DocumentLifecycleTest 18s.
TEST_CLASSES := \
  PropertiesFileOptionsTest \
  ToolOptionsTest \
  FastTests \
  RenameTest1 \
  RenameTest2 \
  ReferenceFinderJmlTest \
  DoEscTest \
  EscCancellationTest \
  ConcurrentEscTest \
  CheckRunnerEscAndRacTest \
  DiagnosticsTest \
  EscStatusTest \
  MethodAndClassTest \
  DefinitionFinderJmlTest \
  CommandDispatchTest \
  DocumentSymbolTest \
  DocumentSymbolProtocolTest \
  RenameJmlTest \
  RenameJmlTest2 \
  RenameMethodAndClassTest \
  RenameProtocolTest \
  RenameTest3 \
  RenameTest4 \
  RacTest \
  MultiFileEscTest \
  EscDirWithContextTest \
  DocumentLifecycleTest \
  CodeLensAndStatusTest \
  HoverTest \
  RenamePreflightTest \
  DebouncingAndCancellationTest \
  BatchAndWatchedFilesTest \
  WatchedFilesHandlerTest \
  IncrementalSyncProtocolTest \
  MultiProjectTest \
  SplitEscTest \
  WorkspaceIndexTest \
  DocumentHighlightTest \
  ModelMethodEscTest \
  MultiClassEscTest \
  LauncherIntegrationTest \
  PerMethodEscStatusTest \
  JmlCompanionSemanticTokensTest \
  GoToDefinitionCrossFileTest \
  LanguageServerLifecycleTest \
  CheckRunnerEscContextTest \
  LegacyEscSmokeTest \
  SymlinkWorkspaceTest \
  EscSessionGenTest \
  SymbolsForProjectTest \
  EscPerMethodMarkerTest \
  EscAtLineTest \
  EscInvocationVariantsTest \
  ClearAndReescTest \
  ClearMarkersTest \
  DidCloseTest \
  WorkspaceFoldersTest

LOG_FILES := $(patsubst %,$(RESULT_DIR)/%.log,$(TEST_CLASSES))

.PHONY: all compile run-tests run-tests-seq _run-logs clean cov-test cov-report cov-show check-commands .FORCE

all: run-tests

## Verify that command-name constants in extension.js match OpenJMLCommands.java.
## Requires node (any modern version) on the PATH.
check-commands:
	node $(LSPROOT)/check-commands.js

## Build the LSP server jar when any server source file is newer than the jar.
$(LSP_JAR) jar: $(LSP_SRCS)
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
	      "$(NJAVA)" $(JAVA_AGENT) $$OPENJML_JVM $$OPENJML_EXPORTS \
	        -Dlsp.testdata=$(LSPTEST)/testdata \
	        -Djml.grammar.lsp=$(LSPROOT)/vscode-extension/syntaxes/jml.tmLanguage.json \
	        -Djml.grammar.ui=$(LSPTEST)/../../OpenJMLUI/syntaxes/jml.tmLanguage.json \
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

## Run all test classes in parallel (default: 4 concurrent JVMs).
## Override with: make run-tests JOBS=3
JOBS ?= 4

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

### Coverage targets (standalone — operate on $(LSPTEST)/cov/)

## Run all LSP tests under JaCoCo and generate an HTML coverage report.
## Usage: make cov-test   (writes report to $(LSPTEST)/cov/html/)
cov-test: .FORCE
	@rm -rf $(LSPTEST)/cov
	@mkdir -p $(LSPTEST)/cov
	@$(MAKE) --no-print-directory COV=1 COV_DIR=$(LSPTEST)/cov run-tests
	@$(MAKE) --no-print-directory COV_DIR=$(LSPTEST)/cov cov-report

## Generate (or refresh) the HTML coverage report from existing exec files.
## Can be run without re-running tests if the exec files are already present.
cov-report: .FORCE
	@rm -rf "$(LSPTEST)/cov/html"
	@( rm -f $(LSPTEST)/cov/combined.exec; \
	   java -jar $(COV_CLI) merge --quiet $(LSPTEST)/cov/lsp-*.exec \
	        --destfile $(LSPTEST)/cov/combined.exec )
	@( java -jar $(COV_CLI) report --quiet $(LSPTEST)/cov/combined.exec \
	        --html $(LSPTEST)/cov/html \
	        --sourcefiles $(LSPROOT)/src \
	        --classfiles $(LSPROOT)/build/classes )
	@echo "Coverage report: $(LSPTEST)/cov/html/index.html"

## Open the coverage report in a browser.
cov-show: .FORCE
	@if [ "$$(uname)" = "Darwin" ]; then open $(LSPTEST)/cov/html/index.html; \
	 else xdg-open $(LSPTEST)/cov/html/index.html 2>/dev/null || true; fi

.FORCE:
