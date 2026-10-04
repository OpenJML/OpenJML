
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
## The following includes a terminating /
mkfile_dir := $(dir $(mkfile_path))

## The folder containing this Makefile, namely .../OpenJMLTest
TEST := $(patsubst %/,%,$(mkfile_dir))

## The folder containing the source and builds, namely (currently) .../OpenJMLsrc
SRC=${TEST}/../OpenJMLsrc

## Location of a folder in which to put test files (relative to the folder holding this makefile)
T=temp-release

.PHONY: openjml-test openjml-test-git openjml-test-temp openjml-clean openjml \
        clean release prep \
        tutorial-tests tutorial-tests-git userguide-tests userguide-tests-released \
        release-tests unittests-seq unittests-par json-tests lsp-tests \
        cov-clean cov-test cov-report cov-show cov-test-by-test cov-analyze-by-test cov-report-by-test

### The following is the OpenJML tests

### FIXME - not sure we need prep, even without release-tests
openjml-test: prep
	$(MAKE) release-tests > log-release-tests || ( echo "Errors reported in log-release-tests" && exit 1 )
	-$(MAKE) userguide-tests
	-$(MAKE) json-tests
	-$(MAKE) -C lsp run-tests
	-$(MAKE) tutorial-tests
	-$(MAKE) unittests-par

## This target is used when running tests as part of a github action
openjml-test-git: prep
	$(MAKE) -C ${TEST} release-tests
	-$(MAKE) -C ${TEST} userguide-tests-released
	-$(MAKE) -C lsp run-tests
	-$(MAKE) -C ${TEST} json-tests
	-$(MAKE) tutorial-tests
	JOBS=4 time ${TEST}/unittests/runpar

openjml-test-temp:
	JOBS=4 time ${TEST}/unittests/runpar
	JOBS=6 time ${TEST}/unittests/runpar
	JOBS=8 time ${TEST}/unittests/runpar
	JOBS=10 time ${TEST}/unittests/runpar
	JOBS=0 time ${TEST}/unittests/runpar
	JOBS=1 time ${TEST}/unittests/runpar
	#grep FAILED $T_Nullness1.out.actual{TEST}/unittests/log-* | grep -v Trace | grep -v Query

openjml-clean: .FORCE
	$(MAKE) -C ${SRC} clean; $(MAKE) openjml

openjml: .FORCE
	(cd ${SRC}; $(MAKE) version && $(MAKE) openjml && $(MAKE) jmlruntime.jar )

## Deletes all temporary files
## Many more to delete
clean: cov-clean
	$(MAKE) -C unittests clean
	find . -name '*.class' -delete
	git checkout ./test/specspath/srczz/z/C.class ./test/specspath/srct/C.class ./test/specspath/srctt/C.class ./test/specspath/srcz/z/C.class
	find . -name '*actual*' -delete
	find . -name 'log*' -type f ! -path './test/gitbug785/guava/*' -delete
	rm -f smt/*.smt*
	rm -rf tempUserGuide
	rm -rf testcompiles
	rm -rf jsontests/json-loc/xx
	rm -f $T


release: .FORCE
	$(MAKE) -C ${SRC} release


prep: temp-release

## This target must match $T
temp-release:
	rm -rf $T
	mkdir $T
	echo "public class A { /*@ invariant 0; */ }" > $T/A.java
	echo "public class B { /*@ invariant true; */ }" > $T/B.java
	echo "import org.jmlspecs.annotation.Pure; public class C { @Pure int m() { return 0; } }" > $T/C.java
	echo "import org.jmlspecs.annotation.*; public class D { @Pure int m() { return 0; } }" > $T/D.java

tutorial-tests: 
	@ ( echo Testing tutorial files ;\
	    . $(TEST)/setup-coverage tutorialtests ; \
	    cd ${TEST}/../../openjml.github.io/tutorial; \
	    ./test \
	)

tutorial-tests-git: 
	@ ( echo Testing tutorial files ;\
	    cd ${TEST}/../../openjml.github.io/tutorial; \
	    ./test \
	)

USERGUIDE=./tempUserGuide
OVERLEAFID=620c2512d552cc226f5f4c94
TESTSCRIPT=${USERGUIDE}/${OVERLEAFID}/test-userguide-examples
# Clones the userguide (from Overleaf) and tests all the example files
# In a git action, this needs a password to login, and fails
userguide-tests:
	@ ( rm -rf ${USERGUIDE}; mkdir -p ${USERGUIDE}; cd ${USERGUIDE}; git clone https://git@git.overleaf.com/${OVERLEAFID} ; )
	@ if [ -e ${TESTSCRIPT} ] ; then \
	    chmod +x ${TESTSCRIPT} ; \
	    ${TESTSCRIPT} ; \
	    rm -rf ${USERGUIDE}; \
	else echo Userguide tests are not available at ${TESTSCRIPT}; fi

# This target is used to run the userguide tests in a github action; it uses openjml and the examples that are in the release
# Obtains the zip of released example files from openjml.org, and tests the contained examples
# (MacOS has curl and does not have wget without manual install)
userguide-tests-released:
	rm -rf ${USERGUIDE}; mkdir -p ${USERGUIDE};
	( cd ${USERGUIDE}; curl -s -S -o examples.zip https://www.openjml.org/examples/userguide-examples.zip; unzip -q *.zip )
	chmod +x ${USERGUIDE}/test-userguide-examples
	${USERGUIDE}/test-userguide-examples


# The 'release tests' are a small set of tests that are used to verify that a openjml build is basically OK.
# It is run as part of the github action that builds a release
# but can also be run directly with this target, before an attempt to construct a release
release-tests: prep .FORCE
	@ echo Running release tests with current development build
	@ ./releaseTests/runtests

# Runs the unit tests, sequentially, which is time-consuming
unittests-seq: prep .FORCE
	@ $(TEST)/unittests/runseq
			
# Runs the unit tests with some parallelism (default 5 parallel jobs).
# Set the number of jobs like this: JOBS=n make unittests-par
unittests-par: prep .FORCE
	@ ${TEST}/unittests/runpar

# Executes the tests of JSON output and input
json-tests: .FORCE
	@ ${TEST}/jsontests/json/run
	@ ${TEST}/jsontests/json-loc/run

# Compiles and runs the LSP server tests
lsp-tests: .FORCE
	$(MAKE) -C ${TEST}/lsp

.FORCE:

### The following are for coverage measurement

# Deletes all coverage data and html files
cov-clean:
	rm -rf ./cov
	mkdir ./cov
	find . -name '*.class' -delete
	git checkout ./test/specspath/srczz/z/C.class ./test/specspath/srct/C.class ./test/specspath/srctt/C.class ./test/specspath/srcz/z/C.class

# Runs all tests to produce coverage data.
# Setting COV to any value (including empty) enables coverage measurement; leaving COV unset disables it.
# One can also run individual tests with coverage, e.g.: COV= ./unittests/runtests escfiles
cov-test:
	- COV= time $(MAKE) json-tests
	- COV= time $(MAKE) release-tests
	- COV= time $(MAKE) tutorial-tests
	- COV= time $(MAKE) userguide-tests
	- COV= time ./unittests/runpar
	- COV= $(MAKE) -C lsp run-tests

# Creates or updates html files based on coverage data
cov-report:
	@rm -rf "./cov/html"
	@( rm -f cov/combined.exec; java -jar ./jacoco/lib/jacococli.jar merge --quiet cov/*.exec --destfile cov/combined.exec )
	@( java -jar ./jacoco/lib/jacococli.jar report --quiet ./cov/combined.exec --html ./cov/html \
	    --sourcefiles "./unittests" --classfiles "./unittests" \
	    --sourcefiles ./../OpenJMLsrc/src/jdk.compiler/share/classes \
            --sourcefiles ./../OpenJMLTest/src/ \
            --classfiles ./../OpenJMLTest/src/ \
            --classfiles ./../OpenJMLsrc/build/macosx-x86_64-server-release/jdk/modules/java.base \
            --classfiles ./../OpenJMLsrc/build/macosx-x86_64-server-release/jdk/modules/jdk.compiler \
            --sourcefiles ./../OpenJMLlsp/src \
            --classfiles ./../OpenJMLlsp/build/classes )

## Per-test coverage: like cov-test for the unit tests (runpar), but split by test case. Each
## test's coverage (including that of any openjml child JVM its ./run script starts) goes to its
## own cov/by-test/<TestSuite>.<method>.exec; each test JVM's index-unit-<suite>.tsv maps each
## file back to its test (class, display name, PASS/FAIL/TIMEOUT, wall-clock ms). Whatever runs
## outside any test (class init, @BeforeClass, @Parameters) goes to cov/by-test/_outside-tests.exec.
## See PerTestCoverage.java and setup-coverage for the mechanism; the same as jSMTLIB's and
## KotlinSL's per-test coverage. cov-test and its cov/*.exec are untouched. The directory is
## cleared first: per-test files are appended to during a run, so stale ones from an earlier
## run would silently mix in. SUITES limits the run to some test suites (all by default), e.g.
##   make cov-test-by-test SUITES="escfiles3 typechecking"
## and JOBS sets runpar's number of concurrent test JVMs, as usual. The analysis
## (cov-analyze-by-test) then runs on the result, even if some tests failed.
cov-test-by-test:
	rm -rf cov/by-test
	- COV= COV_BY_TEST= time ./unittests/runpar $(SUITES)
	$(MAKE) cov-analyze-by-test

## coverage-analyzer (github.com/davidcok/coverage-analyzer): finds tests that add nothing to
## coverage -- empty, duplicate and subsumed tests, and a minimum-run-time set of tests that
## covers everything the suite covers. Its classpath is its own jar plus the org.jacoco.core
## and ASM jars vendored in jacoco/lib alongside jacocoagent.jar: the very (customized) JaCoCo
## build that recorded the data, which places probes differently from stock JaCoCo; the
## analyzer maps probes back to source lines by re-deriving that layout from the class files.
## (The jars are the ones jSMTLIB and KotlinSL vendor; jacocoagent.jar is the same build.)
COV_ANALYZER_JARS := coverage-analyzer org.jacoco.core asm asm-commons asm-tree
ifeq ($(OS),Windows_NT)
  COV_CP_SEP := ;
else
  COV_CP_SEP := :
endif
COV_EMPTY :=
COV_SPACE := $(COV_EMPTY) $(COV_EMPTY)
COV_ANALYZER_CP := $(subst $(COV_SPACE),$(COV_CP_SEP),$(patsubst %,jacoco/lib/%.jar,$(COV_ANALYZER_JARS)))
## The OpenJML compiler as built: the jdk.compiler module of the development build
COV_CLASSES ?= $(firstword $(wildcard ../OpenJMLsrc/build/*/jdk/modules/jdk.compiler))
## OpenJML's own code and the javac code it extends -- the rest of jdk.compiler (com.sun.source,
## jdk.internal, ...) and the test harness are left out. Override to analyze differently, e.g.
##   make cov-analyze-by-test COV_ANALYZER_ARGS="--include 'org.jmlspecs.openjml.**' --granularity line"
COV_ANALYZER_ARGS ?= --include 'org.jmlspecs.openjml.**' --include 'org.openjml.**' \
	--include 'com.sun.tools.javac.**' --only-classfiles

## Analyze the data from the last cov-test-by-test run (without re-running the tests): summary
## to the terminal and cov/by-test-report.txt, full results as CSV files in cov/by-test-report/.
## The per-JVM indexes are first concatenated into cov/by-test/index.tsv (one header).
## --strip removes this directory's absolute path from test names that carry it.
cov-analyze-by-test:
	@cd cov/by-test && first=1 && for f in index-*.tsv; do \
	    if [ $$first = 1 ]; then cat "$$f"; first=0; else tail -n +2 "$$f"; fi; \
	done > index.tsv
	java -cp "$(COV_ANALYZER_CP)" com.sigillogic.coverage.analyzer.Main \
		--index cov/by-test/index.tsv --classfiles $(COV_CLASSES) --strip "$(CURDIR)/" \
		$(COV_ANALYZER_ARGS) --out cov/by-test-report > cov/by-test-report.txt; \
	status=$$?; cat cov/by-test-report.txt; exit $$status

## Merge every per-test file back into one data set and report it, like cov-report does for
## cov-test -- a check that splitting lost nothing.
cov-report-by-test:
	java -jar jacoco/lib/jacococli.jar merge --quiet cov/by-test/*.exec --destfile cov/by-test-merged.exec
	java -jar jacoco/lib/jacococli.jar report --quiet cov/by-test-merged.exec \
		--classfiles $(COV_CLASSES) \
		--sourcefiles ../OpenJMLsrc/src/jdk.compiler/share/classes \
		--html cov/html-by-test \
		--xml cov/coverage-by-test.xml

# Launches a browser on the current coverage data
cov-show:
	@if [ "$$(uname)" = "Darwin" ]; then open ${TEST}/cov/html/index.html; \
	 else xdg-open ${TEST}/cov/html/index.html 2>/dev/null || true; fi
