
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
## The following includes a terminating /
mkfile_dir := $(dir $(mkfile_path))

## The folder containing this Makefile, namely .../OpenJMLTest
TEST=${mkfile_dir}

## The folder containing the source and builds, namely (currently) .../OpenJMLsrc
SRC=${TEST}/../OpenJMLsrc

## Location of a folder in which to put test files (relative to the folder holding this makefile)
T=temp-release

### The following is the OpenJML tests

### FIXME - not sure we need prep, even without release-tests
openjml-test: prep
	make release-tests > log-release-tests || ( echo "Errors reported in log-release-tests" && exit 1 )
	make userguide-tests
	make json-tests
	-make tutorial-tests
	-make unittests-par

## This target is used when running tests as part of a github action
openjml-test-git: prep
	make -C ${TEST} release-tests
	-make -C ${TEST} userguide-tests-released
	make -C ${TEST} json-tests
	-make tutorial-tests
	JOBS=4 time ${TEST}/unittests/runpar

openjml-test-temp:
	JOBS=4 time ${TEST}/unittests/runpar
	JOBS=6 time ${TEST}/unittests/runpar
	JOBS=8 time ${TEST}/unittests/runpar
	JOBS=10 time ${TEST}/unittests/runpar
	JOBS=0 time ${TEST}/unittests/runpar
	JOBS=1 time ${TEST}/unittests/runpar
	#grep FAILED ${TEST}/unittests/log-* | grep -v Trace | grep -v Query

openjml-clean: .FORCE
	make -C ${SRC} clean; make openjml

openjml: .FORCE
	(cd ${SRC}; make version && make openjml && make jmlruntime.jar )

## Deletes all temporary files
## Many more to delete
clean: cov-clean
	find . -name '*.class' -delete
	git checkout ./test/specspath/srczz/z/C.class ./test/specspath/srct/C.class ./test/specspath/srctt/C.class ./test/specspath/srcz/z/C.class
	find . -name '*actual*' -delete
	find . -name 'log*' -type f ! -path './test/gitbug785/guava/*' -delete
	rm -f smt/*.smt*
	rm -f tempUserGuide
	rm -rf testcompiles
	rm -rf jsontests/json-loc/xx


release: .FORCE
	make -C ${SRC} release


prep: temp-release

temp-release temp-release/D.java:
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
# Downloads the userguide (from Overleaf) and tests all the example files
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
	( cd ${USERGUIDE}; curl -s -S -o examples.zip http://www.openjml.org/examples/userguide-examples.zip; unzip -q *.zip )
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

.FORCE:

##### The following are debugging tests

debug:
	rm -f Test.class
	njavac -cp . Test.java
	njava -cp . Test 

tests:
	NOJML= njavac -d bin -cp src:../OpenJDKModule/runtime/src:libs/junit-4.13.2.jar:libs/hamcrest-core-1.3.jar:libs/junit-jupiter-api-5.5.2.jar:libs/apiguardian-api-1.1.0.jar --add-modules jdk.compiler,java.base RunTests.java  `find src -name '*.java' -and -not -name Activator.java`
	STACK=X njava -cp bin:../OpenJDKModule/runtime/src:libs/junit-4.13.2.jar:libs/hamcrest-core-1.3.jar:libs/junit-jupiter-api-5.5.2.jar:libs/apiguardian-api-1.1.0.jar --add-modules jdk.compiler,java.base RunTests

test:
	STACK=X njava -cp ../OpenJDKModule/runtime/src:libs/junit-4.13.2.jar:libs/hamcrest-core-1.3.jar:libs/junit-jupiter-api-5.5.2.jar:libs/apiguardian-api-1.1.0.jar --add-modules jdk.compiler,java.base RunTests

### The following are for coverage measurement

# Deletes all coverage data and html files
cov-clean:
	rm -rf ./cov
	mkdir ./cov
	find . -name '*.class' -delete
	git checkout ./test/specspath/srczz/z/C.class ./test/specspath/srct/C.class ./test/specspath/srctt/C.class ./test/specspath/srcz/z/C.class

# Runs all tests to produce coverage data
# One can also run individual tests and individual unit tests, e.g. COV= runtests escfiles
cov-test:
	- COV= time make json-tests
	- COV= time make release-tests
	- COV= time make tutorial-tests
	- COV= time make userguide-tests
	- COV= time ./unittests/runpar 

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
            --classfiles ./../OpenJMLsrc/build/macosx-x86_64-server-release/jdk/modules/jdk.compiler )

# Launches a browser on the current coverage data
cov-show:
	@open ${TEST}/cov/html/index.html
