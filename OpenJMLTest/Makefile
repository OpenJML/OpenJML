
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
## The following includes a terminating /
mkfile_dir := $(dir $(mkfile_path))

## The folder containing this Makefile, namely .../OpenJMLTest
TEST=${mkfile_dir}

## The folder containing the source and builds, namely (currently) .../OpenJML21
SRC=${TEST}/../OpenJML21

## Location of a folder in which to put test files (relative to the folder holding this makefile)
T=temp-release

### The following is the OpenJML tests

### FIXME - not sure we need prep, even without release-tests
openjml-test: prep
	make release-tests > log-release-tests || ( echo "Errors reported in log-release-tests" && exit 1 )
	make userguide-tests
	make json-tests
	-make unittests-par
	-make tutorial-tests

openjml-test-git: prep
	make -C ${TEST} release-tests
	-make -C ${TEST} userguide-tests-released
	make -C ${TEST} json-tests
	-make tutorial-tests
	JOBS=4 time ${TEST}/unittests/runpar -retrylog

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

tutorial-tests: Run.class .FORCE
	@ ( echo Testing tutorial files ;\
	    . $(TEST)/setup-coverage tutorialtests ; \
            alias openjml="$OJA" ; \
	    cd ${TEST}/../../openjml.github.io/tutorial; \
	    ./test \
	)

USERGUIDE=${TEST}/tempUserGuide
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

# Obtains the zip of released example files from openjml.org, and tests the contained examples
# (MacOS has curl and does not have wget without manual install)
userguide-tests-released:
	rm -rf ${USERGUIDE}; mkdir -p ${USERGUIDE};
	( cd ${USERGUIDE}; curl -s -S -o examples.zip http://www.openjml.org/examples/userguide-examples.zip; unzip -q *.zip )
	chmod +x ${USERGUIDE}/test-userguide-examples
	${USERGUIDE}/test-userguide-examples

release-tests: prep Run.class .FORCE
	@ echo Running release tests with current development build
	@ $(TEST)/releaseTests/runtests

unittests-seq: prep Run.class .FORCE
	@ $(TEST)/unittests/runseq
			
unittests-par: prep Run.class .FORCE
	( ${TEST}/unittests/runpar | tee log-unittests | sort  )

json-tests: .FORCE Run.class
	@ ${TEST}/scripttests/json/run
	@ ${TEST}/scripttests/json-loc/run

Run.class:
	$(TEST)/../OpenJML21/openjml-compile Run.java

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

cov-clean:
	rm -rf ${TEST}/cov
	mkdir ${TEST}/cov

cov-test:
	cd ${TEST}
	COV= time make json-tests
	COV= time ./unittests/runpar | tee log-unittests | sort
	##COV= time make tutorial-tests ## FIXME: Not yet working and one does not complete
	## COV= make release-tests ## FIXME: Not yet working

cov-report:
	@rm -rf ${TEST}/cov/html
	@( cd ${TEST}; rm -f cov/combined.exec; java -jar ./jacoco/lib/jacococli.jar merge --quiet cov/*.exec --destfile cov/combined.exec )
	@( cd ${TEST}; java -jar ./jacoco/lib/jacococli.jar report --quiet cov/combined.exec --html cov/html \
            --sourcefiles ../OpenJML21/src/jdk.compiler/share/classes \
            --sourcefiles ../OpenJMLTest/src/ \
            --classfiles ../OpenJMLTest/src/ \
            --classfiles ../OpenJML21/build/macosx-x86_64-server-release/jdk/modules/java.base \
            --classfiles ../OpenJML21/build/macosx-x86_64-server-release/jdk/modules/jdk.compiler )

cov-show:
	@open ${TEST}cov/html/index.html
