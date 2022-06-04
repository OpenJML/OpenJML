
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
## The following includes a terminating /
mkfile_dir := $(dir $(mkfile_path))

ROOT=${mkfile_dir}

### The following is the OpenJML tests

openjml-test: prep
	make release-tests 
	-make tutorial-tests
	make unittests-par
	make script-tests
	./test-userguide-examples

script-tests:
	( cd ${ROOT}/scripttests; ./escfiles-err )

openjml-clean:
	(cd ${ROOT}/../OpenJDKModule; make clean version openjml jmlruntime.jar )

openjml:
	(cd ${ROOT}/../OpenJDKModule; make version openjml jmlruntime.jar )

release:
	(cd ${ROOT}/../OpenJDKModule; make release)

T=temp-release

prep:
	rm -rf $T
	mkdir $T
	echo "public class A { /*@ invariant 0; */ }" > $T/A.java
	echo "public class B { /*@ invariant true; */ }" > $T/B.java
	echo "import org.jmlspecs.annotation.Pure; public class C { @Pure int m() { return 0; } }" > $T/C.java
	echo "import org.jmlspecs.annotation.*; public class D { @Pure int m() { return 0; } }" > $T/D.java

tutorial-tests:
	@ ( echo Testing tutorial files ;\
	    cd $(mkfile_dir)/../../openjml.github.io/tutorial; \
	    ./test \
	)

release-tests: 
	@ echo Running release tests with current development build
	@ NOZIP= $(ROOT)releaseTests/runtests > log-release-tests || ( echo "Errors reported in log-release-tests" && exit 1 )

unittests-seq:
	@ grep -v sleep ${ROOT}unittests/runall | tr -d '&' > ${ROOT}unittests/runseq
	@ . $(ROOT)unittests/runseq
			
unittests-par:
	. $(ROOT)unittests/runall
			
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

version:
	@ NOJML= njavac -d bin Version.java
	@ STACK=X njava -cp bin Version


