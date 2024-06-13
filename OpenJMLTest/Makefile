
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
## The following includes a terminating /
mkfile_dir := $(dir $(mkfile_path))

ROOT=${mkfile_dir}
D=OpenJML21

### The following is the OpenJML tests

openjml-test: prep
	##make release-tests 
	make tutorial-tests > log-tutorial-tests
	make unittests-par
	make scripttests
	#( cd ./unittests; grep -v sleep ./runall | tr -d '&' > ./runseq ; source ./runseq )

openjml-clean: .FORCE
	(cd ${ROOT}/../$D; make clean version openjml jmlruntime.jar )

openjml: .FORCE
	(cd ${ROOT}/../$D; make version openjml jmlruntime.jar )

release: .FORCE
	(cd ${ROOT}/../$D; make release)

T=temp-release

prep: .FORCE
	rm -rf $T
	mkdir $T
	echo "public class A { /*@ invariant 0; */ }" > $T/A.java
	echo "public class B { /*@ invariant true; */ }" > $T/B.java
	echo "import org.jmlspecs.annotation.Pure; public class C { @Pure int m() { return 0; } }" > $T/C.java
	echo "import org.jmlspecs.annotation.*; public class D { @Pure int m() { return 0; } }" > $T/D.java

tutorial-tests: .FORCE
	@ ( echo Testing tutorial files ;\
	    cd $(mkfile_dir)/../../openjml.github.io/tutorial; \
	    ./test \
	)

release-tests: .FORCE
	@ echo Running release tests with current development build
	@ NOZIP= $(ROOT)releaseTests/runtests > log-release-tests || ( echo "Errors reported in log-release-tests" && exit 1 )

unittests-seq:
	@ grep -v sleep ${ROOT}unittests/runall | tr -d '&' > ${ROOT}unittests/runseq
	@ . $(ROOT)unittests/runseq
			
unittests-par:
	( cd ${ROOT}/unittests; source ./runall | tee log-unittests | sort  )

scripttests: .FORCE
	( cd ${ROOT}/scripttests; ./escfiles-sort)

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

version:
	@ NOJML= njavac -d bin Version.java
	@ STACK=X njava -cp bin Version


coverage:
	java -jar ${HOME}/mylib/jacoco/lib/jacococli.jar report jacoco.exec --html html \
            --sourcefiles ../OpenJML21/src/jdk.compiler/share/classes \
            --classfiles ../OpenJML21/build/macosx-x86_64-server-release/jdk/modules/java.base \
            --classfiles ../OpenJML21/build/macosx-x86_64-server-release/jdk/modules/jdk.compiler
