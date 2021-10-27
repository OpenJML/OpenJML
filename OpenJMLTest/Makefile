
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
## The following includes a terminating /
mkfile_dir := $(dir $(mkfile_path))

ROOT=${mkfile_dir}

### The following is the OpenJML tests

openjml-test: prep
	( cd ${ROOT}/scripttests; ./escfiles-sort)
	( cd ${ROOT}/unittests; source ./runall  )
	#( cd ./unittests; grep -v sleep ./runall | tr -d '&' > ./runseq ; source ./runseq )
	make release-tests

openjml:
	(cd ${ROOT}/../OpenJDKModule; make openjml)

T=temp-release

prep:
	rm -rf $T
	mkdir $T
	echo "public class A { /*@ invariant 0; */ }" > $T/A.java
	echo "public class B { /*@ invariant true; */ }" > $T/B.java
	echo "import org.jmlspecs.annotation.Pure; public class C { @Pure int m() { return 0; } }" > $T/C.java
	echo "import org.jmlspecs.annotation.*; public class D { @Pure int m() { return 0; } }" > $T/D.java

tutorial-test:
	@ ( echo Testing tutorial files ;\
	    cd $(mkfile_dir)/../OpenJDKModule/release-files/tutorial; \
	    X=0 ;\
	    for f in *.java ; do \
		o=`echo $$f | sed -e 's/java/out/'`; \
		c=`cat $$f | head -1 | sed -e 'sx//[ ]*xx' ` ;\
		../../$$c > log ;\
		e=$$? ;\
		if [ -e $$o ]; then  \
			if [ $$e -eq "0" ]; then \
			    X=1; echo $$f "has out file but exit code of 0" ;\
			fi ;\
			diff log $$o ; z=$$? ; \
			if [ $$z -ne "0" ]; then  \
			    X=1; echo $$f "has wrong output" ; \
			fi ;\
		elif [ -n "$( cat log )" ]; then \
			echo "OK example has output: " $$f ;\
			cat log ;\
		elif [ $$e -ne "0" ]; then \
			X=1; echo "OK example has unexpected exit code: " $$f $$e ; \
		fi ; \
	    done ; \
	    exit $$X \
	)

release-tests:
	@ echo Running release tests with current development build
	@ NOZIP= $(ROOT)releaseTests/runtests > log-release-tests || ( echo "Errors reported in log-release-tests" && exit 1 )

unittests-seq:
	. $(ROOT)unittests/runseq
			
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


