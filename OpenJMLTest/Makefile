
#R=/Users/davidcok/projects/OpenJMLB
#ROOT=$R/OpenJML/OpenJDKModule
#MODS=$(ROOT)/build/macosx-x86_64-server-release/images/jmods
#SPECS=/Users/davidcok/projects/OpenJMLB/Specs/specs

### The following is the OpenJML tests

openjml-test: prep
	( cd ./scripttests; ./escfiles-sort)
	( cd ./scripttests; ./gitfiles-sort)
	( cd ./unittests; source ./runall  )
	#( cd ./unittests; grep -v sleep ./runall | tr -d '&' > ./runseq ; source ./runseq )


T=temp-release

prep:
	rm -rf $T
	mkdir $T
	echo "public class A { /*@ invariant 0; */ }" > $T/A.java
	echo "public class B { /*@ invariant true; */ }" > $T/B.java
	echo "import org.jmlspecs.annotation.Pure; public class C { @Pure int m() { return 0; } }" > $T/C.java
	echo "import org.jmlspecs.annotation.*; public class D { @Pure int m() { return 0; } }" > $T/D.java

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

git:
	openjml -no-staticInitWarning -specspath $(SPECS) -esc -dir test/gitbug257 

E-vm:
	openjml 4 -no-staticInitWarning  -specspath /Users/davidcok/testn/esc:$(SPECS) /Users/davidcok/testn/esc/ETest.java -esc -verbose -method m 

E-v:
	openjml 4 -no-staticInitWarning  -specspath /Users/davidcok/testn/esc:$(SPECS) /Users/davidcok/testn/esc/ETest.java -esc -verbose 

E-bin:
	openjml 4 -no-staticInitWarning  -specspath /Users/davidcok/testn/esc:$(SPECS) /Users/davidcok/testn/esc/ETest.java -esc -progress

E:
	openjml -no-staticInitWarning  -specspath /Users/davidcok/testn/esc:$(SPECS) /Users/davidcok/testn/esc/ETest.java -esc -progress

E-src:
	cd ~/testn && openjml 1 -no-staticInitWarning -specspath /Users/davidcok/testn/esc:$(SPECS) /Users/davidcok/testn/esc/ETest.java -esc -verbose


