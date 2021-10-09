
##R=/Users/davidcok/projects/OpenJMLB
##ROOT=$R/OpenJML/OpenJDKModule
##MODS=$(ROOT)/build/macosx-x86_64-server-release/images/jmods
##SPECS=$R/Specs/specs


##### The following are debugging tests

default:
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


### The following is the OpenJML tests

openjml-test:
	( cd ./scripttests; ./escfiles-sort)
	( cd ./scripttests; ./gitfiles-sort)
	( cd ./unittests; source ./runall )
