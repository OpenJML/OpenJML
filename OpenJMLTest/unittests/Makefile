
## This Makefile is used by runtests. We use a Makefile rather than just using the command-line directly so as to use make's checking that a compilation is up to date
## The compile line uses a number of Env. variables set within runtests, so it is not easy to use this Makefile standalone.

## NJAVAC, CP, ROOT, EXPORTS are set in runtests

## Set these javac/openjml options for compiling all the test suites (they don't necessarily apply to all of the test cases)
OPTIONS=
#"-Xlint:unchecked -Xdiags:verbose -Xlint:text-blocks"

unittestframework: OpenJMLTestRunner.class OpenJMLTestRunner.java ../src/org/jmlspecs/openjmltest/*.java ../src/org/jmlspecs/openjmltest/testsuites/*.java
	@NOJML= $(NJAVAC) -g ${OPTIONS} -cp $(CP) -p $(ROOT)/build/*-release/jdk/modules $(EXPORTS) OpenJMLTestRunner.java  ../src/org/jmlspecs/openjmltest/*.java ../src/org/jmlspecs/openjmltest/testsuites/*.java

OpenJMLTestRunner.class: OpenJMLTestRunner.java ../src/org/jmlspecs/openjmltest/*.java ../src/org/jmlspecs/openjmltest/testsuites/*.java
	@NOJML= $(NJAVAC) -g ${OPTIONS} -cp $(CP) -p $(ROOT)/build/*-release/jdk/modules $(EXPORTS) OpenJMLTestRunner.java  ../src/org/jmlspecs/openjmltest/*.java ../src/org/jmlspecs/openjmltest/testsuites/*.java
	@touch unittestframework
