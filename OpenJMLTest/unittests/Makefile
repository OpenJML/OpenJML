
## This Makefile is used by runtests. We use a Makefile rather than just using the command-line directly so as to use make's checking that a compilation is up to date
## The compile line uses a number of Env. variables set within runtests, so it is not easy to use this Makefile standalone.

## NJAVAC, CP, MODPATH, ROOT, OPENJML_EXPORTS are set in runtests (CP and MODPATH are Windows paths on WSL)

## Set these javac/openjml options for compiling all the test suites (they don't necessarily apply to all of the test cases)
OPTIONS=-Xlint:unchecked -Xdiags:verbose -Xlint:text-blocks

unittestframework: ../src/org/openjml/runners/*.java ../src/org/jmlspecs/openjmltest/*.java ../src/org/jmlspecs/openjmltest/testsuites/*.java
	@NOJML=1 WSLENV="$${WSLENV:+$$WSLENV:}NOJML" $(NJAVAC) -g $(OPTIONS) -cp "$(CP)" -p "$(MODPATH)" $(OPENJML_EXPORTS) ../src/org/openjml/runners/*.java  ../src/org/jmlspecs/openjmltest/*.java ../src/org/jmlspecs/openjmltest/testsuites/*.java

clean:
	rm -rf temp log* the.jml.lock unittestframework