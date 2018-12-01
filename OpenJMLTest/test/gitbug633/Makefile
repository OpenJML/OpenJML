OPENJML=/usr/local/openjml
Z3=/usr/local/z3/bin/z3.exe

OJML=java -cp `cygpath -w ${OPENJML}/openjml.jar` org.jmlspecs.openjml.Main -exec `cygpath -w ${Z3}`

all check:
	java -version
	${OJML} -version
	${OJML} -esc Complex.java ComplexOps.java Polar.java Rectangular.java

