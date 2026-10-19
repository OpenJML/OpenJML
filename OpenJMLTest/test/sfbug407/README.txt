This test works fine when applied to files (commands run from OpenJMLTest/scripttests):

../../OpenJMLsrc/openjml --esc --progress -staticInitWarning -jmltesting --timeout=300 --check-feasibility=precondition,reachable,exit,spec --smt=smt/%%.smt --specs-path ../test/sfbug407 ../test/sfbug407/*.java

but gives a feasibility error when appiled to directories

../../OpenJMLsrc/openjml --esc --progress -staticInitWarning -jmltesting --timeout=300 --check-feasibility=precondition,reachable,exit,spec --smt=smt/%%.smt --specs-path ../test/sfbug407 --dir ../test/sfbug407
