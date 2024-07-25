This test works fine when applied to files:

/Users/davidcok/projects/OpenJML21/OpenJML/OpenJMLTest/scripttests/../../OpenJML21/openjml --esc --progress -staticInitWarning -jmltesting --timeout=300 --check-feasibility=precondition,reachable,exit,spec --smt=smt/%%.smt --specs-path ../test/sfbug407 ../test/sfbug407/*.java

but gives a feasibility error when appiled to directories

/Users/davidcok/projects/OpenJML21/OpenJML/OpenJMLTest/scripttests/../../OpenJML21/openjml --esc --progress -staticInitWarning -jmltesting --timeout=300 --check-feasibility=precondition,reachable,exit,spec --smt=smt/%%.smt --specs-path ../test/sfbug407 --dir ../test/sfbug407
