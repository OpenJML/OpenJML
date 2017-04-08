#!/usr/local/bin/bash


source strongarm.conf


# for each eval, we want to run all of the tests associated with that 
# library. We save the output to a file and then pass it to a second program that
# inspects the trace for errors related to specifications. 

JAVA="java"
#/Library/Java/JavaVirtualMachines/jdk1.8.0_65.jdk/Contents/Home/bin/java 


if [ $# -eq 1 ]; then
    echo "Overriding test suite with parameter: $1"
    EVALS=( $1 )
fi

EVALS=( "commons-cli" )

for e in "${EVALS[@]}"
do

    if [ ! -f evals.conf.d/$e.conf ]; then
        echo "Configuration File evals.conf.d/$e.conf not found."
        exit 
    fi

    source evals.conf.d/$e.conf

    echo -e "\e[4m Compiling $EVAL_NAME...\e[0m"
    set +x
    
    # compile each of the filesets
    for fileset in "${COMPILE_FILES[@]}"
    do 
        set -x 

        # RAC compile it.
        (cd $SOURCE_ROOT; $JAVA -Dopenjml.eclipseSpecsProjectLocation=/Users/jls/Projects/Strongarm/OpenJML/Specs $JVM_OPTS  -Dfile.encoding=UTF-8 -classpath /Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJDK/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin-runtime:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/.p2/pool/plugins/org.hamcrest.core_1.3.0.v201303031735.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.annotation_2.1.0.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.core_3.12.2.v20161117-1814.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.apt_1.2.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.tool_1.1.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.core.runtime_3.12.0.v20160606-1342.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.common_3.8.0.v20160509-1230.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.registry_3.6.100.v20160223-2218.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi_3.11.2.v20161107-1947.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi.compatibility.state_1.0.200.v20160504-1419.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/jSMTLIB.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/otherlibs/jpaul-2.5.1.jar org.jmlspecs.openjml.Main -no-internalSpecs -rac -method org.apache.commons.cli.OptionGroup.* -nullableByDefault -classpath bin/:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin -d bin $G2)

        # Javac the tests. 
        (cd $SOURCE_ROOT; javac -classpath bin/:/Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJDK/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin-runtime:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/.p2/pool/plugins/org.hamcrest.core_1.3.0.v201303031735.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.annotation_2.1.0.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.core_3.12.2.v20161117-1814.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.apt_1.2.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.tool_1.1.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.core.runtime_3.12.0.v20160606-1342.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.common_3.8.0.v20160509-1230.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.registry_3.6.100.v20160223-2218.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi_3.11.2.v20161107-1947.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi.compatibility.state_1.0.200.v20160504-1419.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/jSMTLIB.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/otherlibs/jpaul-2.5.1.jar -d bin $G1)
        

        set +x
        for t in "${TESTS[@]}"
        do
            set -x
            
            (cd $SOURCE_ROOT; $JAVA -cp bin/:/Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJDK/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin-runtime:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/.p2/pool/plugins/org.hamcrest.core_1.3.0.v201303031735.jar org.junit.runner.JUnitCore $t)

            set +x
        done 

        set +x
    done

done

