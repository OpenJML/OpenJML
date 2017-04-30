#!/usr/local/bin/bash


source strongarm.conf



JAVA="java"


if [ $# -eq 2 ]; then
    echo "Overriding test suite with parameter: $1"
    EVALS=( $1 )
    TAG=$2
else 
    TAG=$1
fi

for e in "${EVALS[@]}"
do

    if [ ! -f evals.conf.d/$e.conf ]; then
        echo "Configuration File evals.conf.d/$e.conf not found."
        exit 
    fi

    source evals.conf.d/$e.conf

    
    echo -e "\e[32m Checking $EVAL_NAME with tag $TAG...\e[0m"
    
    METHODS=`python sample.py $EVAL_NAME $TAG`

    for method in $METHODS
    do
    echo -e "\e[32m [ESC] \e[0m[$method]"

    #set -x 
    ($JAVA -Dopenjml.eclipseSpecsProjectLocation=/Users/jls/Projects/Strongarm/OpenJML/Specs $JVM_OPTS  -Dfile.encoding=UTF-8 -classpath /Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJDK/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin-runtime:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/.p2/pool/plugins/org.hamcrest.core_1.3.0.v201303031735.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.annotation_2.1.0.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.core_3.12.2.v20161117-1814.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.apt_1.2.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.tool_1.1.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.core.runtime_3.12.0.v20160606-1342.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.common_3.8.0.v20160509-1230.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.registry_3.6.100.v20160223-2218.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi_3.11.2.v20161107-1947.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi.compatibility.state_1.0.200.v20160504-1419.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/jSMTLIB.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/otherlibs/jpaul-2.5.1.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/otherlibs/javax.mail.jar org.jmlspecs.openjml.Main -esc  -code-math=java -no-internalSpecs -method $method -minQuant  $STRONGARM_ARGS -specspath $SPECS_PATH $SRC_FILES )
    
    
    #set +x
    done


done

