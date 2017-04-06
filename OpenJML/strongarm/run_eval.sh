#!/usr/local/bin/bash

TIMEOUT=300
MAX_DEPTH=1
JVM_OPTS="-Xmx10G -Xms1G -XX:+UseG1GC"
JAVA=java
#/Library/Java/JavaVirtualMachines/jdk1.8.0_65.jdk/Contents/Home/bin/java 

#killall -9 tail 

#EVALS=( "junit4" "json-java" "commons-csv" "commons-cli"  )
source strongarm/strongarm.conf 



if [ $# -eq 1 ]; then
    echo "Overriding test suite with parameter: $1"
    EVALS=( $1 )
fi



for e in "${EVALS[@]}"
do

    if [ ! -f strongarm/evals.conf.d/$e.conf ]; then
        echo "Configuration File strongarm/evals.conf.d/$e.conf not found."
        exit 
    fi

    source strongarm/evals.conf.d/$e.conf

    echo -e "\e[4mEvaluating $EVAL_NAME...\e[0m"
    echo "Removing Previous Runs..."
    set -x
  
    rm $JML_FILES 2>/dev/null
    rm $FIGURES_DIR/* 2>/dev/null
    rm strongarm/strongarm*$EVAL_NAME.csv 2>/dev/null   
    rm strongarm/$TRACE_RAW 2>/dev/null
    rm strongarm/$TRACE_COMPACT 2>/dev/null




    set +x

    echo -e "\e[32m[Cleanup Complete] \e[0mStarting Evaluation..."    



    touch strongarm/$TRACE_RAW

    tail -f strongarm/$TRACE_RAW | GREP_COLOR='01;32' egrep --color "STARTING INFERENCE" & 2>/dev/null 

    APID=$!

    tail -f strongarm/$TRACE_RAW | egrep --color "ABORTED" & 2>/dev/null 

    BPID=$!

    set -x

    $JAVA -Dopenjml.eclipseSpecsProjectLocation=/Users/jls/Projects/Strongarm/OpenJML/Specs $JVM_OPTS  -Dfile.encoding=UTF-8 -classpath /Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJDK/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin-runtime:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/.p2/pool/plugins/org.hamcrest.core_1.3.0.v201303031735.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.annotation_2.1.0.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.core_3.12.2.v20161117-1814.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.apt_1.2.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.tool_1.1.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.core.runtime_3.12.0.v20160606-1342.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.common_3.8.0.v20160509-1230.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.registry_3.6.100.v20160223-2218.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi_3.11.2.v20161107-1947.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi.compatibility.state_1.0.200.v20160504-1419.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/jSMTLIB.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/otherlibs/jpaul-2.5.1.jar org.jmlspecs.openjml.Main -infer-timeout=$TIMEOUT -infer-default-preconditions  -infer-max-depth=$MAX_DEPTH -minQuant -infer -infer-debug $STRONGARM_ARGS -infer-persist -verbose -progress -specspath $SPECS_PATH $SRC_FILES > strongarm/$TRACE_RAW

    set +x
    kill -9 $APID 2>/dev/null 
    kill -9 $BPID 2>/dev/null 

    echo -e "\e[32m[💪🏻 Specifications Computed] \e[0mAnalyzing Results..."    

    set -x
    # next, build the summary data.
    cd strongarm 
    python preprocess_data.py $TRACE_RAW $EVAL_NAME
    # then, build the charts.
    #python.app process_analysis.py $EVAL_NAME
    cd ../
    set +x
    echo -e "\e[32m[💪🏻 Done: $EVAL_NAME] "    


done


echo -e "\e[32m[Combined Analysis] \e[0mAnalyzing Results..."    


cd strongarm 

rm strongarm-summary-Combined.csv 2>/dev/null 
rm strongarm-pipeline-steps-Combined.csv 2>/dev/null


./run_combined_analysis.sh 
#python.app process_analysis.py Combined  2>/dev/null
cd ../