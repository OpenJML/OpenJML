#!/usr/local/bin/bash


EVAL_JSON_JAVA=false
EVAL_COMMONS_CSV=true

if [ "$EVAL_JSON_JAVA" = true ] ; then
    echo -e "\e[4mEvaluating JSON-Java...\e[0m"
    echo "Removing Previous Runs..."
    set -x

    rm /Users/jls/Projects/Analysis/json-java/src/org/json/*.jml 
    rm strongarm/figures/JSON-Java/*
    rm strongarm/strongarm*JSON-Java.csv
    rm strongarm/run.out.json-java 
    rm strongarm/run.out.json-java.compact

    set +x

    echo -e "\e[32m[Cleanup Complete] \e[0mStarting Evaluation..."    



    touch strongarm/run.out.json-java

    tail -f strongarm/run.out.json-java | GREP_COLOR='01;32' egrep --color "STARTING INFERENCE" &

    APID=$!

    tail -f strongarm/run.out.json-java | egrep --color "ABORTED" &


    BPID=$!

    set -x

    /Library/Java/JavaVirtualMachines/jdk1.8.0_65.jdk/Contents/Home/bin/java -Dopenjml.eclipseSpecsProjectLocation=/Users/jls/Projects/Strongarm/OpenJML/Specs -Xmx10G -Xms1G -Dfile.encoding=UTF-8 -classpath /Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJDK/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin-runtime:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/.p2/pool/plugins/org.hamcrest.core_1.3.0.v201303031735.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.annotation_2.1.0.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.core_3.12.2.v20161117-1814.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.apt_1.2.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.tool_1.1.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.core.runtime_3.12.0.v20160606-1342.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.common_3.8.0.v20160509-1230.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.registry_3.6.100.v20160223-2218.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi_3.11.2.v20161107-1947.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi.compatibility.state_1.0.200.v20160504-1419.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/jSMTLIB.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/otherlibs/jpaul-2.5.1.jar org.jmlspecs.openjml.Main -infer-timeout=300 -infer-default-preconditions -infer-max-depth=300 -minQuant -infer -infer-debug -infer-persist -verbose -progress -specspath /Users/jls/Projects/Analysis/json-java/src/ /Users/jls/Projects/Analysis/json-java/src/org/json/CDL.java /Users/jls/Projects/Analysis/json-java/src/org/json/Cookie.java /Users/jls/Projects/Analysis/json-java/src/org/json/CookieList.java /Users/jls/Projects/Analysis/json-java/src/org/json/HTTP.java /Users/jls/Projects/Analysis/json-java/src/org/json/HTTPTokener.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONArray.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONException.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONML.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONObject.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONPointer.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONPointerException.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONString.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONStringer.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONTokener.java /Users/jls/Projects/Analysis/json-java/src/org/json/JSONWriter.java /Users/jls/Projects/Analysis/json-java/src/org/json/Property.java /Users/jls/Projects/Analysis/json-java/src/org/json/XML.java /Users/jls/Projects/Analysis/json-java/src/org/json/XMLTokener.java > strongarm/run.out.json-java

    set +x
    kill -9 $APID 
    kill -9 $BPID 

    echo -e "\e[32m[Specifications Computed] \e[0mAnalyzing Results..."    

    set -x
    # next, build the summary data.
    cd strongarm 
    python preprocess_data.py run.out.json-java JSON-Java
    # then, build the charts.
    python.app process_analysis.py JSON-Java
    cd ../
    set +x
    echo -e "\e[32m[Done: JSON-Java] "    

fi 


if [ "$EVAL_COMMONS_CSV" = true ] ; then
    echo -e "\e[4mEvaluating Commons-CSV...\e[0m"
    echo "Removing Previous Runs..."
    set -x


    rm /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/*.jml
    rm strongarm/figures/Commons-CSV/*
    rm strongarm/strongarm*Commons-CSV.csv
    rm strongarm/run.out.commons-csv 
    rm strongarm/run.out.commons-csv.compact 
    set +x

    echo -e "\e[32m[Cleanup Complete] \e[0mStarting Evaluation..."

    touch strongarm/run.out.commons-csv 

    tail -f strongarm/run.out.commons-csv | GREP_COLOR='01;32' egrep --color "STARTING INFERENCE" &
    
    APID=$!

    tail -f strongarm/run.out.commons-csv | egrep --color "ABORTED" &

    BPID=$!

    set -x
    
    /Library/Java/JavaVirtualMachines/jdk1.8.0_65.jdk/Contents/Home/bin/java -Dopenjml.eclipseSpecsProjectLocation=/Users/jls/Projects/Strongarm/OpenJML/Specs -Xmx10G -Xms1G -Dfile.encoding=UTF-8 -classpath /Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJDK/bin:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin-runtime:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/bin:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/.p2/pool/plugins/org.hamcrest.core_1.3.0.v201303031735.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.annotation_2.1.0.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.core_3.12.2.v20161117-1814.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.apt_1.2.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.jdt.compiler.tool_1.1.100.v20160418-1457.jar:/Users/jls/.p2/pool/plugins/org.eclipse.core.runtime_3.12.0.v20160606-1342.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.common_3.8.0.v20160509-1230.jar:/Users/jls/.p2/pool/plugins/org.eclipse.equinox.registry_3.6.100.v20160223-2218.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi_3.11.2.v20161107-1947.jar:/Users/jls/.p2/pool/plugins/org.eclipse.osgi.compatibility.state_1.0.200.v20160504-1419.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/jSMTLIB.jar:/Users/jls/Projects/Strongarm/OpenJML/OpenJML/OpenJML/otherlibs/jpaul-2.5.1.jar org.jmlspecs.openjml.Main -infer-timeout=300 -infer-default-preconditions -infer-max-depth=300 -minQuant -infer -infer-debug -infer-persist -verbose -progress -specspath /Users/jls/Projects/Analysis/commons-csv/src/ /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/Assertions.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/Constants.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/CSVFormat.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/CSVParser.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/CSVPrinter.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/CSVRecord.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/ExtendedBufferedReader.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/Lexer.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/QuoteMode.java /Users/jls/Projects/Analysis/commons-csv/src/org/apache/commons/csv/Token.java > strongarm/run.out.commons-csv    

    set +x

    kill -9 $APID 
    kill -9 $BPID 
    
    echo -e "\e[32m[Specifications Computed] \e[0mAnalyzing Results..."    


    set -x
    # next, build the summary data.
    cd strongarm 
    python preprocess_data.py run.out.commons-csv Commons-CSV
    # then, build the charts.
    python.app process_analysis.py Commons-CSV
    cd ../

    set +x

    echo -e "\e[32m[Done: Commons-CSV] "    

fi 