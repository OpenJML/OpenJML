#!/usr/local/bin/bash


EVALS=( "json-java" "commons-csv" "commons-cli" )


for e in "${EVALS[@]}"
do
    source strongarm/evals.conf.d/$e.conf

    echo -e "\e[4mFigures For $EVAL_NAME...\e[0m"

    set -x
    # next, build the summary data.
    cd strongarm 
    python.app process_analysis.py $EVAL_NAME
    cd ../
    set +x
    echo -e "\e[32m[💪🏻 Done: $EVAL_NAME] "    


done


echo -e "\e[32m[Combined Analysis] \e[0mAnalyzing Results..."    


cd strongarm 

rm strongarm-summary-Combined.csv 2>/dev/null 
rm strongarm-pipeline-steps-Combined.csv 2>/dev/null


./run_combined_analysis.sh 
python.app process_analysis.py Combined  2>/dev/null
cd ../