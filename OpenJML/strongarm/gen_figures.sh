#!/usr/local/bin/bash

source strongarm.conf

RUN_NAME=""

if [ $# -eq 1 ]; then
    echo "Overriding the base dir with parameter: $1"
    RUN_NAME=$1
    mkdir runs/$RUN_NAME/figures 

else
    echo "Please specify run-id."
    exit 
fi


for e in "${EVALS[@]}"
do
    source evals.conf.d/$e.conf


    if [ ! -f evals.conf.d/$e.conf ]; then
        echo "Configuration File evals.conf.d/$e.conf not found."
        exit 
    fi

    if [ ! -f runs/$RUN_NAME/strongarm-summary-$EVAL_NAME.csv ]; then
        echo "Missing CSV data from $EVAL_NAME. Skipping..."
        continue
    fi


    echo -e "\e[32m[💪🏻 Creating Figure Directory For: $EVAL_NAME] "    

    mkdir runs/$RUN_NAME/figures/$EVAL_NAME

    

done


echo -e "\e[32m[Combined Analysis] \e[0mAnalyzing Results..."    


mkdir runs/$RUN_NAME/figures/Combined

rm runs/$RUN_NAME/strongarm-summary-Combined.csv 2>/dev/null 
rm runs/$RUN_NAME/strongarm-pipeline-steps-Combined.csv 2>/dev/null

./run_combined_analysis.sh runs/$RUN_NAME/

python.app create_paper_graphs.py $RUN_NAME "${EVALS[@]}" Combined