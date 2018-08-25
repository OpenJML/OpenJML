#!/usr/local/bin/bash

#EVALS=( "junit4" "json-java" "commons-csv" "commons-cli"  )
source strongarm.conf

RUNID=$1 

for E in "${EVALS[@]}"
do
    
    source evals.conf.d/$E.conf
    python extract_fixpoint.py $EVAL_NAME $RUNID

    echo -e "\e[32m[💪🏻 Fixpoint Done ($EVAL_NAME)] \e[0m"    


done