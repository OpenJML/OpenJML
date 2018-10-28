#!/usr/local/bin/bash

source strongarm.conf 



if [ $# -eq 1 ]; then
    echo "Overriding with parameter: $1"
    EVALS=( $1 )
fi



for e in "${EVALS[@]}"
do

    if [ ! -f evals.conf.d/$e.conf ]; then
        echo "Configuration File evals.conf.d/$e.conf not found."
        exit 
    fi

    source evals.conf.d/$e.conf

    echo -e "\e[4mProcessing specs for $EVAL_NAME...\e[0m"
    
    CHECKS=( "requires" "ensures" "assignable" "@Pure" "forall" "decreasing" "maintaining" )
    for check in "${CHECKS[@]}"
    do
        CT=`grep -w $check $JML_FILES | wc -l`
        echo "$EVAL_NAME: $check $CT"
    done
    
    echo -e "\e[32m[Analysis Complete] \e[0m"    

done

