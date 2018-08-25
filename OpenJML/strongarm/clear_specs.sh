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

    echo -e "\e[4mRemoving specs for $EVAL_NAME...\e[0m"
    set -x
  
    rm $JML_FILES 

    set +x

    echo -e "\e[32m[Cleanup Complete] \e[0m"    

done

