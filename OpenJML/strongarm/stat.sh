#!/usr/local/bin/bash

source strongarm.conf 

#EVALS=( "junit4" "json-java" "commons-csv" "commons-cli"  )

BUFFER="Test Started"

for E in "${EVALS[@]}"
do

    # compute started, completed, and aborted.
    RAW=run.out.$E



    if [ -f $RAW ]; then

        file=$RAW

        started=$(grep "STARTING INFERENCE" $file | wc -l)

        BUFFER=$BUFFER$'\n'"$E $started"

    fi
done


echo "$BUFFER" | column -t
