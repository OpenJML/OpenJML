#!/usr/local/bin/bash

EXPERIMENT="2pac"
DATE=`date "+%F.%H%M%S.%N"`

# create the output directory
OUTDIR=strongarm/runs/$EXPERIMENT-$DATE/

echo "Creating Experiment Output Directory: $OUTDIR"
mkdir -p $OUTDIR

FIXPOINTS=(0 1 2 3)

#EVALS=( "junit4" "json-java" "commons-csv" "commons-cli"  )
source strongarm/strongarm.conf

if [ $# -eq 1 ]; then
    echo "Overriding test suite with parameter: $1"
    EVALS=( $1 )
fi

for E in "${EVALS[@]}"
do
    

    source strongarm/evals.conf.d/$E.conf

    for F in "${FIXPOINTS[@]}"
    do
        echo "Fixpoint $F for Eval: $E..."

        # run the eval
        ./strongarm/run_eval.sh $E 

        # after it's done, move it's generated csv files 
        FILES=`ls strongarm/strongarm*$EVAL_NAME.csv`
        for file in $FILES
        do
            new_ext=".$F.csv"
            dest="${file/\.csv/$new_ext}"
            dest=`basename $dest`
            dest="$OUTDIR/$dest"
            #cp $file 
            echo "Moving $file to $dest"
            mv $file $dest 
        done

        echo -e "\e[32m[💪🏻 Fixpoint $F Done ($EVAL_NAME)] \e[0m"    

    done


done