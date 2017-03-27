#!/usr/local/bin/bash

# step 1 -- take all the summary csvs and stick them together. 

echo "Combining Summary Files..."

FILES=strongarm-summary*.csv
COUNT=0

for f in $FILES
do
    echo -e "\e[32m[Adding] \e[0m$f..."    

    if [ $COUNT -eq 0 ]; then
        cat $f > strongarm-summary-Combined.csv
    else 
        tail -n +2 $f >> strongarm-summary-Combined.csv
    fi
    
    ((COUNT++))
done

echo "Combining Pipeline Files..."




FILES=strongarm-pipeline*.csv
COUNT=0

for f in $FILES
do
    echo -e "\e[32m[Adding] \e[0m$f..."    

    if [ $COUNT -eq 0 ]; then
        cat $f > strongarm-pipeline-steps-Combined.csv
    else 
        tail -n +2 $f >> strongarm-pipeline-steps-Combined.csv
    fi
    
    ((COUNT++))
done
