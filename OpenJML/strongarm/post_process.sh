#!/usr/local/bin/bash

# Clean up the various defects in OpenJML's spec formatter. 


#EVALS=( "junit4" "json-java" "commons-csv" "commons-cli"  )
source strongarm.conf

if [ $# -eq 1 ]; then
    echo "Overriding test suite with parameter: $1"
    EVALS=( $1 )
fi

for E in "${EVALS[@]}"
do
    
    echo -e "\e[32m[Processing ($E)] \e[0m" 

    source evals.conf.d/$E.conf


    for file in $JML_FILES
    do
        echo -e "Processing: \e[4m $E:$file \e[0m" 

        perl -i -0777 -pe 's/private enum.*\{[^\}]*\}//gs' $file        
        perl -i -0777 -pe 's/public enum.*\{[^\}]*\}//gs' $file
        perl -i -0777 -pe 's/enum.*\{[^\}]*\}//gs' $file
        

    done

    echo -e "\e[32m[💪🏻 Done ($E)] \e[0m" 


done 