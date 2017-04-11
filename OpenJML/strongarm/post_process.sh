#!/usr/local/bin/bash

# Clean up the various defects in OpenJML's spec formatter. 


#EVALS=( "junit4" "json-java" "commons-csv" "commons-cli"  )
source strongarm.conf

if [ $# -eq 1 ]; then
    echo "Overriding test suite with parameter: $1"
    EVALS=( $1 )
fi

rm /Users/jls/Projects/Analysis/junit4/src/main/java/junit/framework/Protectable.jml

for E in "${EVALS[@]}"
do
    
    echo -e "\e[32m[Processing ($E)] \e[0m" 

    source evals.conf.d/$E.conf

    for file in $JML_FILES
    do
        echo -e "Processing: \e[4m $E:$file \e[0m" 

        perl -i -0777 -pe 's/public <E extends Enum<E>>E getEnum\(\@NonNull(.){1,7}Class<E> clazz, \@NonNull(.){1,7}String key\) throws JSONException;//sg' $file  

        perl -i -0777 -pe 's/\@Pure(.){1,7}public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, int index, \@NonNull(.){1,7}E defaultValue\);//sg' $file
  
        perl -i -0777 -pe 's/\@Pure(.){1,7}public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, int index\);//sg' $file

        perl -i -0777 -pe 's/\@Pure(.){1,7}public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, \@NonNull(.){1,7}String key\);//sg' $file

        perl -i -0777 -pe 's/\@Pure(.){1,7}public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, \@NonNull(.){1,7}String key, \@NonNull(.){1,7}E defaultValue\);//sg' $file

        perl -i -0777 -pe 's/public <E extends Enum<E>>E getEnum\(\@NonNull(.){1,7}Class<E> clazz, int index\) throws JSONException;//sg' $file  



        perl -i -0777 -pe 's/\(E\)token/token/sg' $file

    done

    echo -e "\e[32m[💪🏻 Done ($E)] \e[0m" 


done 