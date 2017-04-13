#!/usr/local/bin/bash

# Clean up the various defects in OpenJML's spec formatter. 


#EVALS=( "junit4" "json-java" "commons-csv" "commons-cli"  )
source strongarm.conf

if [ $# -eq 1 ]; then
    echo "Overriding test suite with parameter: $1"
    EVALS=( $1 )
fi

rm /Users/jls/Projects/Analysis/junit4/src/main/java/junit/framework/Protectable.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/matchers/JUnitMatchers.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/rules/ErrorCollector.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/internal/matchers/StacktracePrintingMatcher.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/experimental/theories/ParameterSignature.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/junit/runner/TestRunListener.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/AssumptionViolatedException.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/Assume.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/Assert.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/experimental/theories/internal/SpecificDataPointsSupplier.jml

rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/runners/model/TestClass.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/runners/model/FrameworkField.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/runners/model/FrameworkMethod.jml
rm /Users/jls/Projects/Analysis/junit4/src/main/java/org/junit/runner/Description.jml



for E in "${EVALS[@]}"
do
    
    echo -e "\e[32m[Processing ($E)] \e[0m" 

    source evals.conf.d/$E.conf

    for file in $JML_FILES
    do
        echo -e "Processing: \e[4m $E:$file \e[0m" 

        #perl -i -pe 's/\s+=.*;$/;/sg' $file

        perl -i -0777 -pe 's/public <E extends Enum<E>>E getEnum\(\@NonNull(.){1,7}Class<E> clazz, \@NonNull(.){1,7}String key\) throws JSONException;//sg' $file  

        perl -i -0777 -pe 's/\@Pure(.){1,7}public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, int index, \@NonNull(.){1,7}E defaultValue\);//sg' $file
  
        perl -i -0777 -pe 's/\@Pure(.){1,7}public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, int index\);//sg' $file

        perl -i -0777 -pe 's/\@Pure(.){1,7}public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, \@NonNull(.){1,7}String key\);//sg' $file

        perl -i -0777 -pe 's/\@Pure(.){1,7}public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, \@NonNull(.){1,7}String key, \@NonNull(.){1,7}E defaultValue\);//sg' $file

        ####
        perl -i -0777 -pe 's/public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, int index, \@NonNull(.){1,7}E defaultValue\);//sg' $file
  
        perl -i -0777 -pe 's/public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, int index\);//sg' $file

        perl -i -0777 -pe 's/public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, \@NonNull(.){1,7}String key\);//sg' $file

        perl -i -0777 -pe 's/public <E extends Enum<E>>E optEnum\(\@NonNull(.){1,7}Class<E> clazz, \@NonNull(.){1,7}String key, \@NonNull(.){1,7}E defaultValue\);//sg' $file

        ###



        perl -i -0777 -pe 's/public <E extends Enum<E>>E getEnum\(\@NonNull(.){1,7}Class<E> clazz, int index\) throws JSONException;//sg' $file  

        perl -i -0777 -pe 's/<T extends Annotation>T getAnnotation\(\@NonNull(.){1,7}Class<T> annotationType\);//sg' $file  

        perl -i -0777 -pe 's/\!this.canUseSuiteMethod/\!canUseSuiteMethod/gs' $file

        perl -i -0777 -pe 's/== RUNTIME_MX_BEAN/== RuntimeHolder\.RUNTIME_MX_BEAN/gs' $file
        perl -i -0777 -pe 's/== THREAD_MX_BEAN/== ThreadHolder\.THREAD_MX_BEAN/gs' $file

        perl -i -0777 -pe 's/== THREAD_MX_BEAN/== ThreadHolder\.THREAD_MX_BEAN/gs' $file

        perl -i -077 -pe 's/\(isThreadCpuTimeSupportedMethod \!= null\)/\(Holder.isThreadCpuTimeSupportedMethod \!= null\)/gs' $file 

        perl -i -0777 -pe 's/result == CONSTRUCTOR/result == InjectionType.CONSTRUCTOR/gs' $file
        perl -i -0777 -pe 's/result == FIELD/result == InjectionType.FIELD/gs' $file

        perl -i -077 -pe 's/\@Pure(.){1,7}private static <T>List<T> asReversedList\(\@NonNull(.){1,7}final List<T> list\);//gs' $file 

       perl -0777 -i -pe "s/\(E\)token/token/sg" $file

    done

    echo -e "\e[32m[💪🏻 Done ($E)] \e[0m" 


done 