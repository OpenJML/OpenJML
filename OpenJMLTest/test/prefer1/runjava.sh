## This script is sourced

OJB="openjml -java -cp ."

rm -f src/A.class A.class

## Using src/A.java
$OJB src/A.java Test.java

## Using ./A.java
$OJB A.java Test.java

cp src/A.class .

## Using ./A.class, from src/A.java
$OJB -Xprefer:newer Test.java

## Using ./A.java
$OJB -Xprefer:source Test.java

rm -f src/A.class A.class
