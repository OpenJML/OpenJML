## This script is sourced

rm -f src/A.class A.class
## Using src/A.java
$OJA --compile src/A.java Test.java

## Using ./A.java
$OJA A.java Test.java

$OJA --rac src/A.java
cp src/A.class .

## Using ./A.class, from src/A.java
$OJA -cp . -Xprefer:newer Test.java

## Using ./A.java
$OJA -cp . -Xprefer:source Test.java

rm -f src/A.class A.class
