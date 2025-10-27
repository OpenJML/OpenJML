#! /bin/bash

rm -f src/A.class A.class
## Using src/A.java
$OJA -java src/A.java Test.java

## Using ./A.java
$OJA -java A.java Test.java

cp src/A.class .

## Using ./A.class, from src/A.java
$OJA -java -Xprefer:newer Test.java

## Using ./A.java
$OJA -java -Xprefer:source Test.java
