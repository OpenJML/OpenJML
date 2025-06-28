#! /bin/bash

rm -f src/A.class A.class
## Using src/A.java
$OJA --compile src/A.java Test.java

## Using ./A.java
$OJA A.java Test.java

$OJA --rac src/A.java
cp src/A.class .

## Using ./A.class, from src/A.java
$OJA -Xprefer:newer Test.java

## Using ./A.java
$OJA -Xprefer:source Test.java
