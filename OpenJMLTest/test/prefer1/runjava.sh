#! /bin/bash

rm -f src/A.class A.class
## Using src/A.java
openjml -java src/A.java Test.java

## Using ./A.java
openjml -java A.java Test.java

cp src/A.class .

## Using ./A.class, from src/A.java
openjml -java -Xprefer:newer Test.java

## Using ./A.java
openjml -java -Xprefer:source Test.java
