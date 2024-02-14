#! /bin/bash

rm -f src/A.class A.class
## Using src/A.java
openjml --compile src/A.java Test.java

## Using ./A.java
openjml A.java Test.java

openjml --rac src/A.java
cp src/A.class .

## Using ./A.class, from src/A.java
openjml -Xprefer:newer Test.java

## Using ./A.java
openjml -Xprefer:source Test.java
