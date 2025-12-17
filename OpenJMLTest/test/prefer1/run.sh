## This script is sourced

rm -f src/A.class A.class
## Using src/A.java
openjml --compile src/A.java Test.java

## Using ./A.java
openjml A.java Test.java

openjml --rac src/A.java
cp src/A.class .

## Using ./A.class, from src/A.java
openjml -cp . -Xprefer:newer Test.java

## Using ./A.java
openjml -cp . -Xprefer:source Test.java

rm -f src/A.class A.class
