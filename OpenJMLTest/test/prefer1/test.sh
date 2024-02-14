#! /usr/bin/env bash

FILE="$BASH_SOURCE[0]"
DIR=`dirname "$FILE"`
cd "$DIR"

. ./runjava.sh &> actual
diff actual expected || { echo FAILED; exit 1; }
. ./run.sh &> actual
diff actual expected || { echo FAILED; exit 1; }
rm -f actual
