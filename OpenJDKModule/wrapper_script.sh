#!/bin/bash

# Helper script for using OpenJML to infer loop invariants
# Makes slight edits to the outputted file so that it verifies

if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <path_to_java_file>"
  exit 1
fi

rm -f InferredInvariants.java

( set -x; ./openjml "$1" --infer-invariants )

classname=$(basename "$1" .java)

if [ -f InferredInvariants.java ]; then
  # rename the class to InferredInvariants, and delete "public static" from annotations
  ( set -x; sed -i -e "s/${classname}/InferredInvariants/" -e "/^\s*public static $/d" InferredInvariants.java )
fi

