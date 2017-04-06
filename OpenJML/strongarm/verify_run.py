#%%
import numpy as np
import os
import subprocess
import sys 
import pandas as pd


/Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/.p2/pool/plugins/org.hamcrest.core_1.3.0.v201303031735.jar:/Users/jls/Applications/Eclipse-Neon/Eclipse.app/Contents/Eclipse/configuration/org.eclipse.osgi/212/0/.cp/:/Users/jls/Applications/Eclipse-Neon/Eclipse.app/Contents/Eclipse/configuration/org.eclipse.osgi/211/0/.cp/ org.eclipse.jdt.internal.junit.runner.RemoteTestRunner 

javac -classpath /Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin -d bin `find src/test/java -name '*.java'`


javac -classpath bin/:/Users/jls/.p2/pool/plugins/org.junit_4.12.0.v201504281640/junit.jar:/Users/jls/Projects/Strongarm/OpenJML/JMLAnnotations/bin -d bin `find src/test/java -name '*.java'`


JVM_OPTS="-Xmx28G -Xms28G -XX:+UseParallelGC -XX:+AggressiveHeap"
JAVA="java"
#/Library/Java/JavaVirtualMachines/jdk1.8.0_65.jdk/Contents/Home/bin/java 
OPENJML = "/Users/jls/Applications/openjml-0.8.9-20170315/openjml.jar"

#eval_name = sys.argv[1]
eval_name = "JSON-Java" 

summary = "strongarm-summary-{0}.csv".format(eval_name)

df = pd.read_csv(summary) 

df = df[(df["inferred"]==True) & (df["final_contract_loc"] > 0)]

#%%

# step 1 - get all the methods where inference was OK and we actually produced a contract.
methods = list(map(lambda m : m[0:(m.index('('))], df["method"]))

methods
#%%

