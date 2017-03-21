#/usr/bin/env python

#note this script requires Python 3

#%%
import numpy as np
import os
import subprocess
import sys 
import pandas as pd
# first argument should be the log file from strongarm
#file = sys.argv[1]
file = "run.out"
# everything we ATTEMPTED
skip_string = "Skipping contract inference of"
start_string = "STARTING INFERENCE OF"
timeout = "ABORTED INFERENCE OF"
exception = "Inference ABORTED"

#out = subprocess.check_output("cat {0} | grep 'Completed inference of'".format(file), shell=True).splitlines()


# step 1 - get all files we ATTEMPTED to infer.
out = subprocess.check_output("cat {0} | grep 'STARTING INFERENCE OF'".format(file), shell=True).decode('utf-8').splitlines()

methods = []

for line in out:
    method = line.replace("STARTING INFERENCE OF ", "")
    methods.append(method)
    print(method)


print("[INFO] Strongarm attempted to infer {0} Methods.".format(len(methods))) 

# step 2 - ok find out which ones we actually inferred. 
out = subprocess.check_output("cat {0} | grep 'Completed inference of'".format(file), shell=True).decode('utf-8').splitlines()

completed = []

for line in out:
    method = line.replace("Completed inference of ", "")
    parts = method.split(" ")

    method_name = parts[0]
    ts          = int(parts[1].replace("(", ""))
    completed.append((method_name, ts))

    print("{0} was inferred in {1} ms".format(method_name, ts))
    

print("[INFO] Strongarm failed to infer {0} methods".format(len(methods)-len(completed)))


# figure out the failures next 

timeouts =  []

out = subprocess.check_output("cat {0} | grep '{1}'".format(file, timeout), shell=True).decode('utf-8').splitlines()

for line in out:
    parts = line.split(" ")

    method_name = parts[3][0:-1]
    timeouts.append(method_name)
    print("{0} was ABORTED becase it timed out during inference.".format(method_name))
    
print("[INFO] A total of {0} methods could not be inferred because they timed out during inference.".format(len(timeouts)))


#%%

# highlevel data 
import datetime

finished = list(map(lambda m : m[0], completed))
times    = dict(completed)

data = {
    'method'   : methods,
    'inferred' : list(map(lambda m : m in finished, methods)),
    'time'     : list(map(lambda m : -1 if not m in times else times[m], methods)),
    'error'    : list(map(lambda m : not m in timeouts and m not in finished, methods)),
    'timeout'  : list(map(lambda m : m in timeouts, methods))
}

df = pd.DataFrame(data, columns=["method", "inferred", "time", "error", "timeout"])

print(df)

df.to_csv('run-summary-{0}.csv'.format(datetime.datetime.now().isoformat()), sep=',')

# do for each step of the pipeline 

