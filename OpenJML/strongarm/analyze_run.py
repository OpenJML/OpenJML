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
initial_contract = "BEGIN CONTRACT CLEANUP of"

pipeline_steps = [
    
    "AFTER REMOVING DUPLICATE PRECONDITIONS (VIA SMT)",
    "AFTER REMOVING IMPOSSIBLE SPECIFICATION CASES (VIA SMT)",
    "AFTER PERFORMING LEXICAL SUBSTITUTIONS",
    "AFTER PERFORMING LEXICAL SUBSTITUTIONS II",
    "AFTER REMOVING TAUTOLOGIES OF",
    "AFTER REMOVING CONTRADICTIONS OF",
    "AFTER PRUNING USELESS CLAUSES OF",
    "AFTER REMOVING DEAD ASSIGNMENTS OF",
    "AFTER PERFORMING OPTIMIZED PREMAP BLOCK SUBSTITUTIONS",
    "AFTER PERFORMING ALL PREMAP BLOCK SUBSTITUTIONS",
    "AFTER REMOVING LOCALS OF",
    "AFTER REMOVING SPEC PUBLIC OF",
    "AFTER DOING BACKWARDS PROPAGATION OF",
    "AFTER SIMPLIFYING LABELS OF",
    "AFTER REMOVING DUPLICATE ASSIGNMENTS OF",
    "AFTER FIXING RESULTS",
    "AFTER CLEANING PRESTATE ASSIGNABLES",
    "AFTER REMOVING USELESS POSTCONDITIONS",
    "AFTER PRUNING USELESS CLAUSES OF",
    "AFTER ADDING PURITY",
    "AFTER REDUCTION ANALYSIS",
   
   ]

def extract_method_name_and_loc_and_timing(tag):
    the_tag = tag + " "
    #BEGIN CONTRACT CLEANUP of demo.strongarm.A.cmp(int,int) (24 LOC)
    try:
        out = subprocess.check_output("cat {0} | grep '{1}'".format(file, the_tag), shell=True).decode('utf-8').splitlines()

        methods = []
        locs    = []
        ts      = []
        for line in out:
            parts = line.replace(the_tag, "").split(" ")
            method = parts[0]
            loc    = parts[1][1:]
            timing = parts[3][1:]

            methods.append(method)
            locs.append((method,loc))
            ts.append((method,timing))

        return (methods, locs, ts)
    except subprocess.CalledProcessError:
        return ([],[],[])

def extract_method_name_and_loc(tag):
    the_tag = tag + " "
    #BEGIN CONTRACT CLEANUP of demo.strongarm.A.cmp(int,int) (24 LOC)
    out = subprocess.check_output("cat {0} | grep '{1}'".format(file, the_tag), shell=True).decode('utf-8').splitlines()

    methods = []
    locs    = []
    for line in out:
        parts = line.replace(the_tag, "").split(" ")
        method = parts[0]
        loc    = parts[1][1:]

        methods.append(method)
        locs.append((method,loc))
    return (methods, locs)

# step 1 - get all files we ATTEMPTED to infer.
methods, mloc = extract_method_name_and_loc(start_string)

for m in methods:
    print(m)

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

###
#CFG DEPTH OF org.json.CDL.toString(org.json.JSONArray) (295)

#CFGs

out = subprocess.check_output("cat {0} | grep 'CFG DEPTH OF'".format(file), shell=True).decode('utf-8').splitlines()

cfg = []

for line in out:
    print(line)
    method = line.replace("CFG DEPTH OF ", "")
    parts = method.split(" ")

    method_name = parts[0]
    depth       = int(parts[1][1:-1])
    cfg.append((method_name, depth))

###



skipped = []
try:
    out = subprocess.check_output("cat {0} | grep 'Skipping inference'".format(file), shell=True).decode('utf-8').splitlines()

    
    for line in out:
        method = line.replace("[STRONGARM] Skipping inference for ", "")
        parts = method.split(" ")

        method_name = parts[0]
        skipped.append(method_name)
        print("{0} was skipped".format(method_name))
        

    print("[INFO] Strongarm skipped {0} methods".format(len(skipped)))

except subprocess.CalledProcessError:
    skipped = []


refused = []
try:
    out = subprocess.check_output("cat {0} | grep 'REFUSING TO INFER CONTRACT OF'".format(file), shell=True).decode('utf-8').splitlines()

    
    for line in out:
        method = line.replace("REFUSING TO INFER CONTRACT OF ", "")
        parts = method.split(" ")

        method_name = parts[0]
        refused.append(method_name)
        print("{0} was refused".format(method_name))
        

    print("[INFO] Strongarm refused {0} methods".format(len(refused)))

except subprocess.CalledProcessError:
    refused = []



# figure out the failures next 

timeouts =  []

if not len(methods)-len(completed) == 0:
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


file_tag = datetime.datetime.now().isoformat()

finished = list(map(lambda m : m[0], completed))
times    = dict(completed)
mloc_table     = dict(mloc)
cfg_table     = dict(cfg)


data = {
    'method'   : methods,
    'loc'      : list(map(lambda m : -1 if not m in mloc_table else mloc_table[m], methods)),
    'cfg_depth': list(map(lambda m : -1 if not m in cfg_table else cfg_table[m], methods)),
    'inferred' : list(map(lambda m : m in finished and m not in skipped and m not in refused, methods)),
    'skipped'  : list(map(lambda m : m in skipped, methods)),
    'refused'  : list(map(lambda m : m in refused, methods)), 
    'time'     : list(map(lambda m : -1 if not m in times else times[m], methods)),
    'error'    : list(map(lambda m : not m in timeouts and m not in finished, methods)),
    'timeout'  : list(map(lambda m : m in timeouts, methods))

}

df = pd.DataFrame(data, columns=["method", "loc", "cfg_depth", "inferred", "skipped", "refused", "time", "error", "timeout"])

print(df)

df.to_csv('strongarm-summary-{0}.csv'.format(file_tag), sep=',')

# do for each step of the pipeline 

step_columns = ["method"]

methods_in_pipeline = list(filter(lambda m : m not in skipped and m not in refused and m in finished, methods))

data = {
    'method'   : methods_in_pipeline,
}


for step in pipeline_steps:
    step_name = step.replace("AFTER ", "").replace(" ", "_")

    ms, locs, ts = extract_method_name_and_loc_and_timing(step)
    locs_map = dict(locs)
    ts_map   = dict(ts) 
    data[step_name + "_LOC"] = list(map(lambda m : -1 if not m in ms else locs_map[m], methods_in_pipeline))
    data[step_name + "_TS"]  = list(map(lambda m : -1 if not m in ms else ts_map[m], methods_in_pipeline))

    step_columns.append(step_name + "_LOC")
    step_columns.append(step_name + "_TS")


df = pd.DataFrame(data, columns=step_columns)

print(df)

df.to_csv('strongarm-pipeline-steps-{0}.csv'.format(file_tag), sep=',')



