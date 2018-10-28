#%%
import numpy as np
import os
import subprocess
import sys 
import pandas as pd
import datetime

import re
import utils as util

# first argument should be the log file from strongarm
#f = "run.out.json-java" 
#test_case_name = "Commons-CSV"

f = sys.argv[1]
test_case_name = sys.argv[2]
file = f + ".compact"

out = subprocess.check_output("grep -F -f patterns.txt {0} > {1}".format(f, file), shell=True)


print("Finished Creating Compact file...")


# everything we ATTEMPTED
start_tag = "STARTING INFERENCE OF"
timeout_tag = "ABORTED INFERENCE OF"
exception_tag = "Inference ABORTED"
complete_tag = "Completed inference of"
cfg_depth_tag = "CFG DEPTH OF"
skipped_tag="[STRONGARM] Skipping inference for"
skipped_tag2="DID NOT INFER POSTCONDITION"
refused_tag="REFUSING TO INFER CONTRACT OF"
initial_tag = "INITIAL CONTRACT LENGTH"
final_contract_tag   = "FINISHED INFERENCE OF"


pipeline_steps = [
    "AFTER REMOVING DUPLICATE PRECONDITIONS (VIA SMT)",
    "AFTER REMOVING IMPOSSIBLE SPECIFICATION CASES (VIA SMT)",
    "AFTER PERFORMING LEXICAL SUBSTITUTIONS",
#    "AFTER PERFORMING LEXICAL SUBSTITUTIONS II",
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
    "AFTER REMOVING CONTRADICTIONS II OF",    
    "AFTER CLEANING PRESTATE ASSIGNABLES",
    "AFTER REMOVING USELESS POSTCONDITIONS",
    "AFTER PRUNING USELESS CLAUSES II OF",
    "AFTER ADDING PURITY",
    "AFTER REDUCTION ANALYSIS",
   ]

# step 1 - get all files we ATTEMPTED to infer.
methods, mloc = util.extract_method_name_and_loc(file, start_tag)

for m in methods:
    print("[INFO] " + m)

print("[INFO] Strongarm attempted to infer {0} Methods.".format(len(methods))) 

# step 2 - ok find out which ones we actually inferred. 
_, completed = util.extract_method_name_and_ts(file, complete_tag)

for method_name,ts in completed:
    print("{0} was inferred in {1} ms".format(method_name, ts))
    

print("[INFO] Strongarm failed to infer {0} methods".format(len(methods)-len(completed)))

# step 3 - CFG Depths 

cfg = util.extract_method_name_and_metric(file, cfg_depth_tag)

# step 4 - skipped methods 

skipped = util.extract_method_name(file, skipped_tag)
skipped2 = util.extract_method_name_skipped(file, skipped_tag2)
 
skipped = skipped + skipped2

for m in skipped:
    print("{0} was skipped".format(m))


print("[INFO] Strongarm skipped {0} methods".format(len(skipped)))

# step 5 - refused methods. 

refused = util.extract_method_name(file, refused_tag)

for m in refused:
    print("{0} was skipped".format(m))


print("[INFO] Strongarm refused {0} methods".format(len(refused)))


# step 6 - timeouts 

timeouts = []

timeouts = util.extract_method_name(file, timeout_tag)

for m in timeouts:
    print("{0} was ABORTED becase it timed out during inference.".format(m))

print("[INFO] A total of {0} methods could not be inferred because they timed out during inference.".format(len(timeouts)))


# step 7 - initial/final contract lengths 

_, initial_locs, _ = util.extract_method_name_and_loc_and_timing(file, initial_tag)
_, final_locs      = util.extract_method_name_and_loc(file, final_contract_tag)
#final_locs = []

file_tag = test_case_name #datetime.datetime.now().isoformat()

#%%
skipped
#import imp
#util = imp.reload(util)
#%%

finished           = list(map(lambda m : m[0], completed))
times              = dict(completed)
mloc_table         = dict(mloc)
cfg_table          = dict(cfg)
initial_locs_table = dict(initial_locs)
final_locs_table = dict(final_locs)


# write summary data 


data = {
    'method'   : methods,
    'loc'      : list(map(lambda m : -1 if not m in mloc_table else mloc_table[m], methods)),
    'cfg_depth': list(map(lambda m : -1 if not m in cfg_table else cfg_table[m], methods)),
    'inferred' : list(map(lambda m : m in finished and m not in skipped and m not in refused and not m in timeouts, methods)),
    'skipped'  : list(map(lambda m : m in skipped, methods)),
    'refused'  : list(map(lambda m : m in refused, methods)), 
    'time'     : list(map(lambda m : -1 if not m in times else times[m], methods)),
    'error'    : list(map(lambda m : not m in timeouts and m not in finished, methods)),
    'timeout'  : list(map(lambda m : m in timeouts, methods)),
    'initial_contract_loc' : list(map(lambda m : -1 if not m in initial_locs_table else initial_locs_table[m]
    , methods)),
    'final_contract_loc' : list(map(lambda m : -1 if not m in final_locs_table else final_locs_table[m]
    , methods))
}

df = pd.DataFrame(data, columns=["method", "loc", "cfg_depth", "inferred", "skipped", "refused", "time", "error", "timeout", "initial_contract_loc", "final_contract_loc"])

print(df)

df.to_csv('strongarm-summary-{0}.csv'.format(file_tag), sep=',')


# write pipeline data 


# do for each step of the pipeline 

step_columns = ["method"]

methods_in_pipeline = list(filter(lambda m : m not in skipped and m not in refused and m in finished, methods))

data = {
    'method'   : methods_in_pipeline,
}


for step in pipeline_steps:
    print("Processing Pipeline Step: {0}".format(step))
    step_name = step.replace("AFTER ", "").replace(" ", "_")

    ms, locs, ts = util.extract_method_name_and_loc_and_timing(file, step)
    locs_map = dict(locs)
    ts_map   = dict(ts) 
    data[step_name + "_LOC"] = list(map(lambda m : -1 if not m in ms else locs_map[m], methods_in_pipeline))
    data[step_name + "_TS"]  = list(map(lambda m : -1 if not m in ms else ts_map[m], methods_in_pipeline))

    step_columns.append(step_name + "_LOC")
    step_columns.append(step_name + "_TS")


df = pd.DataFrame(data, columns=step_columns)

print(df)

df.to_csv('strongarm-pipeline-steps-{0}.csv'.format(file_tag), sep=',')

