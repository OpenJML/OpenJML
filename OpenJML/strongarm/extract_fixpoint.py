#%%

import numpy as np
import os
import subprocess
import sys 
import pandas as pd
import datetime

import re
import utils as util

EVAL_NAME = sys.argv[1]
RUN=sys.argv[2]

base_dir = "runs/{0}/".format(RUN)

# we can use the summary files to decide which file is the authority
dss = []
pss = []
for filename in os.listdir(base_dir):
    if filename.endswith(".csv") and "strongarm-summary" in filename and EVAL_NAME in filename: 
        file = os.path.join(base_dir, filename)
        print("Loading file: {0}".format(file))
        dss.append(pd.read_csv(file))
        continue

    if filename.endswith(".csv") and "strongarm-pipeline-steps" in filename and EVAL_NAME in filename: 
        file = os.path.join(base_dir, filename)
        print("Loading file: {0}".format(file))
        pss.append(pd.read_csv(file))
        continue


# ok, we have loaded all the ds's. get a list of all the methods.
# and initialize their authority file to 0
methods   = list(dss[0]["method"])
authority = dict(map(lambda m : (m,0), dss[0]["method"]))


#%%

# step 2 - for each method, identify the authority file.

# the logic for this is as follows. either a) it's the N-1
# computation that is flagged as "skipped"  (meaning there is nothing to infer)
# or b) it's the largest LOC. 

def extract_authority(method):
    
    max_loc = -1
    max_idx = 0
    for i in range(0,len(dss)):
        
        ds = dss[i][dss[i]["method"]==method]
        
        authority_idx = 0

        if ds["skipped"].iloc[0]==True:

            if i==0:
                authority_idx = 0
            else:
                authority_idx = i-1 

            return ("EXPLICIT", authority_idx)
        
        # otherwise, we have to do it the hard way
        if ds["final_contract_loc"].iloc[0] > max_loc:
            max_loc = ds["final_contract_loc"].iloc[0]
            max_idx = i 
        else:
            continue 
    
    return ("MAX", max_idx)

for method in methods:
    print("Extracting authority for {0}".format(method))
    kind, auth = extract_authority(method)
    print("{0}===>{1}".format(kind, auth))
    authority[method] = auth 


#%%

# step 3, create final version of the pipeline and summary files 
# by stitching them together. 

# this is how we stich.
base = dss[0] 

for method in methods:
    auth = authority[method]
    if auth == 0:
        continue
    dd = dss[auth]

    base.loc[base["method"]==method] = dd[dd["method"]==method]

# write this out
summary = "{0}/strongarm-summary-{1}.csv".format(base_dir, EVAL_NAME)

base.to_csv(summary, sep=',')

print("Writing summary to: {0}".format(summary))
# do the pipeline.

#%%
pbase = pss[0] 

for method in methods:
    auth = authority[method]
    if auth == 0:
        continue
    dd = pss[auth]

    pbase.loc[pbase["method"]==method] = dd[dd["method"]==method]


pipeline = "{0}/strongarm-pipeline-steps-{1}.csv".format(base_dir, EVAL_NAME)

pbase.to_csv(pipeline, sep=',')

print("Writing pipeline steps to: {0}".format(pipeline))
