#%% 

import numpy as np
import pandas as pd 
import os
import subprocess
import sys 
import math
#%%

#eval_name = "JSON-Java" #sys.argv[1]
#run_id = "2pac-20170411" #sys.argv[2]

eval_name = sys.argv[1]
run_id = sys.argv[2]

#eval_name = "JUnit4" #sys.argv[1]

#eval_name = "JSON-Java" #sys.argv[1]
figures_path = "runs/{0}/figures/{1}".format(run_id, eval_name)
data_dir     = "runs/{0}/".format(run_id)

summary = "{0}strongarm-summary-{1}.csv".format(data_dir, eval_name)

#%% 
d = pd.read_csv(summary)
df = d[d["inferred"]==True]
#%%
# load the data frame; randomly sample 30% of methods. 
num_methods = len(df)
sample_rows = np.random.choice(num_methods, math.floor(num_methods * .30), replace=False)
 
#%%
for i in sample_rows:
    if "<" in df["method"].iloc[i]:
        continue
    chop = df["method"].iloc[i].find('(')
    print(df["method"].iloc[i][0:chop])