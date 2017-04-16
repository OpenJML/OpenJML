#%% 

import numpy as np
import pandas as pd 
import os
import subprocess
import sys 
#%%

eval_name = "JSON-Java" #sys.argv[1]
run_id = "2pac-20170411" #sys.argv[2]

#eval_name = sys.argv[1]
#run_id = sys.argv[2]

#eval_name = "JUnit4" #sys.argv[1]

#eval_name = "JSON-Java" #sys.argv[1]
figures_path = "strongarm/runs/{0}/figures/{1}".format(run_id, eval_name)
data_dir     = "strongarm/runs/{0}/".format(run_id)

summary = "{0}strongarm-summary-{1}.csv".format(data_dir, eval_name)

df = pd.read_csv(summary)

#%%

