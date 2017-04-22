#%% 
import matplotlib.pyplot as plt
import matplotlib as mpl
import numpy as np
import pandas as pd 
import os
import subprocess
import sys 
from scipy.stats import linregress
from lib import time_vs_cfg_depth, cfg_depth_vs_loc, pct_reduction_of_pipeline_steps, red_blue, inference_breakdown_pie, percent_reduction_pie
#%%

# build the list of evals 
evals  = ["JSON-Java", "Commons-CSV"] #sys.argv[2:]
run_id = "2pac-2017-04-17"            #sys.argv[1]


for eval_name in evals:
    print("Processing: " + eval_name)

    figures_path = "runs/{0}/figures/{1}".format(run_id, eval_name)
    data_dir     = "runs/{0}/".format(run_id)

    plt.rcParams['figure.figsize'] = (15, 10)


    summary = "{0}strongarm-summary-{1}.csv".format(data_dir, eval_name)
    pipeline = "{0}strongarm-pipeline-steps-{1}.csv".format(data_dir, eval_name)

    #%%
    # graph stuff
    time_vs_cfg_depth.graph(summary, pipeline, eval_name, figures_path)
    cfg_depth_vs_loc.graph(summary, pipeline, eval_name, figures_path)
    pct_reduction_of_pipeline_steps.graph(summary, pipeline, eval_name, figures_path)
    red_blue.graph(summary, pipeline, eval_name, figures_path)
    inference_breakdown_pie.graph(summary, pipeline, eval_name, figures_path)
    percent_reduction_pie.graph(summary, pipeline, eval_name, figures_path)



if True:
    sys.exit()

