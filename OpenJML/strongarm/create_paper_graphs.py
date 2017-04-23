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
data_dir     = "runs/{0}/".format(run_id)


for eval_name in evals:
    print("Processing: " + eval_name)

    figures_path = "runs/{0}/figures/{1}".format(run_id, eval_name)

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


#%%

#
# a combined hbar graph of inference breakdowns. 
#
labels = np.array(evals)

inferred = []
error    = []
timeout  = []
refused  = []
skipped  = []

for eval_name in evals:

    summary = "{0}strongarm-summary-{1}.csv".format(data_dir, eval_name)



    df = pd.read_csv(summary)


    def fb(xx):
        return len(df[df[xx]==True])

    i = fb("inferred")
    e = fb("error")
    t = fb("timeout")
    r = fb("refused")
    s = fb("skipped")

    the_sum = i + e + t + r + s
    
    inferred.append(round((float(i)/float(the_sum))*100))
    error.append(   round((float(e)/float(the_sum))*100))
    timeout.append( round((float(t)/float(the_sum))*100)) 
    refused.append( round((float(r)/float(the_sum))*100)) 
    skipped.append( round((float(s)/float(the_sum))*100)) 

skipped = [30,20]
error   = [10,50]

ind = np.arange(len(labels))  # the x locations for the groups
width = 0.15       # the width of the bars

fig, ax = plt.subplots()
rects1 = ax.barh(ind - width, inferred, width, color="green")
rects2 = ax.barh(ind, timeout, width, color="yellow")
rects3 = ax.barh(ind - (2*width), error, width, color="red")
rects4 = ax.barh(ind + width, refused, width, color=(96/255.0,99/255.0,106/255.0), hatch="//")
rects5 = ax.barh(ind + (2*width), skipped, width, color=(165/255.0, 172/255.0, 175/255.0))

ax.set_xlabel("Percent of Methods")
ax.set_title('Inference Outcomes')
ax.set_yticks(ind + width / 5)
ax.set_yticklabels(tuple(labels))

ax.legend((rects1[0], rects2[0], rects3[0], rects4[0], rects5[0]), ("Inferred", "Timeout", "Error", "Refused", "Skipped"))
plt.show()


figures_path = "runs/{0}/figures/".format(run_id)

plt.savefig(figures_path + "/outcomes-barh.eps")
plt.savefig(figures_path + "/outcomes-barh.png")
plt.savefig(figures_path + "/outcomes-barh.pdf")

