import matplotlib.pyplot as plt
import matplotlib as mpl
import numpy as np
import pandas as pd 
import os
import subprocess
import sys 
from scipy.stats import linregress

def graph(summary, steps, eval_name, figures_path):

    
    summary_df = pd.read_csv(summary)
    pipeline_df = pd.read_csv(steps)

    summary_df["difference"] = summary_df["initial_contract_loc"] - summary_df["final_contract_loc"]

    
    inferred_df = summary_df[(summary_df['inferred']==True) & (summary_df['cfg_depth'] > 0) & (summary_df['initial_contract_loc'] > -1) & (summary_df['final_contract_loc'] > -1) ]


    ndf = inferred_df[(inferred_df["final_contract_loc"] > 0)]

    ndf = ndf.sort_values(['difference'], ascending=[1])

    initial_spec_lengths = np.array(ndf["initial_contract_loc"])
    final_spec_lengths = np.array(ndf["final_contract_loc"])
    indexes            = np.arange(len(final_spec_lengths))

    bins = np.arange(0,np.max(ndf["initial_contract_loc"]), 1)
    binplace = np.digitize(ndf["initial_contract_loc"], bins)

    initial_bars = np.zeros(len(bins)) 
    istd_bars    = np.zeros(len(bins))
    final_bars   = np.zeros(len(bins)) 
    fstd_bars    = np.zeros(len(bins))
    count_bars    = np.zeros(len(bins))

    for bin in range(1, len(bins)):

        if len(np.where(binplace==bin)[0])==0:
            initial_bars[bin-1] = np.nan
            istd_bars[bin-1]    = np.nan
            final_bars[bin-1]   = np.nan 
            fstd_bars[bin-1]    = np.nan
            count_bars[bin-1]   = np.nan
            
            continue 

        i = initial_spec_lengths[np.where(binplace==bin)]
        f = final_spec_lengths[np.where(binplace==bin)]

        #print(i)
        initial_bars[bin-1] = np.mean(i)
        istd_bars[bin-1]    = np.std(i)
        final_bars[bin-1]   = np.mean(f) 
        fstd_bars[bin-1]    = np.std(f)

        # how much does this sample represent?
        count_bars[bin-1]   = i.size 
            

    # remove nans
    initial_bars = initial_bars[~np.isnan(initial_bars)]
    istd_bars    = istd_bars[~np.isnan(istd_bars)]
    final_bars   = final_bars[~np.isnan(final_bars)]
    fstd_bars    = fstd_bars[~np.isnan(fstd_bars)]
    count_bars    = count_bars[~np.isnan(count_bars)]

    # norm the width 
    limit = np.max(count_bars)
    max_width = 100

    width = (count_bars/limit)*max_width
    width = .8

    indexes            = np.arange(len(initial_bars))

    p1 = plt.bar(indexes, initial_bars, width, color='#d62728')
    p2 = plt.bar(indexes, final_bars, width)

    plt.axhline(y=80, color='r', linestyle='--')
    plt.text(0, 95, "One Full Page of Text", fontsize=11)

    plt.axhline(y=20, color='r', linestyle='--')
    plt.text(0, 30, "1/4 Page of Text", fontsize=11)


    plt.ylabel('Specification Length (LOC)')
    plt.xlabel('Specifications')
    plt.title("Initial and Final Specification Size (LOC)")
    plt.legend((p1[0], p2[0]), ( 'Initial Specification', 'Final Specification'))
    plt.yscale('log')

    fig = plt.gcf()
    fig.set_size_inches(8.5, 4)

    plt.savefig(figures_path + '/stick-graph-v2.png')
    plt.savefig(figures_path + '/stick-graph-v2.pdf')
    plt.savefig(figures_path + '/stick-graph-v2.eps')

    fig = plt.gcf()
    fig.set_size_inches(6.4, 4.8)

    plt.clf()
