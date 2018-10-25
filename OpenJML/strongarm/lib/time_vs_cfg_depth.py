import matplotlib.pyplot as plt
import matplotlib as mpl
import numpy as np
import pandas as pd 
import os
import subprocess
import sys 
from scipy.stats import linregress

def graph(summary, steps, eval_name, figures_path):

    df = pd.read_csv(summary)

    # extract all the cases where we inferred something 
    inferred_df = df[(df['inferred']==True) & (df['cfg_depth'] > 0) & (df['initial_contract_loc'] > -1) & (df['final_contract_loc'] > -1) ]


    x = inferred_df['cfg_depth']
    y = inferred_df['time']

    plt.scatter(x,y, marker='x', c='gray', alpha=.75)
    plt.title("Inference Time vs CFG Complexity")
    plt.xlabel('Control Flow Graph Complexity (Nodes)')
    plt.ylabel('Time (ms)')
    plt.yscale('log')
    plt.xscale('log')


    slope, intercept, r_value, p_value, std_err = linregress(np.log10(x), np.log10(y))
    plt.plot(x, x*slope+intercept, c='black', lw=.5, ls="dashed", aa=True)

    p = np.polyfit(x, np.log(y), 1)

    fig = plt.gcf()
    fig.set_size_inches(3.5, 3.0)


    plt.savefig(figures_path + '/time-vs-cfg-depth.png', bbox_inches='tight')
    plt.savefig(figures_path + '/time-vs-cfg-depth.pdf', bbox_inches='tight')
    plt.savefig(figures_path + '/time-vs-cfg-depth.eps', bbox_inches='tight')

    plt.clf()
    #plt.show()

    fig.set_size_inches(6.4, 4.8)
