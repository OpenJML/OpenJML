

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


    x = inferred_df['loc']
    y = inferred_df['cfg_depth']

    plt.scatter(x,y, marker='x', c='gray', alpha=.75)
    plt.title("{0}".format(eval_name))
    plt.xlabel('Lines of Code (LOC)')
    plt.ylabel('CFG Complexity (Nodes)')
    plt.xlim([0,200])

    plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black')


    fig = plt.gcf()
    fig.set_size_inches(3.5, 2.5)


    plt.savefig(figures_path + "/cfg-depth-vs-loc-{0}.png".format(eval_name), bbox_inches='tight')
    plt.savefig(figures_path + "/cfg-depth-vs-loc-{0}.pdf".format(eval_name), bbox_inches='tight')
    plt.savefig(figures_path + "/cfg-depth-vs-loc-{0}.eps".format(eval_name), bbox_inches='tight')

    plt.clf()
    #plt.show()


    fig = plt.gcf()
    fig.set_size_inches(6.4, 4.8)