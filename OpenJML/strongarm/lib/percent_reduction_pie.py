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

    ndf = df[(df['inferred']==True) & (df['cfg_depth'] > 0) & (df['initial_contract_loc'] > -1) & (df['final_contract_loc'] > -1) ]


    reductions = 100 - (ndf["final_contract_loc"] / ndf["initial_contract_loc"] )*100

    # as a pie chart

    labels = '0-20%', '20-40%', '40-60%', '60-80%', "80-100%"

    def filter_between(low, high):
        return list(filter(lambda x : x >= low and x < high, reductions))

    fb = filter_between

    values = np.array([fb(0,20), fb(20,40), fb(40,60), fb(60,80), fb(80,100)])

    buckets = list(map(lambda x : len(x), values))

    sizes = buckets
    #sizes = [15, 30, 45, 10]

    cls = list(map(lambda x : plt.cm.Greys(x), range(50,200,10)))
    cls = list(map(lambda x : plt.cm.Greys(x), range(50,200,50)))


    gs_colors = [
        (96/255.0,99/255.0,106/255.0),
        (165/255.0, 172/255.0, 175/255.0),
        (65/255.0,68/255.0,81/255.0),
        (143/255.0,135/255.0,130/255.0),
        (207/255.0,207/255.0,207/255.0)

    ]

    cls = gs_colors

    fig1, ax1 = plt.subplots()
    patches, texts, autotexts = ax1.pie(sizes, pctdistance=.7,  autopct='%1.1f%%',startangle=90, colors=cls)
    ax1.axis('equal')  # Equal aspect ratio ensures that pie is drawn as a circle.#
    


    plt.title("{0}".format(eval_name))

    ttl = ax1.title
    
    fig = plt.gcf()
    fig.set_size_inches(2.5, 2.5)


    plt.savefig(figures_path + "/percent-reduction-pie-{0}.png".format(eval_name))
    plt.savefig(figures_path + "/percent-reduction-pie-{0}.pdf".format(eval_name))
    plt.savefig(figures_path + "/percent-reduction-pie-{0}.eps".format(eval_name))


    plt.clf()

    colors = gs_colors 
    fig = plt.figure(figsize=(2.5, 2.5))
    patches = [
        mpl.patches.Patch(color=color, label=label)
        for label, color in zip(labels, colors)]

    fig.legend(patches, labels, loc='center', frameon=False)

    plt.savefig(figures_path + "/percent-reduction-pie-legend.eps")

    #plt.show()
    plt.clf()


    fig.set_size_inches(6.4, 4.8)

