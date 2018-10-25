
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



    gs_colors = [
        (96/255.0,99/255.0,106/255.0),
        (165/255.0, 172/255.0, 175/255.0),
        (65/255.0,68/255.0,81/255.0),
        (143/255.0,135/255.0,130/255.0),
        (207/255.0,207/255.0,207/255.0)

    ]

    for i in [['Error', 'Inferred', 'Skipped', 'Refused', 'Timeout']]: #: 
        labels = list(i) 
        
        def fb(xx):
            return len(df[df[xx]==True])


        #values = np.array([fb('inferred'), fb('timeout'), fb('refused'), fb('error'), fb('skipped')]) 

        values = np.array([fb(i[0].lower()), fb(i[1].lower()), fb(i[2].lower()), fb(i[3].lower()), fb(i[4].lower())]) 

        the_sum = np.sum(values)
        zipped = zip(values, gs_colors) 

        
        zipped = list(filter(lambda x : 100.0*(float(x[0])/the_sum) >= .1, zipped))

        
        vz = list(zip(*zipped))
        
        sizes = vz[0]
        
        fig1, ax1 = plt.subplots()
        patches, texts, autotexts = ax1.pie(sizes, autopct='  %1.1f%%  ',startangle=90, colors=vz[1], pctdistance=1.1, labeldistance=1)


        ax1.axis('equal')  # Equal aspect ratio ensures that pie is drawn as a circle.#
        plt.title("{0}".format(eval_name))

        fig = plt.gcf()
        fig.set_size_inches(2.5, 2.5)
        
        plt.savefig(figures_path + "/inference-breakdown-pie-{0}.png".format(eval_name))
        plt.savefig(figures_path + "/inference-breakdown-pie-{0}.pdf".format(eval_name))
        plt.savefig(figures_path + "/inference-breakdown-pie-{0}.eps".format(eval_name))


        #plt.show()
        plt.clf()

        colors = gs_colors 
        fig = plt.figure(figsize=(2.5, 2.5))
        patches = [
            mpl.patches.Patch(color=color, label=label)
            for label, color in zip(labels, colors)]

        fig.legend(patches, labels, loc='center', frameon=False)

        plt.savefig(figures_path + "/inference-breakdown-pie-legend.eps")

        #plt.show()
        plt.clf()




        fig.set_size_inches(6.4, 4.8)
