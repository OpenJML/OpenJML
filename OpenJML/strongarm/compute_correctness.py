#%%
import matplotlib.pyplot as plt
import matplotlib as mpl
import numpy as np
import pandas as pd 
import os
import glob 
import subprocess
import sys 

#%%

run_id="2pac-2017-04-17"
pcts = []
counts = []

for file in glob.glob('verify.*.' + run_id + '.csv'):
    print("FILE: " + file)
    csv = pd.read_csv(file) 

    total = len(csv)
    correct = len(csv[csv["ok\\n"]==True])
    pct = float(correct)/float(total)

    print("{0} cases, {1} verified ({2}%)".format(total, correct,pct*100))

    pcts.append(pct)
    counts.append(total)

avg_correct = np.mean(pcts) 
print("Overall Correctness: {0}%".format(avg_correct * 100))
print("Total Cases: {0}".format(np.sum(counts)))
