#%%
import numpy as np
import os
import subprocess
import sys 
import pandas as pd

# path to openjml 

#openjml = "/Users/jls/Applications/openjml-0.8.9-20170315/openjml.jar"

#file = "strongarm-summary.csv"

#df = pd.read_csv(file) 

# get all the methods
#methods = list(map(lambda m : m[0:(m.index('('))], df["method"]))


# check each spec.

df = pd.read_csv("strongarm-pipeline-steps-data.csv")


df