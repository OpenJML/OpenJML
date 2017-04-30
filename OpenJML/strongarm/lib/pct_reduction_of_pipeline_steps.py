#%%

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

    
    inferred_df = summary_df[(summary_df['inferred']==True) & (summary_df['cfg_depth'] > 0) & (summary_df['initial_contract_loc'] > -1) & (summary_df['final_contract_loc'] > -1) ]

    pdf = inferred_df.join(pipeline_df.set_index('method'), on='method', lsuffix="_inferred", rsuffix="_pipeline")


    loc_columns    = pdf.filter(regex=('.*_LOC$'))
    timing_columns = pdf.filter(regex=('.*_TS$'))

    
    ## compute the % change of LOC for each pipeline step
    # step 1 is to get the STARTING LOC count for each method.

    
    data = {
        'method' : pdf["method"]
    }

    
    all_cols = []
    for col in list(loc_columns):
        data[col] = []
        data[col + "_overall"] = []

        all_cols.append(col)
        all_cols.append(col + "_overall")

    for method in pdf["method"]:
        row = pdf[pdf["method"] == method]

        last_loc    = row["initial_contract_loc"].iloc[0]
        initial_loc = row["initial_contract_loc"].iloc[0]

        for col in list(loc_columns):
            if last_loc==0 or row[col].iloc[0] == -1 :
                data[col].append(np.nan)
                data[col + "_overall"].append(np.nan)
            else:
                # percent change from previous step
                tmp_loc = last_loc
                #print("Row={0}, last_loc={1}".format(row[col], last_loc))
                pct_change = (row[col].iloc[0] - last_loc) / last_loc
                last_loc = row[col].iloc[0]
                data[col].append(pct_change*100.0)

                # percent change from initial loc
                pct_change = (row[col].iloc[0] - tmp_loc) / initial_loc

                data[col + "_overall"].append(pct_change*100)
    
    df = pd.DataFrame(data, columns=["method"] + all_cols)
    # next, we have to, feach column, calcualte an average and standard deviation. 

    data_between = {
        'analysis' : list(loc_columns),
        'mean'     : [],
        'std'      : [],
        'max'      : [],
        'min'      : [],

    }

    data_overall = {
        'analysis' : list(loc_columns),
        'mean'     : [],
        'std'      : [],
        'max'      : [],
        'min'      : [],

    }


    for col in list(loc_columns):

        df_between = df[df[col] != np.nan]
        data_between['mean'].append(np.mean(df_between[col]))
        data_between['std'].append(np.std(df_between[col]))
        data_between['min'].append(np.min(df_between[col]))
        data_between['max'].append(np.max(df_between[col]))

        df_overall = df[df[col + "_overall"] != np.nan]
        data_overall['mean'].append(np.mean(df_overall[col+ "_overall"]))
        data_overall['std' ].append(np.std(df_overall[col + "_overall"]))
        data_overall['min' ].append(np.min(df_overall[col + "_overall"]))
        data_overall['max' ].append(np.max(df_overall[col + "_overall"]))

    df_between = pd.DataFrame(data_between, columns=['analysis', 'mean', 'std', 'max', 'min'])

    df_overall = pd.DataFrame(data_overall, columns=['analysis', 'mean', 'std', 'max', 'min'])    

    #%%

    # PLOT! FINALLY!

    width = 0.4

    keeps = [2, 3, 4, 5, 6, 7,9, 11, 12, 13, 15, 16, 17, 18, 19, 20]
    labels = ["LEX", "RT", "RC", "RUC", "RDA", "PRE", "RNV", "PBP", "TIV",  "RDA", "RC",  "RPA", "RUP", "RUC", "DMP", "FAR"]

    ind = np.arange(len(keeps))

    # keeps
    between_series = np.take(list(df_between["mean"]), keeps)[::-1]
    between_sd     = np.take(list(df_between["std"]), keeps)[::-1]
    overall_series = np.take(list(df_overall["mean"]), keeps)[::-1]
    overall_sd     = np.take(list(df_overall["std"]), keeps)[::-1]

    #%%

    fig, ax = plt.subplots()
    ax.barh(ind, between_series, width, color='gray', label='Mean Reduction Between Steps', edgecolor="k", lw=.5, xerr=between_sd, error_kw=dict(ecolor='silver', alpha=.5, capsize=3, capthick=1))
    ax.barh(ind + width, overall_series, width, color='silver', edgecolor="k", lw=.5, label='Mean Reduction Overall', hatch="///", error_kw=dict(ecolor='gray', alpha=.5, capsize=3, capthick=1), xerr=overall_sd )

    ax.set(yticks=ind + width, yticklabels=labels[::-1], xlim=[-75,23]) 
    plt.legend(bbox_to_anchor=(.5, -.3), loc='center', ncol=1)

    plt.title("Change in Specification LOC vs Pipeline Step")
    plt.xlabel("Percent Reduction (LOC)")
    plt.ylabel("Pipeline Step")

    fig = plt.gcf()
    fig.set_size_inches(3.5, 3.0)

    plt.savefig(figures_path + '/pct-reduction-of-pipeline-steps.png', bbox_inches='tight')
    plt.savefig(figures_path + '/pct-reduction-of-pipeline-steps.pdf', bbox_inches='tight')
    plt.savefig(figures_path + '/pct-reduction-of-pipeline-steps.eps', bbox_inches='tight')


    plt.clf()

    fig.set_size_inches(6.4, 4.8)
