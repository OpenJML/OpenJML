#%% 

import matplotlib.pyplot as plt
import matplotlib as mpl
import numpy as np
import pandas as pd 



def get_summary(d):
    return (np.min(d), np.max(d), np.mean(d), np.std(d))


#plt.rcParams['figure.figsize'] = (15, 10)

summary = "strongarm-summary-data.csv"

df = pd.read_csv(summary)

# extract all the cases where we inferred something 

inferred_df = df[(df['inferred']==True) & (df['cfg_depth'] > 0) ]

(tmin, tmax, tmean, tstd) = get_summary(inferred_df["time"])

print("Min: {0}\nMax: {1}\nMean: {2}\nSTD: {3}".format(tmin, tmax, tmean, tstd))


#%% 

## plot of loc

plt.scatter(inferred_df['loc'],inferred_df['time'], marker='x', c='black')
#plt.title(r"""\Huge{Big title !} \newline \tiny{Small subtitle !}""")
plt.title("Inference Time vs Lines of Code\n(JSON-Java)")
#plt.subtitle("test")
plt.xlabel('Lines of Code (LOC)')
plt.ylabel('Time (ms)')
plt.ylim([0,3000])

plt.savefig('figures/time-vs-loc.png')
plt.savefig('figures/time-vs-loc.pdf')
plt.savefig('figures/time-vs-loc.eps')

plt.show()


#%% 

x = inferred_df['cfg_depth']
y = inferred_df['time']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("Inference Time vs CFG Complexity\n(JSON-Java)")
plt.xlabel('Control Flow Graph Complexity (Nodes)')
plt.ylabel('Time (ms)')


#plt.ylim([0,3000])

plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black', lw=.5, ls="dashed", aa=True)
plt.savefig('figures/time-vs-cfg-depth.png')
plt.savefig('figures/time-vs-cfg-depth.pdf')
plt.savefig('figures/time-vs-cfg-depth.eps')

plt.show()


#%% 
ndf = df[(df['loc'] > 0) & (df['cfg_depth'] > 0)]
x = ndf['loc']
y = ndf['cfg_depth']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("CFG Complexity vs LOC\n(JSON-Java)")
plt.xlabel('Lines of Code (LOC)')
plt.ylabel('CFG Complexity (Nodes)')
#plt.ylim([0,3000])

plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black')
plt.savefig('figures/cfg-depth-vs-loc.png')
plt.savefig('figures/cfg-depth-vs-loc.pdf')
plt.savefig('figures/cfg-depth-vs-loc.eps')

plt.show()

#%% 

pipeline = "strongarm-pipeline-steps-data.csv"

pdf = pd.read_csv(pipeline)

pdf = pdf[pdf["method"] != "org.json.JSONTokener.syntaxError(java.lang.String)"]
# filter org.json.JSONTokener.syntaxError(java.lang.String)

row_count = pdf.count()["method"]

#%%

loc_columns    = pdf.filter(regex=('.*_LOC$'))

timing_columns = pdf.filter(regex=('.*_TS$'))



#%%
# first, a graph of how often various pipeline steps were deployed
# histogram, x axis should be the steps, y axis is number of times deployed.
# 
# # frequency should be normed to 1

columns = list(loc_columns)[::-1] # reverse it

objects = list(map(lambda c : c.replace("_LOC", "").replace("_", " "), columns)) 
y_pos = np.arange(len(objects))
pct_used = list(map(lambda c : loc_columns[c][loc_columns[c] > -1].count()/row_count
, columns))
 
plt.barh(y_pos, pct_used, align='center', alpha=0.5, color='grey')
plt.yticks(y_pos, objects)
plt.ylabel("Pipeline Step")
plt.xlabel('% Methods Used')
plt.title('Simplification Utilization by Pipeline Step')



plt.savefig('figures/pipeline-step-utilization.pdf')
plt.savefig('figures/pipeline-step-utilization.png')
plt.savefig('figures/pipeline-step-utilization.eps')

#%%

## compute the % change of LOC for each pipeline step

# step 1 is to get the STARTING LOC count for each method.
def starting_loc(method):
    cols = list(loc_columns)

    pdfm = pdf[pdf["method"]==method]

    for c in cols:
        if pdfm[c].iloc[0] > -1:
            return pdfm[c].iloc[0]

    return -1

method_locs = []
for m in pdf["method"]:
    mm = starting_loc(m)            
    method_locs.append(mm)

pdf['method_loc'] = method_locs

#%% 
# v2 - v1 / v1
#loc_columns    = pdf.filter(regex=('.*_LOC$'))

applied_steps = pdf[pdf['method_loc'] > 0]
applied_steps[["method", "REMOVING_CONTRADICTIONS_OF_LOC", "PRUNING_USELESS_CLAUSES_OF_LOC", "PRUNING_USELESS_CLAUSES_II_OF_LOC", "REMOVING_DEAD_ASSIGNMENTS_OF_LOC", "PERFORMING_OPTIMIZED_PREMAP_BLOCK_SUBSTITUTIONS_LOC"]]
#list(applied_steps)
#%%

applied_steps["REMOVING_DUPLICATE_PRECONDITIONS_(VIA_SMT)_LOC"] - applied_steps["REMOVING_IMPOSSIBLE_SPECIFICATION_CASES_(VIA_SMT)_LOC"]


data = {
    'method' : list(applied_steps["method"])
}

cols = list(loc_columns)
methods = data["method"]
all_cols = []
for col in cols:
    data[col] = []
    data[col + "_overall"] = []

    all_cols.append(col)
    all_cols.append(col + "_overall")

for method in methods:# ["org.json.JSONTokener.dehexchar(char)"]: #methods:
    row = applied_steps[applied_steps["method"] == method]

    # this is what we started with
    last_loc = inferred_df[inferred_df["method"]==method]["initial_contract_loc"].iloc[0]
    initial_loc = inferred_df[inferred_df["method"]==method]["initial_contract_loc"].iloc[0]
    
    #sprint(last_loc)
    for col in cols:
        if row[col].iloc[0] == -1:
            data[col].append(np.nan)
            data[col + "_overall"].append(np.nan)
        else:
            # percent change from previous step
            tmp_loc = last_loc
            pct_change = (row[col].iloc[0] - last_loc) / last_loc
            last_loc = row[col].iloc[0]
            data[col].append(pct_change*100.0)

            # percent change from initial loc
            pct_change = (row[col].iloc[0] - tmp_loc) / initial_loc

            data[col + "_overall"].append(pct_change*100)




df = pd.DataFrame(data, columns=["method"] + all_cols)
df


#%%

# next, we have to, feach column, calcualte an average and standard deviation. 

data_between = {
    'analysis' : cols,
    'mean'     : [],
    'std'      : [],
    'max'      : [],
    'min'      : [],

}

data_overall = {
    'analysis' : cols,
    'mean'     : [],
    'std'      : [],
    'max'      : [],
    'min'      : [],

}


for col in cols:

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

df["REMOVING_DEAD_ASSIGNMENTS_OF_LOC"]
#data_between
#df[df["CLEANING_PRESTATE_ASSIGNABLES_LOC"] != np.nan]["CLEANING_PRESTATE_ASSIGNABLES_LOC"]
#df
#%%

applied_steps#["REMOVING_DEAD_ASSIGNMENTS_OF_LOC"]
#%% 

df_between

#%%

df_overall

#%%

# PLOT! FINALLY!

labels = list(map(lambda x : x.replace("_LOC", "").replace("_", " "), cols))
ind = np.arange(len(df_overall))
width = 0.4

fig, ax = plt.subplots()
ax.barh(ind, df_between["mean"][::-1], width, color='gray', label='Mean Reduction Between Steps', edgecolor="k", lw=.5, xerr=df_between["std"][::-1], error_kw=dict(ecolor='silver', alpha=.5, capsize=3, capthick=1))
ax.barh(ind + width, df_overall["mean"][::-1], width, color='silver', edgecolor="k", lw=.5, label='Mean Reduction Overall', hatch="///", error_kw=dict(ecolor='gray', alpha=.5, capsize=3, capthick=1), xerr=df_overall["std"][::-1] )

ax.set(yticks=ind + width, yticklabels=labels[::-1], xlim=[-75,23]) # ylim=[2*width - 1, len(df_overall)])
ax.legend()
plt.title("Change in Specification LOC vs Pipeline Step\n(JSON-Java)")
plt.xlabel("Percent Reduction (LOC)")
plt.ylabel("Pipeline Step")


plt.savefig('figures/pct-reduction-of-pipeline-steps.png')
plt.savefig('figures/pct-reduction-of-pipeline-steps.pdf')
plt.savefig('figures/pct-reduction-of-pipeline-steps.eps')


plt.show()

#%%

ndf = inferred_df[inferred_df["initial_contract_loc"] > -1]

ndf


#%%

# Code length (LOC) vs Final Specification Length. 

y = ndf['loc']
x = ndf['final_contract_loc']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("Method Length (LOC) vs Final Specification Length (LOC)\n(JSON-Java)")
plt.xlabel('Final Contract Length (LOC)')
plt.ylabel('Method Length (LOC)')
#plt.ylim([0,3000])

plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black')
plt.savefig('figures/code-loc-vs-final-contract-loc.png')
plt.savefig('figures/code-loc-vs-final-contract-loc.pdf')
plt.savefig('figures/code-loc-vs-final-contract-loc.eps')

plt.show()


# Same but for CFG


y = ndf['cfg_depth']
x = ndf['final_contract_loc']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("CFG Size (Nodes) vs Final Specification Length (LOC)\n(JSON-Java)")
plt.xlabel('Final Contract Length (LOC)')
plt.ylabel('CFG Size (Nodes)')
#plt.ylim([0,3000])

plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black')
plt.savefig('figures/code-cfg-size-vs-final-contract-loc.png')
plt.savefig('figures/code-cfg-size-vs-final-contract-loc.pdf')
plt.savefig('figures/code-cfg-size-vs-final-contract-loc.eps')

plt.show()


#%% Initial Inferred spec vs Final Size (How good is our reduction?)


y = ndf['initial_contract_loc']
x = ndf['final_contract_loc']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("Initial Contract Length (LOC) vs Final Specification Length (LOC)\n(JSON-Java)")
plt.xlabel('Final Contract Length (LOC)')
plt.ylabel('Initial Contract Length (LOC)')
#plt.yscale('log')
plt.ylim([0,3000])

z = np.polyfit(x, y, 1)
p = np.poly1d(z)
plt.plot(x,p(x), c="black")

#plt.yscale('log')

plt.savefig('figures/initial-contract-size-vs-final-contract-loc.png')
plt.savefig('figures/initial-contract-size-vs-final-contract-loc.pdf')
plt.savefig('figures/initial-contract-size-vs-final-contract-loc.eps')

plt.show()

#%%

# Percent reduction of our stuff. 
# v2 - v1 / v1

reductions = ((ndf["final_contract_loc"] - ndf["initial_contract_loc"]) / ndf["initial_contract_loc"])*100

#%%

# the histogram of the data
n, bins, patches = plt.hist(reductions, 20, normed=1, facecolor='silver', alpha=0.75, hatch="//", edgecolor="black")

plt.xlabel('Percent Reduction of Inferred Specification to Final Specification')
plt.ylabel('Frequency')
plt.title("Relative Frequency of Specification Reduction\n(JSON-Java)")
#plt.axis([40, 160, 0, 0.03])
#plt.grid(True)

# add a 'best fit' line
#l = plt.plot(bins, y, 'r--', linewidth=1)


plt.savefig('figures/percent-reduction-histogram.png')
plt.savefig('figures/percent-reduction-histogram.pdf')
plt.savefig('figures/percent-reduction-histogram.eps')


plt.show()

