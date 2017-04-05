#%% 

import matplotlib.pyplot as plt
import matplotlib as mpl
import numpy as np
import pandas as pd 
import os
import subprocess
import sys 

eval_name = sys.argv[1]
run_id = sys.argv[2]

#eval_name = "JUnit4" #sys.argv[1]

#eval_name = "JSON-Java" #sys.argv[1]
figures_path = "runs/{0}/figures/{1}".format(run_id, eval_name)
data_dir     = "runs/{0}/".format(run_id)

def get_summary(d):
    return (np.min(d), np.max(d), np.mean(d), np.std(d))


#plt.rcParams['figure.figsize'] = (15, 10)

summary = "{0}strongarm-summary-{1}.csv".format(data_dir, eval_name)

df = pd.read_csv(summary)

# extract all the cases where we inferred something 

inferred_df = df[(df['inferred']==True) & (df['cfg_depth'] > 0) & (df['initial_contract_loc'] > -1) & (df['final_contract_loc'] > -1) ]

(tmin, tmax, tmean, tstd) = get_summary(inferred_df["time"])

print("Min: {0}\nMax: {1}\nMean: {2}\nSTD: {3}".format(tmin, tmax, tmean, tstd))

#%%
inferred_df

#%% 

## plot of loc

plt.scatter(inferred_df['loc'],inferred_df['time'], marker='x', c='black')
#plt.title(r"""\Huge{Big title !} \newline \tiny{Small subtitle !}""")
plt.title("Inference Time vs Lines of Code\n{0}".format(eval_name))
#plt.subtitle("test")
plt.xlabel('Lines of Code (LOC)')
plt.ylabel('Time (ms)')
plt.ylim([0,3000])

plt.savefig(figures_path + '/time-vs-loc.png')
plt.savefig(figures_path + '/time-vs-loc.pdf')
plt.savefig(figures_path + '/time-vs-loc.eps')

plt.clf()
#plt.show()

#%% 

x = inferred_df['cfg_depth']
y = inferred_df['time']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("Inference Time vs CFG Complexity\n{0}".format(eval_name))
plt.xlabel('Control Flow Graph Complexity (Nodes)')
plt.ylabel('Time (ms)')


#plt.ylim([0,3000])

plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black', lw=.5, ls="dashed", aa=True)
plt.savefig(figures_path + '/time-vs-cfg-depth.png')
plt.savefig(figures_path + '/time-vs-cfg-depth.pdf')
plt.savefig(figures_path + '/time-vs-cfg-depth.eps')

plt.clf()
#plt.show()

#%% 
ndf = df[(df['loc'] > 0) & (df['cfg_depth'] > 0)]
x = ndf['loc']
y = ndf['cfg_depth']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("CFG Complexity vs LOC\n{0}".format(eval_name))
plt.xlabel('Lines of Code (LOC)')
plt.ylabel('CFG Complexity (Nodes)')
#plt.ylim([0,3000])

plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black')
plt.savefig(figures_path + '/cfg-depth-vs-loc.png')
plt.savefig(figures_path + '/cfg-depth-vs-loc.pdf')
plt.savefig(figures_path + '/cfg-depth-vs-loc.eps')

plt.clf()
#plt.show()
#%% 

pipeline = "{0}strongarm-pipeline-steps-{1}.csv".format(data_dir, eval_name)

pdf = pd.read_csv(pipeline)

#pdf = pdf[pdf["method"] != "org.json.JSONTokener.syntaxError(java.lang.String)"]
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



plt.savefig(figures_path + '/pipeline-step-utilization.pdf')
plt.savefig(figures_path + '/pipeline-step-utilization.png')
plt.savefig(figures_path + '/pipeline-step-utilization.eps')

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

pdf["method_loc"]

#%% 

applied_steps = pdf[pdf['method_loc'] > 0]

applied_steps
#%%


#%%



data = {
    'method' : list(inferred_df["method"])
}

cols = list(loc_columns)
methods = inferred_df["method"] #data["method"]
all_cols = []
for col in cols:
    data[col] = []
    data[col + "_overall"] = []

    all_cols.append(col)
    all_cols.append(col + "_overall")

for method in methods:# ["org.json.JSONTokener.dehexchar(char)"]: #methods:
    row = applied_steps[applied_steps["method"] == method]

    # this is what we started with
    #print(method)
    #print(inferred_df[inferred_df["method"]==method])
    last_loc = inferred_df[inferred_df["method"]==method]["initial_contract_loc"].iloc[0]
    initial_loc = inferred_df[inferred_df["method"]==method]["initial_contract_loc"].iloc[0]
    
    #sprint(last_loc)
    for col in cols:
        #print("ROW: {0}".format(row[col]))
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



#for c in all_cols:
#    print("Col={0}, length={1}".format(c, len(data[c])))

#print("Col={0}, length={1}".format("method", len(data["method"])))

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
plt.title("Change in Specification LOC vs Pipeline Step\n{0}".format(eval_name))
plt.xlabel("Percent Reduction (LOC)")
plt.ylabel("Pipeline Step")


plt.savefig(figures_path + '/pct-reduction-of-pipeline-steps.png')
plt.savefig(figures_path + '/pct-reduction-of-pipeline-steps.pdf')
plt.savefig(figures_path + '/pct-reduction-of-pipeline-steps.eps')


plt.clf()
#plt.show()
#%%

ndf = inferred_df[inferred_df["initial_contract_loc"] > -1]

ndf


#%%

# Code length (LOC) vs Final Specification Length. 

y = ndf['loc']
x = ndf['final_contract_loc']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("Method Length (LOC) vs Final Specification Length (LOC)\n{0}".format(eval_name))
plt.xlabel('Final Contract Length (LOC)')
plt.ylabel('Method Length (LOC)')
#plt.ylim([0,3000])

plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black')
plt.savefig(figures_path + '/code-loc-vs-final-contract-loc.png')
plt.savefig(figures_path + '/code-loc-vs-final-contract-loc.pdf')
plt.savefig(figures_path + '/code-loc-vs-final-contract-loc.eps')

plt.clf()
#plt.show()

# Same but for CFG


x = ndf['cfg_depth']
y = ndf['final_contract_loc']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("Final Specification Length (LOC) vs CFG Size (Nodes)\n{0}".format(eval_name))
plt.ylabel('Final Contract Length (LOC)')
plt.xlabel('CFG Size (Nodes)')
#plt.ylim([0,3000])

plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black')
plt.savefig(figures_path + '/code-cfg-size-vs-final-contract-loc.png')
plt.savefig(figures_path + '/code-cfg-size-vs-final-contract-loc.pdf')
plt.savefig(figures_path + '/code-cfg-size-vs-final-contract-loc.eps')

plt.clf()
#plt.show()

#%% Initial Inferred spec vs Final Size (How good is our reduction?)


x = ndf['initial_contract_loc']
y = ndf['final_contract_loc']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("Final Specification Length (LOC) vs Initial Contract Length (LOC)\n{0}".format(eval_name))
plt.ylabel('Final Contract Length (LOC)')
plt.xlabel('Initial Contract Length (LOC)')
#plt.yscale('log')
plt.ylim([0,3000])

z = np.polyfit(x, y, 1)
p = np.poly1d(z)
plt.plot(x,p(x), c="black")

#plt.yscale('log')

plt.savefig(figures_path + '/initial-contract-size-vs-final-contract-loc.png')
plt.savefig(figures_path + '/initial-contract-size-vs-final-contract-loc.pdf')
plt.savefig(figures_path + '/initial-contract-size-vs-final-contract-loc.eps')

plt.clf()
#plt.show()

#%%

# Percent reduction of our stuff. 
# v2 - v1 / v1

reductions = ((ndf["final_contract_loc"] - ndf["initial_contract_loc"]) / ndf["initial_contract_loc"])*100

#%%

# the histogram of the data
n, bins, patches = plt.hist(reductions, 20, normed=1, facecolor='silver', alpha=0.75, hatch="//", edgecolor="black")

plt.xlabel('Percent Reduction of Inferred Specification to Final Specification')
plt.ylabel('Frequency')
plt.title("Relative Frequency of Specification Reduction\n{0}".format(eval_name))
#plt.axis([40, 160, 0, 0.03])
#plt.grid(True)

# add a 'best fit' line
#l = plt.plot(bins, y, 'r--', linewidth=1)


plt.savefig(figures_path + '/percent-reduction-histogram.png')
plt.savefig(figures_path + '/percent-reduction-histogram.pdf')
plt.savefig(figures_path + '/percent-reduction-histogram.eps')


plt.clf()
#plt.show() 
#%% times smaller 

reductions = (ndf["final_contract_loc"] / ndf["initial_contract_loc"] )*100

#reductions = list(filter(lambda x : x > 10, reductions))

reductions
#%% 

# the histogram of the data
n, bins, patches = plt.hist(reductions, 8, normed=1, facecolor='silver', alpha=0.75, hatch="//", edgecolor="black")

plt.xlabel('Specification Size as a Percentage of Initial Specification Size')
plt.ylabel('Frequency')
plt.title("Final Specification Size as a Percentage of Initial Specification Size\n{0}".format(eval_name))
#plt.axis([40, 160, 0, 0.03])
#plt.xscale('log')
#plt.grid(True)

# add a 'best fit' line
#l = plt.plot(bins, y, 'r--', linewidth=1)

rects = patches

# Now make some labels
labels = ["label%d" % i for i in range(len(rects))]
for rect, label in zip(rects, labels):
    height = rect.get_height()
    ax = plt.gca()
    #ax.text(rect.get_x() + rect.get_width()/2, height, label, ha='center', va='bottom')

ax = plt.gca()
#ax.text(patches[0].get_x(),0.0008931602042757867, "fuck")    
#ax.text(patches[0].get_x() + patches[0].get_width() /2,patches[0].get_height(), "fuck")    

plt.savefig(figures_path + '/times-reduction-histogram.png')
plt.savefig(figures_path + '/times-reduction-histogram.pdf')
plt.savefig(figures_path + '/times-reduction-histogram.eps')


plt.clf()
#plt.show()
#%% 
#nn = ndf[["initial_contract_loc", "final_contract_loc"]]
#nn["reduction"] = reductions
#nn

#%% 

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

fig1, ax1 = plt.subplots()
ax1.pie(sizes, labels=labels, autopct='%1.1f%%',startangle=90, colors=cls)
ax1.axis('equal')  # Equal aspect ratio ensures that pie is drawn as a circle.#
plt.title("Percent Reduction of Final Contract as Percentage of Initial\n{0}".format(eval_name))


plt.savefig(figures_path + '/percent-reduction-pie.png')
plt.savefig(figures_path + '/percent-reduction-pie.pdf')
plt.savefig(figures_path + '/percent-reduction-pie.eps')


plt.clf()
#plt.show() 
#%%
list(map(lambda x : x, range(10,100,10)))


#%%

# breakdown of method results 

summary = "{0}strongarm-summary-{1}.csv".format(data_dir, eval_name)

df = pd.read_csv(summary)
#%%
# categories 

labels = 'Inferred', 'Timeout', 'Refused', 'Error', 'Skipped'

def fb(xx):
    return len(df[df[xx]==True])


values = np.array([fb('inferred'), fb('skipped'), fb('refused'), fb('error'), fb('timeout')]) 

buckets = values

sizes = buckets
#sizes = [15, 30, 45, 10]

cls = list(map(lambda x : plt.cm.Greys(x), range(50,200,50)))

fig1, ax1 = plt.subplots()
patches = ax1.pie(sizes, labels=labels, autopct='%1.1f%%',startangle=90, colors=cls)[0]

#patches[0].set_hatch('//') 
#patches[1].set_hatch('+') 
#patches[2].set_hatch('o') 

ax1.axis('equal')  # Equal aspect ratio ensures that pie is drawn as a circle.#
plt.title("Breakdown of Inference Outcomes\n{0}".format(eval_name))


plt.savefig(figures_path + '/inference-breakdown-pie.png')
plt.savefig(figures_path + '/inference-breakdown-pie.pdf')
plt.savefig(figures_path + '/inference-breakdown-pie.eps')
