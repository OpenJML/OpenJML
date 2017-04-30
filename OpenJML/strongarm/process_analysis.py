#%% 

import matplotlib.pyplot as plt
import matplotlib as mpl
import numpy as np
import pandas as pd 
import os
import subprocess
import sys 
from scipy.stats import linregress

#%%

#eval_name = "JSON-Java" #sys.argv[1]
#run_id = "2pac-2017-04-17" #sys.argv[2]

eval_name = sys.argv[1]
run_id = sys.argv[2]

#eval_name = "JUnit4" #sys.argv[1]

#eval_name = "JSON-Java" #sys.argv[1]
figures_path = "runs/{0}/figures/{1}".format(run_id, eval_name)
data_dir     = "runs/{0}/".format(run_id)

#figures_path = "strongarm/runs/{0}/figures/{1}".format(run_id, eval_name)
#data_dir     = "strongarm/runs/{0}/".format(run_id)


def get_summary(d):
    return (np.min(d), np.max(d), np.mean(d), np.std(d))

#print(">>>>{0}".format(plt.rcParams['figure.figsize']))

plt.rcParams['figure.figsize'] = (15, 10)

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
plt.title("Inference Time vs CFG Complexity")
plt.xlabel('Control Flow Graph Complexity (Nodes)')
plt.ylabel('Time (ms)')
plt.yscale('log')
plt.xscale('log')


slope, intercept, r_value, p_value, std_err = linregress(np.log10(x), np.log10(y))
plt.plot(x, x*slope+intercept, c='black', lw=.5, ls="dashed", aa=True)

#plt.ylim([0,3000])

#10^(Slope*X + Yintercept)

p = np.polyfit(x, np.log(y), 1)
#plt.semilogx(x, p[0] * np.log(y) + p[1], 'r-')

#plt.plot(x, np.log(np.poly1d(np.polyfit(x, np.log(y), 1))(x)), c='black', lw=.5, ls="dashed", aa=True)

#plt.plot(x, p(x))
#plt.plot(x, np.poly1d(np.polyfit(x, y, 1))(x), c='black', lw=.5, ls="dashed", aa=True)


fig = plt.gcf()
fig.set_size_inches(3.5, 3.0)


plt.savefig(figures_path + '/time-vs-cfg-depth.png', bbox_inches='tight')
plt.savefig(figures_path + '/time-vs-cfg-depth.pdf', bbox_inches='tight')
plt.savefig(figures_path + '/time-vs-cfg-depth.eps', bbox_inches='tight')

plt.clf()
#plt.show()

fig.set_size_inches(6.4, 4.8)


#%%

#%% 
ndf = df[(df['loc'] > 0) & (df['cfg_depth'] > 0)]
x = ndf['loc']
y = ndf['cfg_depth']

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
#%%
print(figures_path)
#%% 

pipeline = "{0}strongarm-pipeline-steps-{1}.csv".format(data_dir, eval_name)

pdf = pd.read_csv(pipeline)

#pdf = pdf[pdf["method"] != "org.json.JSONTokener.syntaxError(java.lang.String)"]
# filter org.json.JSONTokener.syntaxError(java.lang.String)

row_count = pdf.count()["method"]
pdf
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
    if pdfm.empty:
        return -1
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

data_methods = []
#list(inferred_df["method"])
data = {
    'method' : []
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

    if row.empty:
        continue 
    data_methods.append(method)
    #print("Found Row: {0}".format(row))
    # this is what we started with
    #print(method)
    #print(inferred_df[inferred_df["method"]==method])
    last_loc = inferred_df[inferred_df["method"]==method]["initial_contract_loc"].iloc[0]
    initial_loc = inferred_df[inferred_df["method"]==method]["initial_contract_loc"].iloc[0]
    
    #sprint(last_loc)
    for col in cols:
        #print("METHOD: {0} ROW: {1}".format(method, row[col]))
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

data["method"] = data_methods

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
labels = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I','J', 'K', 'L', 'M', 'C', 'O', 'P', 'D', 'R', 'S']
width = 0.4

keeps = [2, 3, 4, 5, 6, 7,9, 11, 12, 13, 15, 16, 17, 18, 19, 20]
labels = ["LEX", "RT", "RC", "RUC", "RDA", "PRE", "RNV", "PBP", "TIV",  "RDA", "RC",  "RPA", "RUP", "RUC", "DMP", "FAR"]

ind = np.arange(len(keeps))

#between_series = df_between["mean"][::-1][:-2]
#between_sd     = df_between["std"][::-1][:-2]
#overall_series = df_overall["mean"][::-1][:-2]
#overall_sd     = df_overall["std"][::-1][:-2]

# keeps


between_series = np.take(list(df_between["mean"]), keeps)[::-1]
between_sd     = np.take(list(df_between["std"]), keeps)[::-1]
overall_series = np.take(list(df_overall["mean"]), keeps)[::-1]
overall_sd     = np.take(list(df_overall["std"]), keeps)[::-1]

#labels = labels[2:]
between_series
#%%

fig, ax = plt.subplots()
ax.barh(ind, between_series, width, color='gray', label='Mean Reduction Between Steps', edgecolor="k", lw=.5, xerr=between_sd, error_kw=dict(ecolor='silver', alpha=.5, capsize=3, capthick=1))
ax.barh(ind + width, overall_series, width, color='silver', edgecolor="k", lw=.5, label='Mean Reduction Overall', hatch="///", error_kw=dict(ecolor='gray', alpha=.5, capsize=3, capthick=1), xerr=overall_sd )

ax.set(yticks=ind + width, yticklabels=labels[::-1], xlim=[-75,23]) # ylim=[2*width - 1, len(df_overall)])
#ax.legend(loc='top right')
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

#plt.show()
#%%

#ndf = inferred_df[(inferred_df["final_contract_loc"] > 0) & (inferred_df["final_contract_loc"] < 100)]


ndf = inferred_df[(inferred_df["final_contract_loc"] > 0) & (inferred_df["initial_contract_loc"] < 10000000000000)]

ndf

#%% 
ndf["difference"] = ndf["initial_contract_loc"] - ndf["final_contract_loc"]


#ndf = ndf.sort(['initial_contract_loc', 'final_contract_loc'], ascending=[1, 1])

ndf = ndf.sort(['difference'], ascending=[1])

initial_spec_lengths = list(ndf["initial_contract_loc"])
final_spec_lengths = list(ndf["final_contract_loc"])
indexes            = np.arange(len(final_spec_lengths))

#initial_spec_lengths[-1]
#final_spec_lengths[-1] 
#%% 

width=.5

p1 = plt.bar(indexes, initial_spec_lengths, width, color='#d62728')
p2 = plt.bar(indexes, final_spec_lengths, width,
              )

plt.ylabel('Specification Length (LOC)')
plt.xlabel('Specifications')
plt.title("Initial and Final Specification Size (LOC)\n{0}".format(eval_name))
#plt.legend((p2[0], p1[0]), ( 'Initial Specification', 'Final Specification'))
#plt.yscale('log')



plt.savefig(figures_path + '/stick-graph.png')
plt.savefig(figures_path + '/stick-graph.pdf')
plt.savefig(figures_path + '/stick-graph.eps')

plt.clf()
#plt.show()

#%%

ndf["difference"] = ndf["initial_contract_loc"] - ndf["final_contract_loc"]


#ndf = ndf.sort(['initial_contract_loc', 'final_contract_loc'], ascending=[1, 1])

ndf = ndf.sort(['difference'], ascending=[1])

initial_spec_lengths = np.array(ndf["initial_contract_loc"])
final_spec_lengths = np.array(ndf["final_contract_loc"])
indexes            = np.arange(len(final_spec_lengths))

ndf
#%%
bins = np.arange(0,np.max(ndf["initial_contract_loc"]), 1)
binplace = np.digitize(ndf["initial_contract_loc"], bins)

initial_bars = np.zeros(len(bins)) 
istd_bars    = np.zeros(len(bins))

final_bars   = np.zeros(len(bins)) 
fstd_bars    = np.zeros(len(bins))

count_bars    = np.zeros(len(bins))

bins
#%%

#bins
#np.where(binplace==100)
for bin in range(1, len(bins)):
    #print("BIN: {0}".format(bin))
    #print(initial_spec_lengths[np.where(binplace==bin)])

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


#%%

# norm the width 

limit = np.max(count_bars)
max_width = 100

width = (count_bars/limit)*max_width
width = .8
#%%
indexes            = np.arange(len(initial_bars))

p1 = plt.bar(indexes, initial_bars, width, color='#d62728')
p2 = plt.bar(indexes, final_bars, width,
              )

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
#plt.show()

#%%


bins = np.linspace(1, np.max(ndf["initial_contract_loc"]), 100)

bins
#%%

n = 50
x = np.random.rand(n)
y = np.random.rand(n)
z = np.random.rand(n)
cm = plt.cm.get_cmap('jet')
 
fig, ax = plt.subplots()
sc = ax.scatter(initial_bars,final_bars,s=count_bars*50,linewidth=0,alpha=0.5, cmap=cm, c=count_bars)

#sc = ax.scatter(initial_bars,final_bars,s=count_bars*500,cmap=cm,linewidth=0,alpha=0.5)
plt.title("Final Specification Length vs Initial Specification Length\n{0}".format(eval_name))
plt.xlabel("Initial Specification Length (LOC)")
plt.ylabel("Final Specification Length (LOC)")
plt.axhline(y=80, color='r', linestyle='--')
plt.text(165000, 95, "One Full Page of Text", fontsize=11)
ax.grid()
fig.colorbar(sc)

plt.savefig(figures_path + '/final-loc-bubble.png')
plt.savefig(figures_path + '/final-loc-bubble.pdf')
plt.savefig(figures_path + '/final-loc-bubble.eps')
 

plt.clf()
#plt.show()

#%%

final_bars


#%%

# Code length (LOC) vs Final Specification Length. 

x = ndf['loc']
y = ndf['final_contract_loc']

plt.scatter(x,y, marker='x', c='gray', alpha=.75)
plt.title("Final Specification Length (LOC) vs Method Length (LOC)\n{0}".format(eval_name))
plt.ylabel('Final Contract Length (LOC)')
plt.xlabel('Method Length (LOC)')
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

print("test")


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
#texts[0].set_fontsize(1)

for patch, txt in zip(patches, autotexts):
    # the angle at which the text is located
    ang = (patch.theta2 + patch.theta1) / 2.
    # new coordinates of the text, 0.7 is the distance from the center 
    x = patch.r * 0.7 * np.cos(ang*np.pi/180)
    y = patch.r * 0.7 * np.sin(ang*np.pi/180)
    # if patch is narrow enough, move text to new coordinates
    if (patch.theta2 - patch.theta1) < 10.:
        txt.set_position((x, y))




plt.title("{0}".format(eval_name))

ttl = ax1.title
#ttl.set_position([.5, 1.05])

fig = plt.gcf()
fig.set_size_inches(2.5, 2.5)


plt.savefig(figures_path + "/percent-reduction-pie-{0}.png".format(eval_name))
plt.savefig(figures_path + "/percent-reduction-pie-{0}.pdf".format(eval_name))
plt.savefig(figures_path + "/percent-reduction-pie-{0}.eps".format(eval_name))


plt.clf()
#plt.show() 

#%%

colors = gs_colors # ["red", "blue", "green", "purple", "orange"]
fig = plt.figure(figsize=(2.5, 2.5))
patches = [
    mpl.patches.Patch(color=color, label=label)
    for label, color in zip(labels, colors)]

fig.legend(patches, labels, loc='center', frameon=False)

plt.savefig(figures_path + "/percent-reduction-pie-legend.eps".format(eval_name))

#plt.show()
plt.clf()

#%%
fig.set_size_inches(6.4, 4.8)




#%%
list(map(lambda x : x, range(10,100,10)))


#%%

# breakdown of method results 

summary = "{0}strongarm-summary-{1}.csv".format(data_dir, eval_name)

df = pd.read_csv(summary)
#%%
# categories 

#['Error', 'Inferred', 'Skipped', 'Refused', 'Timeout']
#['Error', 'Timeout', 'Refused', 'Skipped', 'Inferred']

gs_colors = [
    (96/255.0,99/255.0,106/255.0),
    (165/255.0, 172/255.0, 175/255.0),
    (65/255.0,68/255.0,81/255.0),
    (143/255.0,135/255.0,130/255.0),
    (207/255.0,207/255.0,207/255.0)

]

for i in [['Error', 'Inferred', 'Skipped', 'Refused', 'Timeout']]: #: itertools.permutations(['Inferred', 'Timeout', 'Refused', 'Error', 'Skipped']):

    labels = list(i) #'Inferred', 'Timeout', 'Refused', 'Error', 'Skipped'

    print(labels)

    def fb(xx):
        return len(df[df[xx]==True])


    #values = np.array([fb('inferred'), fb('timeout'), fb('refused'), fb('error'), fb('skipped')]) 

    values = np.array([fb(i[0].lower()), fb(i[1].lower()), fb(i[2].lower()), fb(i[3].lower()), fb(i[4].lower())]) 

    the_sum = np.sum(values)
    zipped = zip(values, gs_colors) 

    
    zipped = list(filter(lambda x : 100.0*(float(x[0])/the_sum) >= .1, zipped))

    print(zipped)
    
    vz = list(zip(*zipped))
    
    sizes = vz[0]
    
    fig1, ax1 = plt.subplots()
    patches, texts, autotexts = ax1.pie(sizes, autopct='  %1.1f%%  ',startangle=90, colors=vz[1], pctdistance=1.1, labeldistance=1)

    #autotexts[0].set_position((-.5,1))


    if eval_name=="Commons-Email":
        autotexts[4].set_position((-10,1))

    if eval_name=="JSON-Java":
        autotexts[2].set_position((.5,-.1))


    if eval_name=="JUnit4":
        autotexts[0].set_position((-.3,.8))
        #autotexts[2].set_position((.5,.8))
        #autotexts[3].set_position((.5,.8))
        #autotexts[4].set_position((.5,.8))

        
    #texts[0].set_fontsize(100)
    # texts[1].set_fontsize(8)
    # texts[2].set_fontsize(8)
    # texts[3].set_fontsize(8)
    # texts[4].set_fontsize(8)

    #patches[0].set_hatch('//') 
    #patches[1].set_hatch('+') 
    #patches[2].set_hatch('o') 

    ax1.axis('equal')  # Equal aspect ratio ensures that pie is drawn as a circle.#
    plt.title("{0}".format(eval_name))

    fig = plt.gcf()
    fig.set_size_inches(2.5, 2.5)

    
    plt.savefig(figures_path + "/inference-breakdown-pie-{0}.png".format(eval_name))
    plt.savefig(figures_path + "/inference-breakdown-pie-{0}.pdf".format(eval_name))
    plt.savefig(figures_path + "/inference-breakdown-pie-{0}.eps".format(eval_name))



    #plt.show()
    plt.clf()

    
#%%
colors = gs_colors # ["red", "blue", "green", "purple", "orange"]
fig = plt.figure(figsize=(2.5, 2.5))
patches = [
    mpl.patches.Patch(color=color, label=label)
    for label, color in zip(labels, colors)]

fig.legend(patches, labels, loc='center', frameon=False)

plt.savefig(figures_path + "/inference-breakdown-pie-legend.eps".format(eval_name))

#plt.show()
plt.clf()
#%%
fig.set_size_inches(6.4, 4.8)
