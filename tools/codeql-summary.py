#!/usr/bin/env python3
# Summarizes a CodeQL SARIF file (from tools/codeql-local): prints each security finding, then the number of
# findings per query for each severity; writes every finding, grouped by query, to the given text file.
# Usage: codeql-summary.py results.sarif results.txt
import collections
import json
import re
import sys

sarif, txt = sys.argv[1], sys.argv[2]
run = json.load(open(sarif))["runs"][0]
rules = run["tool"]["driver"]["rules"]

def message(result):
    # first line, with SARIF's [text](n) links reduced to text
    return re.sub(r"\[([^]]*)\]\(\d+\)", r"\1", result["message"]["text"].splitlines()[0])

def location(result):
    loc = result["locations"][0]["physicalLocation"]
    return "%s:%d" % (loc["artifactLocation"]["uri"], loc.get("region", {}).get("startLine", 0))

groups = collections.defaultdict(list)
for r in run["results"]:
    groups[r["rule"]["index"]].append(r)

def kind(index):
    props = rules[index].get("properties", {})
    if "security" in props.get("tags", []):
        return "security"
    return props.get("problem.severity", "recommendation")

kinds = ["security", "error", "warning", "recommendation"]
by_kind = {k: sorted((i for i in groups if kind(i) == k), key=lambda i: -len(groups[i])) for k in kinds}

with open(txt, "w") as f:
    for k in kinds:
        for i in by_kind[k]:
            rule = rules[i]
            f.write("%s [%s] %s\n" % (rule["id"], k, rule["shortDescription"]["text"]))
            for r in sorted(groups[i], key=location):
                f.write("    %s  %s\n" % (location(r), message(r)))
            f.write("\n")

total = sum(len(g) for g in groups.values())
print("CodeQL: %d findings" % total)
for k in kinds:
    n = sum(len(groups[i]) for i in by_kind[k])
    print("\n%s: %d" % (k.capitalize(), n))
    for i in by_kind[k]:
        rule = rules[i]
        if k == "security":
            for r in groups[i]:
                print("  %s  %s\n      %s" % (location(r), rule["id"], message(r)))
        else:
            print("  %5d  %-45s %s" % (len(groups[i]), rule["id"], rule["shortDescription"]["text"]))
print("\nEvery finding, by query: %s" % txt)
