import numpy as np
import os
import subprocess
import sys 
import pandas as pd
import re


def extract_method_name_and_loc_and_timing(file, tag):
    the_tag = tag + " "
    #BEGIN CONTRACT CLEANUP of demo.strongarm.A.cmp(int,int) (24 LOC)
    try:
        out = subprocess.check_output("cat {0} | grep '{1}'".format(file, the_tag), shell=True).decode('utf-8').splitlines()

        methods = []
        locs    = []
        ts      = []
        for line in out:
            parts = line.replace(the_tag, "")
            parts = re.findall(r"(.*) \((\d+) LOC\) \((\d+) ms\)", parts)[0]
            method = parts[0]
            loc    = int(parts[1])
            timing = int(parts[2])

            methods.append(method)
            locs.append((method,loc))
            ts.append((method,timing))

        return (methods, locs, ts)
    except subprocess.CalledProcessError:
        return ([],[],[])

def extract_method_name_and_loc(file, tag):
    the_tag = tag + " "
    #BEGIN CONTRACT CLEANUP of demo.strongarm.A.cmp(int,int) (24 LOC)
    out = subprocess.check_output("cat {0} | grep '{1}'".format(file, the_tag), shell=True).decode('utf-8').splitlines()

    methods = []
    locs    = []
    for line in out:
        parts = line.replace(the_tag, "")
        parts = re.findall(r"(.*) \((\d+) LOC\)", parts)[0]
        method = parts[0]
        loc    = int(parts[1])

        methods.append(method)
        locs.append((method,loc))
    return (methods, locs)


def extract_method_name_and_ts(file, tag):
    the_tag = tag + " "
    #BEGIN CONTRACT CLEANUP of demo.strongarm.A.cmp(int,int) (24 LOC)
    out = subprocess.check_output("cat {0} | grep '{1}'".format(file, the_tag), shell=True).decode('utf-8').splitlines()

    methods = []
    tss    = []
    for line in out:
        parts = line.replace(the_tag, "")
        parts = re.findall(r"(.*) \((\d+) ms\)", parts)[0]
        method = parts[0]
        ts    = int(parts[1])

        methods.append(method)
        tss.append((method,ts))
    return (methods, tss)


def extract_method_name_and_metric(file, tag):

    the_tag = tag + " "

    out = subprocess.check_output("cat {0} | grep '{1}'".format(file, the_tag), shell=True).decode('utf-8').splitlines()

    data = []

    for line in out:
        print(line)
        method = line.replace(the_tag, "")

        matches = re.findall(r"(.*) \((\d+)\)", method)[0]

        method_name = matches[0]
        metric      = int(matches[1])

        data.append((method_name, metric))
    return data


def extract_method_name(file, tag):
        
    the_tag = tag + " "
    
    data = []
    try:
        out = subprocess.check_output("cat {0} | grep -F '{1}'".format(file, the_tag), shell=True).decode('utf-8').splitlines()

        
        for line in out:
            method = line.replace(the_tag, "")            
            matches = re.findall(r"(.*\)).*", method)
            method_name = matches[0]
            data.append(method_name)
            
    except subprocess.CalledProcessError:
        data = []

    return data


def extract_method_name_skipped(file, tag):
        
    the_tag = tag + " "
    
    data = []
    try:
        out = subprocess.check_output("cat {0} | grep -F '{1}'".format(file, the_tag), shell=True).decode('utf-8').splitlines()

        
        for line in out:
            method = line.replace(the_tag, "")            
            matches = re.findall(r"(.*\)).*\(SKIPPING\)", method)
            method_name = matches[0]
            data.append(method_name)
            
    except subprocess.CalledProcessError:
        data = []

    return data
