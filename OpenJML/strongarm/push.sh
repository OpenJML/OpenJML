#!/usr/local/bin/bash

rsync -avz --exclude 'run.out*' --exclude 'OpenJML/.metadata' --exclude 'OpenJML/OpenJML/OpenJML/strongarm/figures/' --exclude 'OpenJML/OpenJML/OpenJML/strongarm/runs/' --exclude 'OpenJML/OpenJML/OpenJML/benchmarks/' --exclude='.git/' --exclude='.metadata/' --exclude 'OpenJML/OpenJML/OpenJMLTest/benchmarks/' --exclude='.gitignore' /Users/jls/Projects/Strongarm/ jls@biggie:/Users/jls/Projects/Strongarm 


rsync -avz --exclude='.git/' --exclude='.metadata' --exclude='.gitignore' /Users/jls/Projects/Analysis/ jls@biggie:/Users/jls/Projects/Analysis 

#rsync -avz --exclude 'run.out*' --exclude 'OpenJML/.metadata' --exclude 'OpenJML/OpenJML/OpenJML/strongarm/figures/' --exclude 'OpenJML/OpenJML/OpenJML/strongarm/runs/' --exclude 'OpenJML/OpenJML/OpenJML/benchmarks/' --exclude='.git/' --exclude='.metadata/' --exclude 'OpenJML/OpenJML/OpenJMLTest/benchmarks/' --exclude='.gitignore' /Users/jls/Projects/Strongarm/ jls@crunch:/Users/jls/Projects/Strongarm --delete


#rsync -avz --exclude='.git/' --exclude='.metadata' --exclude='.gitignore' /Users/jls/Projects/Analysis/ jls@crunch:/Users/jls/Projects/Analysis --delete



# rsync -avz --exclude 'run.out*' --exclude 'OpenJML/.metadata' --exclude 'OpenJML/OpenJML/OpenJML/strongarm/figures/' --exclude 'OpenJML/OpenJML/OpenJML/benchmarks/' --exclude='.git/' --exclude='.metadata/' --exclude 'OpenJML/OpenJML/OpenJMLTest/benchmarks/' --exclude='.gitignore' /Users/jls/Projects/Strongarm/ jls@crunch:/home/jls/Projects/Strongarm --delete


# rsync -avz --exclude='.git/' --exclude='.metadata' --exclude='.gitignore' /Users/jls/Projects/Analysis/ jls@crunch:/home/jls/Projects/Analysis --delete
