# This script is used to run OpenJMLGUITests.
# Before running the script make sure that the environment variable "JAVA_HOME" is set and ant executable is in the PATH. 
# Set the RUNNER_PATH and AUT_PATH to run the RCPTT tests. 

import os
import shutil
import subprocess

# Set RCPTT Test Runner Path (if not available download Test Runner from https://www.eclipse.org/rcptt/download/)
RUNNER_PATH = "C:/rcptt.runner-2.1.0/eclipse"

# Set location of Eclipse used for testing the plugins
AUT_PATH="C:/eclipse"

def run_plugin_tests():

    if not os.path.isdir(RUNNER_PATH):
        raise Exception ("The RCPTT Test Runner directory %s was expected to be available but is not." % (RUNNER_PATH))
    
    if not os.path.isdir(AUT_PATH):
        raise Exception ("The Eclipse directory %s to run RCPTT tests was expected to be available but is not." % (AUT_PATH))
    
    #setup the AUT workspace
    for f in os.listdir(os.path.join(AUT_PATH, "dropins")):
        if f.startswith("org.jmlspecs.") :
            os.remove(os.path.join(AUT_PATH, "dropins", f))
            
    # create latest plugin jars
    # Note that we are assuming here that JAVA_HOME env variable in set and ant is in the PATH
    cmd = [ "ant", "-buildfile","../OpenJMLFeature/Create_Update_Site.xml", "-Declipse.home=" +AUT_PATH, "create_dirs"  ]
    exitcode = execute_process(cmd)
    print exitcode
        
    for file in os.listdir("../OpenJMLFeature/plugins"):
        shutil.copyfile(os.path.join("../OpenJMLFeature/plugins", file), os.path.join(AUT_PATH, "dropins", file))
        
    cmd = ["ant", "-Drunner-path="+RUNNER_PATH, "-Daut-path="+AUT_PATH]
    execute_process(cmd)
    
    #clean up 
    shutil.rmtree("../OpenJMLFeature/buildDirectory")
    shutil.rmtree("../OpenJMLFeature/plugins")
    shutil.rmtree("../OpenJMLFeature/features")
        
def execute_process(cmd): 
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, shell = False)
    while(True):
        line = p.stdout.readline()
        if(len(line) == 0):
            break
        print (line.decode("utf-8"))
    print p.returncode
    return p.returncode

if __name__ == "__main__":
    run_plugin_tests()
