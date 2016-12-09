#! C:/Python35/python
# This script is used to run OpenJMLGUITests.
# Before running the script make sure that the environment variable "JAVA_HOME" is set and ant executable is in the PATH. 
# Set the RUNNER_PATH and AUT_PATH to run the RCPTT tests. 

# Set RCPTT Test Runner Path (if not available download Test Runner from https://www.eclipse.org/rcptt/download/)
RUNNER_PATH="C:/cygwin/home/dcok/apps/rcptt.runner-2.1.0/eclipse"

# Set location of Eclipse used for testing the plugins
AUT_PATH="C:/cygwin/home/dcok/apps/eclipse-neon-gui/eclipse"

import os
import shutil
import subprocess
import platform


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
    if platform.system().startswith('Linux'):
        ant_exe = "ant"
    else:
        # on Windows, python 3.5 fails to execute ant script if ant.bat file is not specified. 
        ant_exe = "ant.bat"
    ant_exe = "C:/cygwin/home/dcok/ant/apache-ant-1.9.4/bin/ant.bat"
    cmd = [ ant_exe, "-buildfile","../OpenJMLFeature/Create_Update_Site.xml", "-Declipse.home=" +AUT_PATH, "create_dirs"  ]
    exitcode = execute_process(cmd)
    if exitcode != 0 :
        raise Exception ("Cannot create OpenJML plugin files successfully.")
    
    for file in os.listdir("../OpenJMLFeature/plugins"):
        shutil.copyfile(os.path.join("../OpenJMLFeature/plugins", file), os.path.join(AUT_PATH, "dropins", file))
        
    cmd = [ant_exe, "-Drunner-path="+RUNNER_PATH, "-Daut-path="+AUT_PATH]
    execute_process(cmd)
    
    #clean up 
    shutil.rmtree("../OpenJMLFeature/buildDirectory")
    shutil.rmtree("../OpenJMLFeature/plugins")
    shutil.rmtree("../OpenJMLFeature/features")
        
def execute_process(cmd): 
    new_env = dict(os.environ)
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=new_env, shell=False)
    while(True):
        line = p.stdout.readline()
        if(len(line) == 0):
            break
        print (line.decode("utf-8"))
    p.wait()
    return p.returncode

if __name__ == "__main__":
    run_plugin_tests()
