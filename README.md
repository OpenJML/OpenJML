# OpenJML
This is the primary repository for the OpenJML project. The active issues list for OpenJML development is [here](https://github.com/OpenJML/OpenJML/issues)
and the [wiki](https://github.com/OpenJML/OpenJML/wiki) contains information relevant to development. 
Public documentation for users is at the [project website](https://www.openjml.org).
In particular, there is a [tutorial](https://openjml.github.io/tutorial),
a [JML reference manual](https://www.openjml.org/documentation/JML_Reference_Manual.pdf),
an [OpenJML Reference Manual](https://openjml.github.io/documentation/OpenJMLUserGuide.pdf),
and other resources.

The OpenJML tool is currently up to date with openjdk-17-ga (as of 7 December 2021).

The website for the Java Modeling Language itself is [here](http://www.jmlspecs.org) and discussions about language features and semantics are on the issues list of the [JML Reference Manual project](https://github.com/JavaModelingLanguage/RefMan).

Releases numbered 0.16.X and following are installed simply by unzipping the downloaded release file into an empty directory of the user's choice.
The release includes the executable file ``openjml``, which implements OpenJML, the executable ``openjml-java``, which is a build of Java 17 that incorporates the OpenJML runtime library and can be used to run programs compiled with `openjml` to include runtime assertion checks.

On Mac OS, you may need to execute the ``mac-setup`` script so that the Mac security system allows the OpenJML libraries to be executed.
The 0.16.X series of releases do not need a particular version (or any version) of Java installed.

This material is partially based upon work supported by the National Science Foundation under Grant No. ACI-1314674.
Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the National Science Foundation.
