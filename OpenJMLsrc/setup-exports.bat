@echo off
:: Sets OPENJML_EXPORTS with --add-exports flags needed for programmatic use of OpenJML.
:: Usage: call "%INSTALL%\setup-exports.bat"

set "OPENJML_EXPORTS=--add-modules jdk.compiler,java.base"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/com.sun.tools.javac.main=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/com.sun.tools.javac.comp=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/com.sun.tools.javac.util=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/com.sun.tools.javac.code=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/com.sun.tools.javac.api=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/com.sun.tools.javac.parser=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/com.sun.tools.javac.tree=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/org.jmlspecs.openjml=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/org.jmlspecs.openjml.ext=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/org.jmlspecs.openjml.proverinterface=ALL-UNNAMED"
set "OPENJML_EXPORTS=%OPENJML_EXPORTS% --add-exports=jdk.compiler/org.jmlspecs.openjml.visitors=ALL-UNNAMED"
