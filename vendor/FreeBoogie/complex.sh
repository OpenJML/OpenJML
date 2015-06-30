for f in `find src -name \*.java`; do echo $f; cyclomatic < $f | awk '{if ($1 > 20) print $0}'; done

