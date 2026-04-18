# lsp-duplicate — Candidate tests for removal

This directory holds test classes that were moved out of `lsp/test/` during a
coverage and redundancy analysis (April 2026).  They are **not compiled or run**
by the test suite; they are kept here for review before a final deletion decision.

## Why these tests were moved

### DefinitionFinderTest.java

Tests go-to-definition for symbols declared and referenced in plain `.java` files.
`DefinitionFinderJmlTest` (still in `lsp/test/`) covers all the same `.java`-only
scenarios and additionally exercises `.jml` companion files.  JaCoCo instruction
analysis confirmed zero unique instructions attributable to `DefinitionFinderTest`
when the rest of the suite is present.

### ReferenceFinderTest.java

Tests find-all-references for symbols in plain `.java` files.  The same reasoning
applies as for `DefinitionFinderTest`: `ReferenceFinderJmlTest` covers all
`.java`-only vectors and also tests `.jml` companion file scenarios.  JaCoCo
confirmed zero unique instructions.

### RenameTest1Maybe.java

Contains two rename tests (`testRenameJavaField`, `testRenameGhostField`) that
were extracted from `RenameTest1.java`.  These tests call `Renamer.rename()`
directly through `RenameTestBase.renameAt()` and do not add behavioral coverage
beyond what `RenameTest1.java` already provides for the same code paths.  JaCoCo
confirmed zero unique instructions when the rest of the rename suite is present.

## What to do with these files

- **Delete** if the corresponding Jml-variant test class gives you confidence
  that the scenarios are fully covered.
- **Restore** to `lsp/test/` (and re-add to `Makefile` and `AllLspTests`) if
  review reveals a scenario that is not covered elsewhere.

The rename and JML-variant test classes that subsume these are:

| Moved file              | Subsumed by                        |
|-------------------------|------------------------------------|
| DefinitionFinderTest    | DefinitionFinderJmlTest            |
| ReferenceFinderTest     | ReferenceFinderJmlTest             |
| RenameTest1Maybe        | RenameTest1, RenameMethodAndClassTest |
