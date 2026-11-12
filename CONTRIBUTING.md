# Contributing to OpenJML

## Questions, bugs and feature requests

- Questions and general discussion: [GitHub Discussions](https://github.com/OpenJML/OpenJML/discussions).
- Bugs and feature requests: [GitHub Issues](https://github.com/OpenJML/OpenJML/issues). For a bug, include
  the output of `openjml --version`, the command line, and the smallest Java/JML input that shows the problem.
- Security vulnerabilities: see [SECURITY.md](SECURITY.md); do not open a public issue.

## Code and specification changes

Changes are made by pull request.

- Branch from the development branch (`dev-` followed by the Java version, e.g. `dev-21`) and target your
  pull request at it. The `master-` branch holds releases.
- OpenJML is built together with sibling repositories (`Specs`, `JMLAnnotations`, `Solvers`, ...) cloned under
  a common parent directory. A change that also needs a library-specification change uses a same-named branch
  in `Specs`.
- Building and running tests are described in the [wiki](https://github.com/OpenJML/OpenJML/wiki).
  In short: in `OpenJMLsrc`, `bash configure` once, then `make openjml`; in `OpenJMLTest/unittests`,
  `./runtests <suite>` runs one test suite and `./runpar` runs them all.

## Requirements for a pull request

- **Tests.** Every bug fix comes with a regression test that fails without the fix; every new feature
  comes with tests of it. The full test suite passes.
- **An issue.** Reference the issue the change addresses in the commit message or pull request.
- **Style.** Follow the surrounding code. New code uses 4-space indentation and no tabs
  (`openjml-format.xml` is an Eclipse formatter profile for this).
- **Changes to OpenJDK code.** Keep edits to the OpenJDK sources minimal and mark each with a
  `// OPENJML` comment, so upstream merges can find them.
- **Licensing.** Contributions are accepted under the project's license (see [LICENSE](LICENSE)).
