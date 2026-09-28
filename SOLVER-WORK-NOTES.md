# Solver work: status and open decisions

Working notes for the `solver-work` branch; remove before merging. Nothing has been pushed.

## What is on this branch

`solver-work` = `dev-21` (local, ahead of `origin/dev-21`: the rows up to 8ea8dbbde1) + the rows after it + this file.

| Commit | Content |
|---|---|
| 657f5c7d76 | Explicit triggers for 7 type axioms (z3 >= 4.12 matching loops); enum axiom guarded by `instanceof` |
| c0f5e4c472 | `jSMTLIB.jar` = 0.13.0 release |
| 93a4d6c13f | Solver names passed to jSMTLIB un-normalized (right adapter for cvc5 and z3-4.3.x); 8 more explicit triggers |
| 466c2884de | cvc5: `unknown` with no counterexample becomes a warning, not an internal error; no `get-value` of expressions with bound variables; z3 options only for z3 |
| 07a9585727 | Solver-specific goldens `expected<N>.<solver>`; cvc5 golden for `bag` |
| 3c641e0a3d | cvc5 goldens where cvc5 answers `unknown` (Dzmz, enums2, escJml1, escAbstractSpecs) |
| 8ea8dbbde1 | Alternate goldens for z3-5.1.0 counterexample variants (6 tests) |
| 8cca9c6b4b | `--z3=<settings>` (mbqi, autoconf, no-mbqi, no-autoconf; both off by default); `@Options("--z3=mbqi")` on the test methods that need MBQI; alternate goldens for jmlarray, jmlseq, jmlstring |
| b3fdb6ffa8 | `pickProverExec` also finds `<prover>.jar` (smtinterpol) -- to be replaced, see below |
| c0ec9ca7c0 | `jSMTLIB.jar` from jSMTLIB `dev` (0.14.0 development build, a4d9d20a); goldens and 2 test sources use `(- N)` (136 occurrences) |

Checked with z3-5.1.0 and z3-4.3.1: the value-format tests (esc2 testNewLblSyntax/testShowStatementESC,
escArithmeticModes2 testModEqual(Long), escLemma, jmlbigint) pass with both. With z3-5.1.0: esc2/escfunction
`testMethodAxioms(2)` and `choosex` pass with the `@Options` annotations.
`escfiles` with z3-5.1.0 on `dev-21`: 90 passed, 8 failed, about 12-13 min (old build with z3-4.3.1: 76 min).

## jSMTLIB (separate repository) -- merged into `dev` (local, not pushed)

- 0.13.0 released (includes the `:pattern` fix). `dev` is 0.14.0; its jar is the one in `OpenJMLsrc/libs`.
- On `dev`: d42feb79 z3-4.3 `get-value` values structured, printing `(- N)`; 3e2477d3 cvc5 stopped after a parse error,
  and failed option queries reported accurately; 807a0964 `parseScript` end-of-input check; 4cdd9e05 merge;
  a4d9d20a script goldens (version-check for the 0.14.0 bump, zapi for the value format).
- Unchecked: the bitwuzla golden for `ok_lambdaBasicArrow` probably needs the same message update (no bitwuzla here).

## To do

- **smtinterpol**: replace the `.jar` special case (b3fdb6ffa8) in `pickProverExec` with a lookup of jSMTLIB's
  `.command` property (`org.smtlib.solver_smtinterpol-2.5.command=java,-jar,%exec%,-q`); OpenJML has to load
  jSMTLIB's properties itself (`new SMT()` does not).

## Decided

- `@Options("--z3=...")` on a class or method replaces the global `--z3` value (the usual option stack).
- `escchoose.m` and `gitbug890.model_test` (z3-5.1.0 lost proofs that MBQI does not fix) stay as failures.
- cvc5 'unknown' goldens are kept as cvc5-specific responses; cvc5 timeouts are left; z3-5.1.0 is the default.
- `--smt-batch` is parked on its own branch `batch-prelude` (16fa2a2c51); see issue #985.
- `escfilesTrace` is set aside for now.

## Decisions to make

1. **Merging.** Merge `solver-work` into `dev-21`? The jar in it is a jSMTLIB development build: wait for a release?
2. **A fallback for `unknown` results** (retry in a fresh z3 process with MBQI on and a short timeout): worth it?
   (z3 ignores `:smt.mbqi` set mid-session, and ignores time limits on `check-sat-using` with MBQI.)
3. **Internal temporaries in messages**: "Precondition conjunct is false: `_JML__tmp`18 != null`" shows internal names
   (and their numbering differs between runs and solvers). Show the source expression instead?

## Left to the user

- `gitbug963` (type-checker message changed) and `gitbug963a` (no expected file).
- A full cvc5 run of the whole suite.
- Deleting the superseded OpenJML branches `z3-triggers-enum-fix`, `solver-fixes`, `z3-mbqi`.
