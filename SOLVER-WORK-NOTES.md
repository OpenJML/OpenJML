# Solver work: status and open decisions

Working notes for the `solver-work` branch; remove before merging. Nothing has been pushed.

## What is on this branch

`solver-work` = `dev-21` (local, ahead of `origin/dev-21`: the rows up to 8ea8dbbde1) + the last two rows + this file.

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
| b3fdb6ffa8 | `pickProverExec` also finds `<prover>.jar` (smtinterpol) |

Checked with z3-5.1.0: esc2/escfunction `testMethodAxioms(2)` and `choosex` pass with the `@Options` annotations.
`escfiles` with z3-5.1.0 on `dev-21`: 90 passed, 8 failed, about 12-13 min (old build with z3-4.3.1: 76 min).

## `--smt-batch` (separate branch `batch-prelude`, for review)

- 16fa2a2c51 on top of 93a4d6c13f: `--smt-batch` (off by default), `SolverBatch`, `escbatch` tests (9 pass),
  and test-framework changes it needs (compile with `jSMTLIB.jar` patched in; export `org.jmlspecs.openjml.esc`, `org.smtlib`).
- It needs no jSMTLIB change, but reaches three protected jSMTLIB members by reflection:
  `AbstractSolver.translate(INode)`, `AbstractSolver.solverProcess`, `SolverProcess.process`
  (the last is replaceable by the new public `SolverProcess.stopIfRunning()`). A public jSMTLIB method such as
  `AbstractSolver.sendBatch(List<ICommand>)` would make it independent of jSMTLIB internals.

## jSMTLIB (separate repository)

- Released 0.13.0 (includes the `:pattern` fix). `dev` is now 0.14.0.
- Branch `fix/z3-4.3-get-value` (worktree `~/projects/jSMTLIB-getvalue`), not merged:
  - d42feb79 `Solver_z3_4_3.get_value` returns structured values, so z3-4.3 prints `(- 5)` like every other adapter.
  - (in progress) cvc5 stopped after a parse error; `requireOptionEnabled` reports a failed option query instead of
    "only valid if ... has been enabled"; regression test; golden updates.
  - (to do) `Parser.parseScript()` end-of-input check.

## Decided

- `@Options("--z3=...")` on a class or method replaces the global `--z3` value (the usual option stack).
- `escchoose.m` and `gitbug890.model_test` (z3-5.1.0 lost proofs that MBQI does not fix) stay as failures.
- cvc5 'unknown' goldens are kept as cvc5-specific responses; cvc5 timeouts are left; z3-5.1.0 is the default.
- `--smt-batch` stays on its own branch for review.

## Decisions to make

1. **Merging.** Merge `solver-work` into `dev-21`? And `fix/z3-4.3-get-value` into jSMTLIB `dev`, then a jar with it?
   (The OpenJML goldens `( - N )` -> `(- N)`, 23 expected files + 2 test sources, go with that jar.)
2. **`--smt-batch`**: see above -- keep? default? add the public jSMTLIB method?
3. **A fallback for `unknown` results** (retry in a fresh z3 process with MBQI on and a short timeout): worth it?
   (z3 ignores `:smt.mbqi` set mid-session, and ignores time limits on `check-sat-using` with MBQI.)
4. **Internal temporaries in messages**: "Precondition conjunct is false: `_JML__tmp`18 != null`" shows internal names
   (and their numbering differs between runs and solvers). Show the source expression instead?
5. **`escfilesTrace`** suite: it does not run (tests pass `""` as an option, which OpenJML rejects) and its goldens
   are out of date. Repair it?
6. **smtinterpol** support (the `.jar` lookup) is on this branch; keep it, or drop it since only z3 and cvc5 matter now?

## Left to the user

- `gitbug963` (type-checker message changed) and `gitbug963a` (no expected file).
- A full cvc5 run of the whole suite.
