# Independent verification

`leanchecker` (in the Lean toolchain, `lean --version` = v4.33.0) reloads the compiled `.olean`
files and re-checks every declaration with a fresh kernel, so it catches anything that bypassed
the type checker while the files were compiled (environment hacks, `implemented_by`, unsafe code,
…).  `check.sh` runs it over every module of the development; `test/Axioms.lean` prints the axioms
of the final theorems (`propext`, `Classical.choice`, `Quot.sound` only).  Together these are the
"trust anchors" a reviewer needs: the statements are in `Thomson/Complete.lean` and the
directory READMEs, the kernel is the only judge, and nothing depends on `native_decide`
(`Lean.ofReduceBool`).
