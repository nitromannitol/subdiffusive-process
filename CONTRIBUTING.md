# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues
and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # compile the two source dependencies and the library
```

The toolchain is pinned in `lean-toolchain` and managed by
[elan](https://github.com/leanprover/elan). The first build compiles CoarseGraining and
MarkovProcess from source, which takes a long time; the README records a measured build time.
The library must build with **no warnings**. The only files that contain a `sorry` are the
three comparator challenges under `SubdiffusiveProcessAudit/*/Challenge.lean`, each with
exactly one, in its final theorem.

`lake build SubdiffusiveProcess` builds the library alone, and `lake build
SubdiffusiveProcessAudit` builds the comparator files.

## The main results and the axiom audit

The main theorems are in `SubdiffusiveProcess/MainTheorems.lean`: Theorem A in its
introduction form (`process_convergence`) and its precise form (`process_convergence_precise`),
Theorem B (`quantitative_homogenization`) and Theorem C (`anomalous_holder_regularity`).
Their axiom reports must consist of exactly `propext`, `Classical.choice` and
`Quot.sound`:

```bash
lake env lean SubdiffusiveProcess/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

`SubdiffusiveProcess/Meta/AxiomsAudit.lean` is deliberately not imported by the library root,
because a `#print axioms` command runs again whenever its module is rebuilt. The check script
fails on `sorryAx`, on any other axiom, on a warning and on a missing, unexpected or duplicate
report. The reports are those of the four main theorems and of the theorems of the audit exports
that the table in `CORRESPONDENCE.md` names by their full names.

## Attributions in comments

Comments of the form "adapted from `Algsuperdiff/…`" refer to the Lean library `Algsuperdiff` of the
public repository [scottnarmstrong/Superdiffusion](https://github.com/scottnarmstrong/Superdiffusion):
the arguments of the cited module were adapted for this development, and the path after `Algsuperdiff/`
is the module's path in that repository.

## Metaprogramming

`SubdiffusiveProcess/Meta/EventTransport.lean` defines commands that re-issue existing declarations
with some constants replaced by others, and `SubdiffusiveProcess/Paper/obl_ramp_threshold12_transfer.lean`
uses them once, in a single `run_cmd`. Every declaration produced this way is added to the environment
through the kernel like any other, so the axiom reports of the main theorems and of the audit exports
cover them; nothing in the library is trusted beyond the kernel.

## Conventions for Lean files

- Every Lean file uses the module system (`module`, `public import`, `@[expose] public
  section`) and has at most 10,000 lines.
- No `sorry`, `admit`, `native_decide`, new `axiom` or `set_option maxHeartbeats` anywhere in
  the library.
- Keep statements faithful to the paper. Refer to a result of the paper by its LaTeX label,
  as [`CORRESPONDENCE.md`](CORRESPONDENCE.md) does, and never by a line number: line numbers
  change with every edit of the paper.
- Add new declarations under `SubdiffusiveProcess/`. The pinned dependencies under
  `.lake/packages/` are read-only; extend them from this project rather than editing them.
- `lake clean` deletes the compiled dependencies and forces a rebuild of several hours. To
  rebuild only this project, delete its own build output under
  `.lake/build/lib/lean/SubdiffusiveProcess` and run `lake build` again.

## Comparators

Each pair under `SubdiffusiveProcessAudit/` has a mathlib-only `Challenge.lean`, a
`Solution.lean` that proves the same statement from the library, and a `comparator.json` that
permits exactly `propext`, `Classical.choice` and `Quot.sound`. Do not add a declaration to a
challenge that the statement does not need, and do not change a challenge without checking it
against the paper's statement. Run all pairs with `scripts/run_comparators.sh` or
`scripts/run_comparators.sh --palomar`, as described in the README. A missing pair, a missing
tool or a failed kernel check is a failure. Logs are kept under `.lake/comparator-logs/`.

## Continuous integration

`.github/workflows/build.yml` builds the library, rejects any warning and runs the axiom
audit. `.github/workflows/comparator.yml` runs the comparators with separately pinned tools,
and `.github/workflows/palomar.yml` runs them with the tools bundled with the Lean toolchain,
one job per pair; see [`CI_ARTIFACTS.md`](CI_ARTIFACTS.md).
