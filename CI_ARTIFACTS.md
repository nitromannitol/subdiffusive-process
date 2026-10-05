# Hosted comparator workflow and its prebuilt inputs

The workflow [`.github/workflows/palomar.yml`](.github/workflows/palomar.yml) runs the
independent comparator checks on GitHub-hosted runners, with the kernels bundled with the
Lean toolchain. It runs one job per comparator pair: Theorem A
(`ProcessConvergence`), Theorem B (`QuantitativeHomogenization`) and Theorem C
(`AnomalousHolderRegularity`). Each job has a 180-minute limit. The planning estimates, which
include download, elaboration, export and all kernels, are 90, 60 and 90 minutes
respectively. They are estimates, not measurements; each job saves its actual phase timings in
`result.json`.

## Why prebuilt inputs

The whole development takes many CPU-hours to compile, far more than a single hosted job
allows. The workflow therefore restores a compiled copy of the library and of the two source
dependencies, and compiles only the challenge and solution of the pair being checked.

**What this does and does not establish.** The trust in a comparator result rests on the
kernel replay and the comparison described below, not on who produced the compiled files.
The hashes below tie the compiled inputs to the checked source; an artifact is not itself a
verification receipt. A from-scratch build, the zero-warning check and the axiom audit of the
main theorems are separate checks, run by [`build.yml`](.github/workflows/build.yml).

## What a job does

1. **Fetch the dependencies.** It fetches the exact CoarseGraining and MarkovProcess commits
   recorded in `lake-manifest.json` from their public repositories, with Git's system and user
   configuration and credential helpers disabled. A successful run therefore shows that the
   pins can be fetched anonymously.
2. **Restore and validate the inputs.** The compiled library and dependencies are published
   as release assets, in chunks below GitHub's 2 GiB asset limit, together with a manifest.
   The workflow requires the SHA-256 of the manifest as a dispatch input, while
   [`.github/prebuilt.json`](.github/prebuilt.json) records the asset tag and a key over all
   proof and configuration inputs. Before extracting anything, the restore checks the exact
   Lean version, the toolchain file, every Lean source file and comparator configuration
   (by hash) and the dependency revisions against the checked-out commit. It validates every
   transport chunk and every extracted file, refuses unexpected members and symbolic links, and
   checks the restored files again before and after verification. Changes to documentation do
   not change the key. There is no fallback to a cold build.
3. **Elaborate the pair afresh.** Only the selected challenge and solution are compiled, with
   the pinned Lean compiler, into fresh output paths. The compiled files of the audit modules
   are never taken from the uploaded bundle.
4. **Export and compare.** The bundled `leanexport` exports those fresh modules inside a
   network-isolated `bubblewrap` sandbox. `lake comparator --challenge-from-export
   --solution-from-export` then compares the theorem statements and their dependency closures,
   checks that only the permitted axioms occur, and replays the solution independently with the
   Lean kernel, NanoDa and con-ron.
5. **Report.** A final job fails unless every matrix job succeeded. Per-pair logs and
   timings are uploaded as workflow artifacts.

The export step needs a high memory-mapping limit, so the jobs run
`sudo sysctl -w vm.max_map_count=262144` first.

## Producing the inputs for a commit

After building the checkout independently:

```bash
python3 scripts/prebuilt_artifacts.py create --root . \
  --project-build .lake/build --packages .lake/packages --output ARTIFACT_DIR
```

Upload `manifest-COMMIT.json` and the `prebuilt.tar.zst.part*` files as assets of a release
whose tag is recorded in `.github/prebuilt.json`. Each manifest is bound to its exact commit
and is immutable; identical source snapshots share their archive chunks. Dispatch the workflow
with the manifest's SHA-256. Passing the hash as an input avoids a circular dependency
between a commit and a manifest that mentions it. The assets are read with the ordinary
Actions token, which is not passed to the compiler or to the export sandbox.

To check a restore locally:

```bash
python3 scripts/prebuilt_artifacts.py restore --manifest ARTIFACT_DIR/manifest.json \
  --manifest-sha256 MANIFEST_SHA256
./scripts/run_comparators.sh --palomar --prebuilt --pair ProcessConvergence
```
