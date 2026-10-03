# Subdiffusive process

A Lean 4 formalization of

> Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi,
> *Anomalous scaling limit of a Brownian particle in a log-correlated potential*.

The paper studies a Brownian particle driven by the gradient of a
log-correlated random potential, its subdiffusive scaling limit, and the
elliptic estimates underlying that limit. The development uses
[Mathlib](https://github.com/leanprover-community/mathlib4),
[CoarseGraining](https://github.com/nitromannitol/CoarseGraining) and
[MarkovProcess](https://github.com/nitromannitol/MarkovProcess).
The [paper source](paper/multifractal.tex), bibliography and figures are included
under [`paper/`](paper/).

This private CI candidate has the measured local results below.
Publication remains subject to author review. The workflows are manual until release.

## Main results

The three introduction theorems are exposed in
[`SubdiffusiveProcess/MainTheorems.lean`](SubdiffusiveProcess/MainTheorems.lean):

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem A (introduction, `t.A`) | `SubdiffusiveProcess.process_convergence` (`Paper.t_A_short`) | Convergence of the analytically characterized, rescaled particle laws, singular marginals, exit-time bounds and anomalous path regularity. |
| Scaling limit (precise form, `t.scaling.limit`) | `SubdiffusiveProcess.process_convergence_precise` (`Paper.t_A`) | Precise scaling-limit conclusions alongside the introduction theorem. |
| Theorem B | `SubdiffusiveProcess.quantitative_homogenization` | Quantitative approximation of the rescaled elliptic problem by its homogenized problem. |
| Theorem C | `SubdiffusiveProcess.anomalous_holder_regularity` | Anomalous Hölder regularity estimates for elliptic solutions. |

The full Lean statements specify the hypotheses and conclusions.
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) records the paper-to-Lean correspondence.

The formal process is the continuous Feller diffusion constructed from weak
elliptic resolvents. For the physical coefficient `a`, its energy is
`∫ a |∇u|² dx` on `L²(a dx)`; the rescaled laws use the energy and speed
measure specified in the paper. The paper identifies this diffusion, from
every starting point, with the solution of
`dX = ∇log a(X) dt + √2 dW` by a localized Itô argument. That
Brownian-driver identification is not formalized here. The Lean scaling-limit
theorem concerns the analytically characterized path laws.

## Verification

The standalone build and fresh clean-clone build passed with zero errors and 23,895 / 23,895 warnings, respectively. Headline A, precise A, B and C use exactly `propext`, `Classical.choice` and `Quot.sound`. Theorem B passed bundled comparator checks locally; the A/C exporters require a higher host memory-mapping limit and run in GitHub Actions. The final release also awaits the port team’s linter-warning fixes. The code-only production scan found no incomplete proofs or added axioms.

The release checks require a successful standalone build, no incomplete
production proofs, and axiom reports containing exactly `propext`,
`Classical.choice` and `Quot.sound` for each main theorem.
The A comparator checks the exact introduction theorem `Paper.t_A_short`;
the precise A form has its own axiom report. The three Mathlib-only comparator challenges each have an intentional
statement-level `sorry`; their solutions are checked separately.

Two verification runners are provided. The bundled Palomar route runs in
GitHub Actions for this candidate; the pinned standalone-tool route is also available:

- The pinned comparator workflow follows the verification-tool revisions in
  [Superdiffusion at 7f20476](https://github.com/scottnarmstrong/Superdiffusion/tree/7f20476).
  It runs Lean and NanoDa replay through `leanprover/comparator`.
- The Palomar workflow uses `lake comparator` and the NanoDa and con-ron
  kernels bundled with the selected Lean toolchain, following
  [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/blob/2891de4c48955af824969a263d31b25e7a9a1406/scripts/verify-comparator.sh).

Each route requires every comparator pair to be present and to pass, and
records its own verification results.

## Size

The production library contains 5,860 Lean files and 1,561,884 physical lines. Comparator sources are counted separately.

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
lake build
lake build SubdiffusiveProcess.Meta.AxiomsAudit
```

Lean and Mathlib are pinned to `v4.35.0-rc2`. CoarseGraining and MarkovProcess
are pinned in [`lake-manifest.json`](lake-manifest.json). These two dependency
commits currently require access to the private `nitromannitol` repositories.
Public publication requires making the pinned commits available publicly. The first build also
compiles these source dependencies and may take several hours.

For the pinned comparator route, build the tool revisions in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) and set
`COMPARATOR_BIN`, `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT` and
`COMPARATOR_NANODA` to their executable paths, then run:

```bash
./scripts/run_comparators.sh
```

For the bundled Palomar route, install `bubblewrap`. On Linux, the bundled
exporter needs a memory-mapping limit of at least 131,072 for this development.
If `/proc/sys/vm/max_map_count` is lower, a host administrator can raise it
with `sudo sysctl -w vm.max_map_count=262144`. Then run:

```bash
./scripts/run_comparators.sh --palomar
```

Logs are saved under `.lake/comparator-logs/`. Each fresh audit checkout is
retained under `.lake/comparator-runs/`; existing build artifacts are preserved. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build and verification conventions.

## Repository layout

```text
SubdiffusiveProcess.lean             Library root
SubdiffusiveProcess/
  MainTheorems.lean                  Theorems A, B and C
  Paper/                            Supporting paper results
  Meta/AxiomsAudit.lean              Explicit axiom-report target
SubdiffusiveProcessAudit/            Comparator challenges and solutions
paper/                              Paper sources, bibliography and figures
scripts/                            Local verification runners
.github/workflows/                  Manual build and comparator workflows
```

## How this was built

The development used AI-assisted proof writing under human direction.
[`formalization.yaml`](formalization.yaml) records the available automation
and review information; measured local results and the independent comparator workflow are described above.

## Authors and citation

The Lean development is by **Scott Armstrong**, **Ahmed Bou-Rabee** and
**Tuomo Kuusi**. Use [`CITATION.cff`](CITATION.cff) to cite it.

## License

The Lean development is licensed under Apache License 2.0; see
[`LICENSE`](LICENSE). The paper is included with the authors' authorization;
its publication license is not specified by this software license.
