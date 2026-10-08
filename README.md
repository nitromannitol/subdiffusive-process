# Anomalous scaling limit of a Brownian particle in a log-correlated potential

A machine-checked **Lean 4** formalization of the paper

> Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi,
> *Anomalous scaling limit of a Brownian particle in a log-correlated potential*
> (preprint forthcoming).

The paper's source, bibliography, figures and compiled PDF are included under
[`paper/`](paper/). The three main theorems of the paper are proved, in the form in
which its introduction states them, **for every random environment that satisfies the
paper's standing assumptions**.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4)
and on two public libraries:
[CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining), the
homogenization library of Armstrong and Kuusi, and
[MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess), a library of
continuous-time Markov processes and Feller semigroups.

[![CI](https://github.com/nitromannitol/subdiffusive-process/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/subdiffusive-process/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/subdiffusive-process/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/subdiffusive-process/actions/workflows/comparator.yml)
## What is proved

The paper studies a Brownian particle in `ℝᵈ`, `d ≥ 2`, whose drift is the gradient of a
log-correlated random potential:

> `dX = ∇ log a(X) dt + √2 dW`,  `a(x) = exp(Σₖ (γₖ(x) − γₖ(0)))`.

The potential is a sum of independent smooth random fields `γ₀, γ₁, γ₂, …`, where `γₖ` is
a copy of `γ₀` stretched by the factor `3ᵏ`. The fluctuations therefore have the same
size at every scale. The size is set by a small parameter `δ`, the *disorder strength*.
Keeping only the fields `γ₀, …, γ_L` gives the *infrared cutoff* coefficient `a_L`, whose
homogenized (effective) diffusivity `ahom_L` decreases as a power of the scale `3^L`.
So the particle is subdiffusive: the time to travel a distance `r` grows faster than `r²`.
The model is stated precisely in [Standing assumptions and scope](#standing-assumptions-and-scope).

The three main results, formalized as stated in the introduction of the paper, are
collected in [`SubdiffusiveProcess/MainTheorems.lean`](SubdiffusiveProcess/MainTheorems.lean).

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem A (label `t.A`) | `SubdiffusiveProcess.process_convergence` | The rescaled particle converges to a singular, non-Gaussian diffusion with anomalous exit times. |
| Theorem A, precise form (label `t.scaling.limit`) | `SubdiffusiveProcess.process_convergence_precise` | The stronger quenched form from which Theorem A follows. |
| Theorem B (label `t.B`) | `SubdiffusiveProcess.quantitative_homogenization` | Quantitative homogenization of the Dirichlet problem, uniformly in the cutoff. |
| Theorem C (label `t.C`) | `SubdiffusiveProcess.anomalous_holder_regularity` | Large-scale Hölder regularity with exponent close to one, and a Liouville theorem. |

**Theorem A (scaling limit, `t.A`).** Let `d ≥ 2`. There is `δ₀(d) > 0` such that, for every
model with `0 < δ ≤ δ₀`, there is a continuous strong Markov process `Z` on `ℝᵈ` in the
random environment, with quenched laws `Pₓ` when started at `x`, such that:

1. *Convergence.* For every `x`, as `N → ∞`, the annealed law of the rescaled particle
   `(3⁻ᴺ X(3²ᴺ t / ahom_N))_{t ≥ 0}`, started at `X₀ = 3ᴺx`, converges to the annealed law
   of `Z` started at `x`. Here `X` is the diffusion with generator `a⁻¹ ∇·(a ∇)` and
   `ahom_N` is the effective diffusivity of `a_N`.
2. *Reversible measure.* Almost surely, `Z` is reversible with respect to a measure `μ` that
   is singular with respect to Lebesgue measure.
3. *Anomalous scaling.* There are `C < ∞` and `η > 0`, depending only on `d` and the law of
   `γ₀`, such that the first exit time `σ_r` of `Z` from the cube of side `r` centred at its
   starting point satisfies `E[Eₓ σ_r] ≤ C r^(2+η)` for every `x` and every `r ∈ (0, 1]`.
   For every `x`, almost surely, `Pₓ`-almost every path satisfies
   `limsup_{t↓0} t^(−γ) |Z_t − Z₀| = ∞` for every `γ > 1/(2+η)`. In dimension two one can
   take `η = τ²/log 3`, where `τ² = log E exp γ₀(0)`.
4. *Non-Gaussian marginals.* Almost surely, for every `x` and `t > 0`, the law of `Z_t` is
   absolutely continuous with respect to `μ` and is not Gaussian.

In Lean, `Z` is given by a continuous Markov kernel from (environment, starting point) to
continuous paths that has the strong Markov property at stopping times of the usual
augmentation, and the pre-limit processes are fixed by their weak elliptic resolvents.
The *precise form* (`t.scaling.limit`) gives more: in one common environment, almost
surely, the path laws of the rescaled processes converge weakly uniformly over starting
points in compact sets; the reversible measures converge locally weakly to a non-atomic,
fully supported, singular measure; the effective diffusivities satisfy
`ahom_m / ahom_ℓ ≤ C 3^(−η(m−ℓ))` for `ℓ ≤ m`; the exit times satisfy
`E ∫ σ_k dK ≤ C 3^(−(2+η)k)` at the discrete scales `3⁻ᵏ`; the path law is singular with
respect to every mixture of Brownian laws; and the pointwise Hölder exponent at time zero
is at most `1/(2+η)`.

**Theorem B (quantitative homogenization, `t.B`).** For `0 ≤ L ≤ M` let
`A_{L,M}(x) = ahom_L⁻¹ a_L(3ᴹx)` on the unit cube `□₀ = (−½, ½)ᵈ`. For `f ∈ L²(□₀)` and
`h ∈ H²(□₀)`, let `u_{L,M}` solve `−∇·(A_{L,M} ∇u) = f` in `□₀` with `u = h` on the boundary,
and let `u_hom` solve `−Δu = f` with the same boundary values. The error
`D_{L,M} = ‖u_{L,M} − u_hom‖_{L²} + ‖∇u_{L,M} − ∇u_hom‖_{H⁻¹} + ‖A_{L,M} ∇u_{L,M} − ∇u_hom‖_{H⁻¹}`
measures the difference of solutions, gradients and fluxes.

1. *Uniform in the cutoff.* For every `ϑ ∈ (0,1)` and `q ∈ [1,∞)` there are `δ₀(ϑ,q,d) > 0`
   and `C(ϑ,q,d) < ∞` such that, for `δ ≤ δ₀`, there are random variables `Z_{L,M} ≥ 1`
   with `sup_{L ≤ M} ‖Z_{L,M}‖_{Lᵠ} ≤ C` and, almost surely, simultaneously for all
   `L ≤ M`, `f` and `h`,
   `D_{L,M} ≤ Z_{L,M} δ^ϑ (‖f‖_{L²} + ‖h‖_{H²})`.
   If `f = 0`, the factor `δ^ϑ` can be replaced by `Cδ`.
2. *Algebraic rate at a fixed cutoff.* There is `α_hom(d) > 0`, chosen before the cutoff
   and the moment order, such that for every `L` and `q ≥ 1` there is a random variable
   `Y_{L,q} ≥ 1` with `‖Y_{L,q}‖_{Lᵠ} ≤ C(L,q,d,δ)` and, almost surely, simultaneously for
   all `M ≥ L`, `f` and `h`,
   `D_{L,M} ≤ Y_{L,q} 3^(−α_hom (M−L)) (‖f‖_{L²} + ‖h‖_{H²})`.
   No smallness of `δ` is needed here beyond the model's own range `δ ≤ ½`.

The Lean statement also asserts that the two Dirichlet problems have unique weak solutions,
which the paper takes for granted.

**Theorem C (large-scale Hölder regularity and a Liouville theorem, `t.C`).** There are
`δ₀(d) > 0`, `C₀(d)` and `C(d)` such that, for `δ ≤ δ₀`, with
`γ_reg = 1 − C₀ δ √|log δ|`, and with `L` ranging over `ℕ ∪ {∞}` (where `a_∞ = a`):

1. *Large-scale Hölder estimate.* For every `γ ∈ [½, γ_reg]`, every `L` and every outer
   scale `m`, there is a random minimal scale `𝓛_L(γ,m)` with
   `P[𝓛_L(γ,m) > k] ≤ C exp(−(1−γ)² (k−C)₊ / (C δ² |log δ|))` for every `k ∈ ℕ`. Almost
   surely, for every `L` and `m`, every `a_L`-harmonic function `u` on the cube `□_m`
   of side `3ᵐ` and every cube `z + □_n ⊆ □_{m−1}` with `n ≤ m − 𝓛_L(γ,m)` satisfy
   `‖u − (u)_{z+□_n}‖_{L²(z+□_n)} ≤ C 3^(−γ(m−n)) ‖u − (u)_{□_m}‖_{L²(□_m)}` and
   `‖a_L^{1/2} ∇u‖_{L²(z+□_n)} ≤ C 3^((1−γ)(m−n)) ‖a_L^{1/2} ∇u‖_{L²(□_m)}`
   (all norms are averaged over their cube).
2. *Liouville theorem.* Almost surely, for every `L`, every `a_L`-harmonic function on `ℝᵈ`
   with `liminf_{R→∞} R^(−γ_reg) inf_c ‖u − c‖_{L²(B_R)} = 0` is constant.

## Standing assumptions and scope

1. **Every theorem is about every model.** The
   theorems hold for every `GMCModel d` (`SubdiffusiveProcess.Model.GMCModel`) with `d ≥ 2`
   and small disorder `δ ≤ δ₀(d)`. For Theorem B(1) the threshold also depends on `ϑ` and
   `q`, and Theorem B(2) needs no smallness beyond the model's own range `δ ≤ ½`.
   The constructor `SubdiffusiveProcess.Model.nonempty_gmcModel_of_zeroLevelLaw` produces a
   model from a zero-level law, that is, from a probability law for `γ₀` with the properties
   listed next. A `GMCModel` packages the paper's assumptions: independent layers
   `γ₀, γ₁, …` of locally `C¹ˑ¹` potentials with `γₖ` distributed as `γ₀(3⁻ᵏ ·)`;
   (g1) stationarity, mean zero and range of dependence `√d`; (g2) the exponential-moment
   bound `E exp(δ⁻²(‖γ₀‖ + ‖∇γ₀‖ + ‖∇²γ₀‖)²) ≤ 2` on the unit cube; (g3) invariance under
   signed coordinate permutations and under `γ₀ ↦ −γ₀`; (g4) `τ² = log E exp γ₀(0) > 0`.
   The local `C¹ˑ¹` regularity is part of the type of a potential, so it holds for every
   sample and not only almost surely.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The axiom report of each main theorem consists of
   exactly `propext`, `Classical.choice` and `Quot.sound`. The main theorems rely on no
   unproved result: everything they use, including the facts the paper cites from the
   literature, is available in mathlib, CoarseGraining or MarkovProcess, or is proved in
   this repository.
3. **The formal process.** The diffusion `X` and its limit `Z` are the continuous Feller
   diffusions constructed from weak elliptic resolvents, described by their analytic path
   laws. **The identification of `X` with the solution of the stochastic differential
   equation `dX = ∇ log a(X) dt + √2 dW` is proved in the paper only and is not
   formalized.** The Lean theorems make no statement about a Brownian motion `W` or an
   Itô integral.
4. **Versions on null sets.** Theorem A uses versions defined in every environment. The
   limiting kernel is replaced by the law of a constant path on a measurable null set of
   environments, and a cutoff semigroup is the identity outside the probability-one event
   on which it is built. This preserves every almost-sure statement. The order of
   quantifiers is as in the paper: "for every `x`, almost surely" allows the null set to
   depend on `x`, while "almost surely, for every `x`" gives one common event.
5. **Clock normalization.** The cutoff process of index `0` in the convergence statement
   (`KN 0`) is clock-normalized: its generator is `ahom₀⁻¹` times the physical one. The
   physical rescaling therefore uses the time factor
   `T_N = ahom₀ · 3^(2N) / ahom_N` (`physicalTimeFactor`), and the factor `ahom₀` cancels
   the normalization, giving the paper's clock `3^(2N) / ahom_N`.
6. **Norms and conventions.** Cubes and balls use the sup norm; quadratic energies use the
   Euclidean norm. In Theorem B, the negative norms are the volume-normalized, componentwise
   duals of `H¹₀` (tests vanish on the boundary), and the `H²` norm of the boundary datum is
   the sum of the `L²` sizes of the function, its gradient and its Hessian; another
   equivalent `H²` norm changes only the constants. The effective diffusivity `ahom_m` is
   defined as the infimum, over the cubes `□_n` of side `3ⁿ`, of the normalized trace of the
   expected coarse-grained matrix of `a_m` on `□_n`; this equals the paper's limit as
   `n → ∞` because that sequence is nonincreasing.
7. **Scope of the Liouville theorem.** Theorem C gives large-scale oscillation and
   weighted-energy bounds above a random minimal scale, and a Liouville theorem for entire
   weakly harmonic functions whose normalized `L²` oscillation has subcritical `liminf`
   growth. Its conclusion is a constant continuous representative of the weak solution.
   It makes no claim about pointwise Hölder regularity at microscopic scales.
8. **Total real-valued definitions.** Lean's real-valued definitions are total: division by
   zero, `Real.log 0`, a non-integrable integral and a non-summable series all have
   conventional values, `ENNReal.toReal ∞ = 0`, and a supremum or infimum over an empty
   set is `0`. Analytic conclusions therefore come with the positivity, finiteness,
   integrability and boundedness hypotheses that the theorem statements spell out.
   Where a process has been killed, that is, sent to a cemetery point, the
   lifetime-value function returns the starting point; this is only a convention that
   makes the function total.
9. **Explicit versus implicit.** Some statements make explicit what the paper leaves
   implicit, for example measurability of the random variables, or existence and
   uniqueness of the weak Dirichlet solutions in Theorem B. Some intermediate lemmas repeat
   hypotheses that the model already contains (such as `d ≥ 2` or `δ > 0`); they do not
   narrow the class of models.
10. **Statements without a formal counterpart.** Statements of the paper without a formal
    counterpart in this repository, besides the identification with the stochastic
    differential equation: none. The correspondence table in
    `CORRESPONDENCE.md` maps 160 statements and passages of the paper to Lean
    declarations; an entry names the declaration that formalizes a statement, and a statement
    without one is marked **Paper-only**. For some passages the section *Audit exports* of
    that file names further declarations that state the passage in the form in which the
    paper does. The independent comparator check below covers the statements of the main
    theorems themselves.

## Guarantees

- **No `sorry`.** The library has none. The three comparator challenges under
  [`SubdiffusiveProcessAudit/`](SubdiffusiveProcessAudit/) each contain one intentional
  statement-level `sorry`, which the corresponding solution proves.
- **Standard axioms only.** The axiom report of each of the 4 main
  theorems lists exactly `propext`, `Classical.choice` and `Quot.sound`, and so does that of every theorem of the
  [audit exports](CORRESPONDENCE.md#audit-exports) that is named there by its full name.
  [`SubdiffusiveProcess/Meta/AxiomsAudit.lean`](SubdiffusiveProcess/Meta/AxiomsAudit.lean)
  prints the reports, and `scripts/check_axioms.py` fails on any other axiom, on `sorryAx`,
  on a missing or an unexpected report.
- **Builds from a clean checkout.** `lake build` of this tree, in a fresh build directory,
  compiled 16,405 jobs with 0 warnings and no errors, and a fresh
  clone of the repository builds in the same way. The continuous-integration build rejects
  any warning.
- **Independent check of the statements.** Theorems A, B and C are restated in
  [`SubdiffusiveProcessAudit/`](SubdiffusiveProcessAudit/) using mathlib alone, one
  challenge file per theorem. The solution file proves each restatement from the library,
  and [leanprover/comparator](https://github.com/leanprover/comparator) checks that the
  statement is proved, with only the three standard axioms, through independent
  implementations of the Lean kernel. See
  [`SubdiffusiveProcessAudit/README.md`](SubdiffusiveProcessAudit/README.md). The precise
  form of Theorem A has its own axiom report but no separate challenge.
- **Pinned toolchain and dependencies.** Lean and mathlib `v4.35.0-rc2`; CoarseGraining and
  MarkovProcess at the exact revisions recorded in [`lake-manifest.json`](lake-manifest.json)
  (see [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the version in
  [`paper/`](paper/), pinned to `6532069f529ce5e4499526a1267309c7db9dee22`.

## Size

The library contains 5,884 Lean files with 1,592,483 physical lines,
on top of mathlib, CoarseGraining and MarkovProcess. The comparator sources are counted
separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

The two source dependencies have no prebuilt cache, so the first build compiles them as
well as the library. With the dependencies already built, a fresh build of the library took
about 87 minutes on an Intel i9-9900X machine running eight concurrent Lean processes.

`import SubdiffusiveProcess` loads the main theorems and what they use. The other modules,
including most of those cited in `CORRESPONDENCE.md`, are built by `lake build` and imported
individually, for example `import SubdiffusiveProcess.Paper.app_a_orlicz_clt_scaling`.

The dependencies are public repositories, pinned to exact commits in
[`lake-manifest.json`](lake-manifest.json):

- CoarseGraining: `https://github.com/scottnarmstrong/CoarseGraining` at
  `310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be`.
- MarkovProcess: `https://github.com/scottnarmstrong/MarkovProcess` at
  `666cda029098a1106914fc9fa7abd1727573284a`.

To reproduce the axiom reports:

```bash
lake env lean SubdiffusiveProcess/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

To build the paper, run `latexmk -pdf multifractal.tex` in [`paper/`](paper/).

## Running the comparators

Each comparator pair has a configuration `SubdiffusiveProcessAudit/<Pair>/comparator.json`
that permits exactly `propext`, `Classical.choice` and `Quot.sound`. The comparator checks
that the solution proves the challenge statement, compares their dependency closures, and
replays the proof with the Lean, NanoDa and con-ron kernels.

To run all three pairs locally with the tools bundled with the pinned Lean toolchain:

```bash
./scripts/run_comparators.sh --palomar
```

This needs `bubblewrap` and, on Linux, a memory-mapping limit of at least 131072
(`sudo sysctl -w vm.max_map_count=262144`). Logs are kept under `.lake/comparator-logs/`.
The [comparator workflow](.github/workflows/comparator.yml) runs the same checks on
GitHub-hosted runners, one job per pair; see [`CI_ARTIFACTS.md`](CI_ARTIFACTS.md).

There are two continuous-integration workflows: **CI** builds the library and checks the
axiom reports; **Comparator audit** checks all three challenge/solution pairs. CI runs on
pushes to `main` that change code or build configuration. Both workflows can be started
manually from the [Actions page](https://github.com/nitromannitol/subdiffusive-process/actions).
See [`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
SubdiffusiveProcess.lean          the root module, importing the main theorems
SubdiffusiveProcess/
  MainTheorems.lean               Theorems A, B and C, stated in full
  Model/                          the standing random environment (GMCModel)
  Paper/                          the paper's statements and their proofs, one module each
  Paper/Foundations/AuditExports/ the audit exports: some passages of the paper stated in
                                  the form in which the paper states them
  Meta/AxiomsAudit.lean           the axiom report, compiled by `lake build`, not imported by the root
  ...                             supporting theory: coarse graining, elliptic regularity,
                                  Sobolev and Besov spaces, Dirichlet forms, probability
SubdiffusiveProcessAudit/         the mathlib-only restatements and their solutions
paper/                            the paper: source, bibliography, figures, PDF
scripts/                          axiom check and comparator runners
.github/workflows/                build and comparator workflows
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and
OpenAI (GPT) and, for some auxiliary proof work, DeepSeek, Mistral and Z.ai (GLM) models, under
the direction of the authors. Every proof is checked by the Lean kernel. The models, tooling,
hardware and review status are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Scott Armstrong**, **Ahmed Bou-Rabee** and **Tuomo Kuusi**.
To cite it, use [`CITATION.cff`](CITATION.cff).

Funding: Scott Armstrong was supported by NSF grants DMS-2000200 and DMS-2350340, and
Tuomo Kuusi by the Academy of Finland and by the European Research Council (ERC) under the
European Union's Horizon 2020 research and innovation programme (grant agreement No
818437).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
The paper in [`paper/`](paper/) is included with its authors' permission; its publication
licence is not set by this software licence.
