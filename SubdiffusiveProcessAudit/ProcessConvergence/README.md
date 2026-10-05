# Theorem A: scaling limit

This pair checks Theorem A of the introduction, label `t.A`, exposed as
`SubdiffusiveProcess.process_convergence` and proved from `SubdiffusiveProcess.Paper.t_A_short`.
The precise scaling-limit theorem, label `t.scaling.limit`
(`SubdiffusiveProcess.process_convergence_precise`), has no pair of its own.

**What `Challenge.lean` states.** For every model in dimension at least two with disorder
`0 < δ ≤ δ₀(d)`, the annealed laws of the physically rescaled process converge, from every
starting point, to the law of a continuous strong Markov process in the random environment.
Almost surely the process is reversible for a singular measure, its positive-time marginals
are absolutely continuous with respect to that measure and not Gaussian, its annealed mean
exit time from a cube of side `r ∈ (0,1]` is at most `C r^(2+η)`, and its paths satisfy
`limsup_{t↓0} t^(−γ)|Z_t − Z₀| = ∞` for every `γ > 1/(2+η)`; in dimension two `η = τ²/log 3`.

**How to read the encoding.**

- *The process.* The limit is a continuous Markov kernel from (environment, starting point) to
  continuous paths. It is strong Markov in the following sense: it restarts at every finite stopping
  time of the usual augmentation of the path filtration. The pre-limit processes, for each
  cutoff `N`, are attached to their weak elliptic resolvents: the resolvent of the Feller
  semigroup agrees, on every bounded open convex set `W`, with the weak `H¹(W)` solution of
  `μρu − ∇·(c∇u) = ρf`, where `c` and `ρ` are the cutoff coefficient and speed density.
  Together with the axioms of a `C₀` resolvent, this determines the semigroup; it is the
  paper's construction of the diffusion. The finite-dimensional distributions of the path laws
  are those of the semigroup. The identification with the solution of the stochastic
  differential equation is in the paper only.
- *Clock normalization.* The cutoff process of index `0` (`KN 0`) has generator `ahom₀⁻¹ ρ⁻¹∇·(ρ∇)`:
  the coefficient `cutoffCoefficient` carries the factor `ahom⁻¹` and the speed density
  `cutoffSpeedDensity` does not. The rescaling therefore uses the time factor
  `physicalTimeFactor = ahom₀ · 3^(2N)/ahom_N`, whose factor `ahom₀` cancels that
  normalization and gives the paper's clock `3^(2N)/ahom_N`.
- *Versions on null sets.* The statement quantifies over kernels defined in every environment.
  The almost-sure conclusions keep the paper's order: "for every `x`, almost surely" and
  "almost surely, for every `x`" are written as such.
- *Measurable structure.* The theorem takes `[MeasurableSpace C(ℝᵈ,ℝ)]` and
  `[BorelSpace C(ℝᵈ,ℝ)]` as arguments because Mathlib has no canonical σ-algebra on spaces of
  continuous functions. The Borel structure is unique, so this loses nothing.
- *The effective diffusivity* `ahom` is defined as the infimum over cube scales of the
  normalized trace of the expected coarse-grained matrix; this is the paper's limit, since
  the sequence is nonincreasing.

The solution applies the library theorem without adding a hypothesis or dropping a
conclusion. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
