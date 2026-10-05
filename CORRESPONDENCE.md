# Paper–Lean correspondence

This document maps the statements of the paper
*Anomalous scaling limit of a Brownian particle in a log-correlated potential*
(Armstrong, Bou-Rabee, Kuusi) to their Lean declarations, so that a reader of the paper can
find where each result is proved. The paper is included under [`paper/`](paper/), pinned to
`2806669bc133074d5ff0f3059608f172abf8fda0`; every label below refers to that version.

**Conventions.**

- Lean names are given relative to the namespace `SubdiffusiveProcess`. The module column
  gives the full module name; the file is the corresponding path under the repository root.
- The paper column gives the paper's own `\label` when the statement has one, and otherwise
  the section and title of the statement.
- A row names the declaration that formalizes the statement. It is a reading aid: a count of
  rows, or the fact that a declaration compiles, does not by itself show that it says what
  the paper says. The statements of the main theorems are checked separately, by the
  independent comparator challenges in [`SubdiffusiveProcessAudit/`](SubdiffusiveProcessAudit/).
- A row marked **Paper-only** has no formal counterpart in this repository.
- Where the paper reduces a general cube, scalar or datum to a normalized one by
  translation, scaling or the trivial case of zero data, the declaration may be stated for the
  normalized instance, with the general instance obtained by the same reduction.
- Some intermediate declarations carry side conditions that the paper leaves implicit, for
  example the geometry of an affine lift, a cutoff, or a collar. They are supplied where the
  declaration is used, and none of them appears among the hypotheses of Theorems A, B or C.

## Standing assumptions and scope

1. **Every theorem is about every model, and models are not constructed here.** The
   theorems hold for every `GMCModel d` (`SubdiffusiveProcess.Model.GMCModel`) with `d ≥ 2`
   and small disorder `δ ≤ δ₀(d)`. For Theorem B(1) the threshold also depends on `ϑ` and
   `q`, and Theorem B(2) needs no smallness beyond the model's own range `δ ≤ ½`.
   **The existence of a model at arbitrarily small disorder is not formalized.** The
   constructor `SubdiffusiveProcess.Model.nonempty_gmcModel_of_zeroLevelLaw` produces a model
   only from a *supplied* zero-level law, that is, from a probability law for `γ₀` with the
   properties listed next; it is conditional on that law. The paper's principal example, a
   smooth stationary centred Gaussian field with finite range of dependence, is not
   constructed here. The theorems are therefore implications, and they would say nothing if
   no model existed. A `GMCModel` packages the paper's assumptions: independent layers
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

## The formal process

The process laws are characterized by their weak elliptic resolvents and by their
finite-dimensional distributions under the associated semigroups. This is the paper's
defining analytic construction of the diffusions `X` and `X^(L)` and of the common-scale
cutoff laws. The paper also shows that these laws are the laws of the solutions of the
stochastic differential equation `dX = ∇ log a(X) dt + √2 dW`; that identification is
outside the formally verified surface.

The cutoff process of index `0` (`KN 0`) is clock-normalized: its generator is `ahom₀⁻¹` times
the physical one. The physical rescaling uses the time factor
`T_N = ahom₀ · 3^(2N) / ahom_N`, the definition `SubdiffusiveProcess.physicalTimeFactor`
([PhysicalTimeFactor.lean](SubdiffusiveProcess/Main/PhysicalTimeFactor.lean)). The process `KN 0`
must therefore not be identified directly with the unnormalized law of `X`. The physical
Dirichlet form is `∫ a |∇u|² dx` on `L²(a dx)`; the rescaled form and speed measure are the
pair specified in the paper.

## The main results

| Paper | Lean declaration | Module | Comparator |
| --- | --- | --- | --- |
| `t.A`, Theorem A (introduction) | `process_convergence`, from `Paper.t_A_short` | `SubdiffusiveProcess.MainTheorems` | [`ProcessConvergence`](SubdiffusiveProcessAudit/ProcessConvergence/) |
| `t.scaling.limit`, precise form of Theorem A | `process_convergence_precise`, from `Paper.t_A` | `SubdiffusiveProcess.MainTheorems` | none (separate axiom report) |
| `t.B`, Theorem B | `quantitative_homogenization`, from `Paper.t_B` | `SubdiffusiveProcess.MainTheorems` | [`QuantitativeHomogenization`](SubdiffusiveProcessAudit/QuantitativeHomogenization/) |
| `t.C`, Theorem C | `anomalous_holder_regularity`, from `Paper.t_C` | `SubdiffusiveProcess.MainTheorems` | [`AnomalousHolderRegularity`](SubdiffusiveProcessAudit/AnomalousHolderRegularity/) |

Theorem A follows from its precise form in the paper; here both are proved, and the headline
statement is the one compared by the independent challenge.

## The diffusion and its stochastic differential equation

| Paper | Lean declaration | Treatment |
| --- | --- | --- |
| `s.fixed.coefficient`, analytic construction of the diffusion and its Dirichlet form | `Paper.finiteDimensional_cutoff` and its semigroup and path-kernel results; `Paper.in_crossing` | Formalized: the diffusion is constructed from its weak elliptic resolvent. |
| `s.fixed.coefficient`, interpretation as the solution of the stochastic differential equation; `e.fixed.clock.sde` | none | **Paper-only; not formalized.** |

## All statements

The table below lists 160 statements and passages of the paper, in the order
of the paper, with the Lean declaration that formalizes each.

| Paper label or passage | Lean declaration | Module | Paper source |
| --- | --- | --- | --- |
| `t.A` | `Paper.t_A_short` | `SubdiffusiveProcess.Paper.t_A_short` | [source](paper/multifractal.tex) |
| `t.B` | `Paper.t_B` | `SubdiffusiveProcess.Paper.t_B` | [source](paper/multifractal.tex) |
| `t.C` | `Paper.t_C` | `SubdiffusiveProcess.Paper.t_C` | [source](paper/multifractal.tex) |
| `l.sharp.compare.J` | `Paper.l_sharp_compare_J_convex` | `SubdiffusiveProcess.Paper.l_sharp_compare_J_convex` | [source](paper/multifractal.tex) |
| `e.coarse.grained.ellipticity` | `Paper.d_coarse_grained_ellipticity` | `SubdiffusiveProcess.Paper.d_coarse_grained_ellipticity` | [source](paper/multifractal.tex) |
| `d.mathcal.E` | `Paper.d_mathcal_E` | `SubdiffusiveProcess.Paper.d_mathcal_E` | [source](paper/multifractal.tex) |
| `l.lambdas.stability` | `Paper.l_lambdas_stability` | `SubdiffusiveProcess.Paper.l_lambdas_stability` | [source](paper/multifractal.tex) |
| `p.coarse.grained.poincare` | `Paper.p_coarse_grained_poincare` | `SubdiffusiveProcess.Paper.p_coarse_grained_poincare` | [source](paper/multifractal.tex) |
| `p.coarse.grained.caccioppoli` | `Paper.p_coarse_grained_caccioppoli` | `SubdiffusiveProcess.Paper.p_coarse_grained_caccioppoli` | [source](paper/multifractal.tex) |
| `l.sensitivity.general` | `Paper.l_sensitivity_general_convex` | `SubdiffusiveProcess.Paper.l_sensitivity_general_convex` | [source](paper/multifractal.tex) |
| `l.J.sensitivity` | `Paper.l_J_sensitivity_convex` | `SubdiffusiveProcess.Paper.l_J_sensitivity_convex` | [source](paper/multifractal.tex) |
| `l.coarse.graining.RHS` | `Paper.l_coarse_graining_RHS` | `SubdiffusiveProcess.Paper.l_coarse_graining_RHS` | [source](paper/multifractal.tex) |
| `l.coarse.grained.Caccioppoli.RHS.ASD` | `Paper.l_coarse_grained_Caccioppoli_RHS_ASD` | `SubdiffusiveProcess.Paper.l_coarse_grained_Caccioppoli_RHS_ASD` | [source](paper/multifractal.tex) |
| `p.general.coarse.graining.ASD` | `Paper.p_general_coarse_graining_ASD` | `SubdiffusiveProcess.Paper.p_general_coarse_graining_ASD` | [source](paper/multifractal.tex) |
| `l.sensitivity.for.cutoffs` | `Paper.l_sensitivity_for_cutoffs` | `SubdiffusiveProcess.Paper.l_sensitivity_for_cutoffs` | [source](paper/multifractal.tex) |
| `l.aL.negative.Besov` | `Paper.l_aL_negative_Besov` | `SubdiffusiveProcess.Paper.l_aL_negative_Besov` | [source](paper/multifractal.tex) |
| `lemma:infrared.approx.cutoffs` | `Paper.lemma_infrared_approx_cutoffs_convex` | `SubdiffusiveProcess.Paper.lemma_infrared_approx_cutoffs_convex` | [source](paper/multifractal.tex) |
| `l.annealed.matrix.bounds` | `Paper.l_annealed_matrix_bounds_convex` | `SubdiffusiveProcess.Paper.l_annealed_matrix_bounds_convex` | [source](paper/multifractal.tex) |
| `p.special.two.d.exact.formula` | `Paper.p_special_two_d_exact_formula` | `SubdiffusiveProcess.Paper.p_special_two_d_exact_formula` | [source](paper/multifractal.tex) |
| `lemma.crude.J.bound` | `Paper.lemma_crude_J_bound_convex` | `SubdiffusiveProcess.Paper.lemma_crude_J_bound_convex` | [source](paper/multifractal.tex) |
| `p.coarse.grained.bound` | `Paper.p_coarse_grained_bound` | `SubdiffusiveProcess.Paper.p_coarse_grained_bound` | [source](paper/multifractal.tex) |
| `d.mathcalS.def` | `Paper.d_mathcalS_def` | `SubdiffusiveProcess.Paper.d_mathcalS_def` | [source](paper/multifractal.tex) |
| `d.bLm` | `Paper.d_bLm` | `SubdiffusiveProcess.Paper.d_bLm` | [source](paper/multifractal.tex) |
| `l.ellipticity.bound` | `Paper.l_ellipticity_bound` | `SubdiffusiveProcess.Paper.l_ellipticity_bound` | [source](paper/multifractal.tex) |
| `l.multiscale.response.large.cubes` | `Paper.l_multiscale_response_large_cubes` | `SubdiffusiveProcess.Paper.l_multiscale_response_large_cubes` | [source](paper/multifractal.tex) |
| `l.J.bound.by.Besov` | `Paper.l_J_bound_by_Besov` | `SubdiffusiveProcess.Paper.l_J_bound_by_Besov` | [source](paper/multifractal.tex) |
| `l.Besov.norms` | `Paper.l_Besov_norms` | `SubdiffusiveProcess.Paper.l_Besov_norms` | [source](paper/multifractal.tex) |
| `l.var.bounds` | `Paper.l_var_bounds` | `SubdiffusiveProcess.Paper.l_var_bounds` | [source](paper/multifractal.tex) |
| `p.combine.under.S` | `Paper.p_combine_under_S` | `SubdiffusiveProcess.Paper.p_combine_under_S` | [source](paper/multifractal.tex) |
| `p.homogenization.step` | `Paper.p_homogenization_step` | `SubdiffusiveProcess.Paper.p_homogenization_step` | [source](paper/multifractal.tex) |
| `t.renormalized.diffusivities` | `Paper.t_renormalized_diffusivities` | `SubdiffusiveProcess.Paper.t_renormalized_diffusivities` | [source](paper/multifractal.tex) |
| `p.sharp.asymptotic` | `Paper.p_sharp_asymptotic` | `SubdiffusiveProcess.Paper.p_sharp_asymptotic` | [source](paper/multifractal.tex) |
| `l.laplacian.corrector.energy` | `Paper.l_laplacian_corrector_energy` | `SubdiffusiveProcess.Paper.l_laplacian_corrector_energy` | [source](paper/multifractal.tex) |
| `l.one.step.upper` | `Paper.l_one_step_upper` | `SubdiffusiveProcess.Paper.l_one_step_upper` | [source](paper/multifractal.tex) |
| `l.one.step.lower` | `Paper.l_one_step_lower` | `SubdiffusiveProcess.Paper.l_one_step_lower` | [source](paper/multifractal.tex) |
| `p.homogenized.coefficient.strict.decay` | `Paper.p_homogenized_coefficient_strict_decay` | `SubdiffusiveProcess.Paper.p_homogenized_coefficient_strict_decay` | [source](paper/multifractal.tex) |
| `p.homogenized.coefficient.reciprocal.lower` | `Paper.p_homogenized_coefficient_reciprocal_lower` | `SubdiffusiveProcess.Paper.p_homogenized_coefficient_reciprocal_lower` | [source](paper/multifractal.tex) |
| `p.Holder.regularity` | `Paper.p_Holder_regularity` | `SubdiffusiveProcess.Paper.p_Holder_regularity` | [source](paper/multifractal.tex) |
| `d.good.events` | `Paper.d_good_events` | `SubdiffusiveProcess.Paper.d_good_events` | [source](paper/multifractal.tex) |
| `p.good.scale.mathcal.E` | `Paper.p_good_scale_mathcal_E` | `SubdiffusiveProcess.Paper.p_good_scale_mathcal_E` | [source](paper/multifractal.tex) |
| `p.density.of.good.scales` | `Paper.p_density_of_good_scales` | `SubdiffusiveProcess.Paper.p_density_of_good_scales` | [source](paper/multifractal.tex) |
| `l.bad.scales.for.nabla.gj` | `Paper.l_bad_scales_for_nabla_gj` | `SubdiffusiveProcess.Paper.l_bad_scales_for_nabla_gj` | [source](paper/multifractal.tex) |
| `l.exp.goodscales` | `Paper.l_exp_goodscales` | `SubdiffusiveProcess.Paper.l_exp_goodscales` | [source](paper/multifractal.tex) |
| `l.discounted.J.local` | `Paper.l_discounted_J_local` | `SubdiffusiveProcess.Paper.l_discounted_J_local` | [source](paper/multifractal.tex) |
| `l.centered.energy.good.scale` | `Paper.l_centered_energy_good_scale` | `SubdiffusiveProcess.Paper.l_centered_energy_good_scale` | [source](paper/multifractal.tex) |
| `l.harmonic.approximation.good.scales.GMC` | `Paper.l_harmonic_approximation_good_scales_GMC` | `SubdiffusiveProcess.Paper.l_harmonic_approximation_good_scales_GMC` | [source](paper/multifractal.tex) |
| `l.excess.decay.good.scales.GMC` | `Paper.l_excess_decay_good_scales_GMC` | `SubdiffusiveProcess.Paper.l_excess_decay_good_scales_GMC` | [source](paper/multifractal.tex) |
| `l.iteration.lemma.GMC` | `Paper.l_iteration_lemma_GMC` | `SubdiffusiveProcess.Paper.l_iteration_lemma_GMC` | [source](paper/multifractal.tex) |
| `l.sum.the.errors` | `Paper.l_sum_the_errors` | `SubdiffusiveProcess.Paper.l_sum_the_errors` | [source](paper/multifractal.tex) |
| `l.min.scale.good.scale` | `Paper.l_min_scale_good_scale` | `SubdiffusiveProcess.Paper.l_min_scale_good_scale` | [source](paper/multifractal.tex) |
| `l.cutoff.regularity.response` | `Paper.l_cutoff_regularity_response` | `SubdiffusiveProcess.Paper.l_cutoff_regularity_response` | [source](paper/multifractal.tex) |
| `p.cutoff.regularity.good.scales` | `Paper.p_cutoff_regularity_good_scales` | `SubdiffusiveProcess.Paper.p_cutoff_regularity_good_scales` | [source](paper/multifractal.tex) |
| `l.cutoff.regularity.good.scale.estimates` | `Paper.cutoff_good_scale_estimates` | `SubdiffusiveProcess.Paper.cutoff_good_scale_estimates` | [source](paper/multifractal.tex) |
| `p.cutoff.Holder.regularity` | `Paper.p_cutoff_Holder_regularity` | `SubdiffusiveProcess.Paper.p_cutoff_Holder_regularity` | [source](paper/multifractal.tex) |
| `p.cutoff.Holder.bounded.multiplier` | `Paper.p_cutoff_Holder_bounded_multiplier` | `SubdiffusiveProcess.Paper.p_cutoff_Holder_bounded_multiplier` | [source](paper/multifractal.tex) |
| `t.cutoff.Dirichlet.homogenization` | `Paper.t_cutoff_Dirichlet_homogenization` | `SubdiffusiveProcess.Paper.t_cutoff_Dirichlet_homogenization` | [source](paper/multifractal.tex) |
| `t.fixed.cutoff.Dirichlet.algebraic` | `Paper.t_fixed_cutoff_Dirichlet_algebraic` | `SubdiffusiveProcess.Paper.t_fixed_cutoff_Dirichlet_algebraic` | [source](paper/multifractal.tex) |
| `l.finite.cutoff.coefficient.convergence` | `Paper.l_finite_cutoff_coefficient_convergence` | `SubdiffusiveProcess.Paper.l_finite_cutoff_coefficient_convergence` | [source](paper/multifractal.tex) |
| `t.large.scale.Holder.multifractal` | `Paper.t_large_scale_Holder_multifractal` | `SubdiffusiveProcess.Paper.t_large_scale_Holder_multifractal` | [source](paper/multifractal.tex) |
| `t.scaling.limit` | `Paper.t_A` | `SubdiffusiveProcess.Paper.t_A` | [source](paper/multifractal.tex) |
| `mfd:lem-infrared` | `Paper.mfd_lem_infrared` | `SubdiffusiveProcess.Paper.mfd_lem_infrared` | [source](paper/multifractal.tex) |
| `mfd:lem-cell-ellipticity` | `Paper.lem_cell_ellipticity` | `SubdiffusiveProcess.Paper.lem_cell_ellipticity` | [source](paper/multifractal.tex) |
| `mfd:lem-coercivity` | `Paper.lem_coercivity` | `SubdiffusiveProcess.Paper.lem_coercivity` | [source](paper/multifractal.tex) |
| `mfd:lem-extension` | `Paper.lem_extension` | `SubdiffusiveProcess.Paper.lem_extension` | [source](paper/multifractal.tex) |
| `mfd:lem-primitive` | `Paper.lem_primitive` | `SubdiffusiveProcess.Paper.lem_primitive` | [source](paper/multifractal.tex) |
| `mfd:lem-extremes` | `Paper.lem_extremes` | `SubdiffusiveProcess.Paper.lem_extremes` | [source](paper/multifractal.tex) |
| `mfd:prop-growth` | `Paper.prop_growth` | `SubdiffusiveProcess.Paper.prop_growth` | [source](paper/multifractal.tex) |
| `mfd:lem-neumann-error` | `Paper.mfd_lem_neumann_error` | `SubdiffusiveProcess.Paper.mfd_lem_neumann_error` | [source](paper/multifractal.tex) |
| `mfd:thm-fold` | `Paper.mfd_thm_fold` | `SubdiffusiveProcess.Paper.mfd_thm_fold` | [source](paper/multifractal.tex) |
| `mfd:prop-folded-iteration` | `Paper.prop_folded_iteration` | `SubdiffusiveProcess.Paper.prop_folded_iteration` | [source](paper/multifractal.tex) |
| `mfd:cor-neumann-source` | `Paper.mfd_cor_neumann_source` | `SubdiffusiveProcess.Paper.mfd_cor_neumann_source` | [source](paper/multifractal.tex) |
| `mfd:cor-14` | `Paper.cor_14` | `SubdiffusiveProcess.Paper.cor_14` | [source](paper/multifractal.tex) |
| `mfd:lem-strips` | `Paper.lem_strips` | `SubdiffusiveProcess.Paper.lem_strips` | [source](paper/multifractal.tex) |
| `mfd:lem-15` | `Paper.mfd_lem_15` | `SubdiffusiveProcess.Paper.mfd_lem_15` | [source](paper/multifractal.tex) |
| `mfd:lem-resampling-sum` | `Paper.lem_resampling_sum` | `SubdiffusiveProcess.Paper.lem_resampling_sum` | [source](paper/multifractal.tex) |
| `mfd:prop-16` | `Paper.mfd_prop_16` | `SubdiffusiveProcess.Paper.mfd_prop_16` | [source](paper/multifractal.tex) |
| `mfd:prop-response-compact` | `Paper.mfd_prop_response_compact` | `SubdiffusiveProcess.Paper.mfd_prop_response_compact` | [source](paper/multifractal.tex) |
| `mfd:prop-killed-inverse` | `Paper.prop_killed_inverse` | `SubdiffusiveProcess.Paper.prop_killed_inverse` | [source](paper/multifractal.tex) |
| `mfd:lem-response-reciprocal` | `Paper.lem_response_reciprocal` | `SubdiffusiveProcess.Paper.lem_response_reciprocal` | [source](paper/multifractal.tex) |
| `mfd:lem-19` | `Paper.lem_19` | `SubdiffusiveProcess.Paper.lem_19` | [source](paper/multifractal.tex) |
| `mfd:lem-cutoffs` | `Paper.mfd_lem_cutoffs` | `SubdiffusiveProcess.Paper.mfd_lem_cutoffs` | [source](paper/multifractal.tex) |
| `mfd:prop-regularity` | `Paper.mfd_prop_regularity` | `SubdiffusiveProcess.Paper.mfd_prop_regularity` | [source](paper/multifractal.tex) |
| `mfd:prop-locality` | `Paper.prop_locality` | `SubdiffusiveProcess.Paper.prop_locality` | [source](paper/multifractal.tex) |
| `mfd:prop-killed-consistency` | `Paper.mfd_prop_killed_consistency` | `SubdiffusiveProcess.Paper.mfd_prop_killed_consistency` | [source](paper/multifractal.tex) |
| `mfd:lem-sincos` | `Paper.lem_sincos` | `SubdiffusiveProcess.Paper.lem_sincos` | [source](paper/multifractal.tex) |
| `mfd:prop-21` | `Paper.mfd_prop_21` | `SubdiffusiveProcess.Paper.mfd_prop_21` | [source](paper/multifractal.tex) |
| `mfd:lem-borel-weights` | `Paper.mfd_lem_borel_weights` | `SubdiffusiveProcess.Paper.mfd_lem_borel_weights` | [source](paper/multifractal.tex) |
| `mfd:cor-energy-measures` | `Paper.cor_energy_measures` | `SubdiffusiveProcess.Paper.cor_energy_measures` | [source](paper/multifractal.tex) |
| `mfd:lem-truncation` | `Paper.lem_truncation` | `SubdiffusiveProcess.Paper.lem_truncation` | [source](paper/multifractal.tex) |
| `mfd:prop-boundary` | `Paper.mfd_prop_boundary` | `SubdiffusiveProcess.Paper.mfd_prop_boundary` | [source](paper/multifractal.tex) |
| `mfd:prop-gluing` | `Paper.mfd_prop_gluing` | `SubdiffusiveProcess.Paper.mfd_prop_gluing` | [source](paper/multifractal.tex) |
| `mfd:lem-skeleton` | `Paper.lem_skeleton` | `SubdiffusiveProcess.Paper.lem_skeleton` | [source](paper/multifractal.tex) |
| `mfd:in-deterministic` | `Paper.in_deterministic` | `SubdiffusiveProcess.Paper.in_deterministic` | [source](paper/multifractal.tex) |
| `mfd:lem-prefix-limit` | `Paper.lem_prefix_limit` | `SubdiffusiveProcess.Paper.lem_prefix_limit` | [source](paper/multifractal.tex) |
| `mfd:lem-band` | `Paper.mfd_lem_band` | `SubdiffusiveProcess.Paper.mfd_lem_band` | [source](paper/multifractal.tex) |
| `mfd:in-prefix` | `Paper.mfd_in_prefix` | `SubdiffusiveProcess.Paper.mfd_in_prefix` | [source](paper/multifractal.tex) |
| `mfd:lem-witness` | `Paper.lem_witness` | `SubdiffusiveProcess.Paper.lem_witness` | [source](paper/multifractal.tex) |
| `mfd:prop-allchain` | `Paper.prop_allchain` | `SubdiffusiveProcess.Paper.prop_allchain` | [source](paper/multifractal.tex) |
| `mfd:lem-goodext` | `Paper.mfd_lem_goodext_uniform` | `SubdiffusiveProcess.Paper.mfd_lem_goodext_uniform` | [source](paper/multifractal.tex) |
| `mfd:prop-density` | `Paper.mfd_prop_density` | `SubdiffusiveProcess.Paper.mfd_prop_density` | [source](paper/multifractal.tex) |
| `mfd:thm-C0` | `Paper.mfd_thm_C0` | `SubdiffusiveProcess.Paper.mfd_thm_C0` | [source](paper/multifractal.tex) |
| `mfd:lem-endpoints` | `Paper.mfd_lem_endpoints` | `SubdiffusiveProcess.Paper.mfd_lem_endpoints` | [source](paper/multifractal.tex) |
| `mfd:lem-diff` | `Paper.lem_diff` | `SubdiffusiveProcess.Paper.lem_diff` | [source](paper/multifractal.tex) |
| `mfd:lem-relvar` | `Paper.lem_relvar` | `SubdiffusiveProcess.Paper.lem_relvar` | [source](paper/multifractal.tex) |
| `mfd:prop-conc` | `Paper.prop_conc` | `SubdiffusiveProcess.Paper.prop_conc` | [source](paper/multifractal.tex) |
| `mfd:cor-32` | `Paper.cor_32` | `SubdiffusiveProcess.Paper.cor_32` | [source](paper/multifractal.tex) |
| `mfd:lem-affine` | `Paper.lem_affine` | `SubdiffusiveProcess.Paper.lem_affine` | [source](paper/multifractal.tex) |
| `mfd:lem-shifts` | `Paper.lem_shifts` | `SubdiffusiveProcess.Paper.lem_shifts` | [source](paper/multifractal.tex) |
| `mfd:lem-mass` | `Paper.lem_mass` | `SubdiffusiveProcess.Paper.lem_mass` | [source](paper/multifractal.tex) |
| `mfd:lem-replace` | `Paper.lem_replace` | `SubdiffusiveProcess.Paper.lem_replace` | [source](paper/multifractal.tex) |
| `mfd:thm-prop` | `Paper.mfd_thm_prop` | `SubdiffusiveProcess.Paper.mfd_thm_prop` | [source](paper/multifractal.tex) |
| `mfd:thm-eta` | `Paper.thm_eta` | `SubdiffusiveProcess.Paper.thm_eta` | [source](paper/multifractal.tex) |
| `mfd:thm-c1` | `Paper.mfd_thm_c1` | `SubdiffusiveProcess.Paper.mfd_thm_c1` | [source](paper/multifractal.tex) |
| `mfd:lem-chaos-moments` | `Paper.lem_chaos_moments` | `SubdiffusiveProcess.Paper.lem_chaos_moments` | [source](paper/multifractal.tex) |
| `mfd:prop-chaos-growth` | `Paper.prop_chaos_growth` | `SubdiffusiveProcess.Paper.prop_chaos_growth` | [source](paper/multifractal.tex) |
| `mfd:lem-varying-trace` | `Paper.lem_varying_trace` | `SubdiffusiveProcess.Paper.lem_varying_trace` | [source](paper/multifractal.tex) |
| `mfd:prop-speed-resolvent` | `Paper.prop_speed_resolvent` | `SubdiffusiveProcess.Paper.prop_speed_resolvent` | [source](paper/multifractal.tex) |
| `mfd:prop-uniform-resolvent` | `Paper.mfd_prop_uniform_resolvent` | `SubdiffusiveProcess.Paper.mfd_prop_uniform_resolvent` | [source](paper/multifractal.tex) |
| `tight:lem-static` | `Paper.tight_lem_static` | `SubdiffusiveProcess.Paper.tight_lem_static` | [source](paper/multifractal.tex) |
| `tight:lem-subharmonic` | `Paper.tight_lem_subharmonic` | `SubdiffusiveProcess.Paper.tight_lem_subharmonic` | [source](paper/multifractal.tex) |
| `tight:prop-tightness` | `Paper.tight_prop_tightness` | `SubdiffusiveProcess.Paper.tight_prop_tightness` | [source](paper/multifractal.tex) |
| `mfd:prop-quenched-convergence` | `Paper.mfd_prop_quenched_convergence` | `SubdiffusiveProcess.Paper.mfd_prop_quenched_convergence` | [source](paper/multifractal.tex) |
| `mfd:prop-limit-properties` | `Paper.prop_limit_properties` | `SubdiffusiveProcess.Paper.prop_limit_properties` | [source](paper/multifractal.tex) |
| `mfd:lem-killing` | `Paper.mfd_lem_killing` | `SubdiffusiveProcess.Paper.mfd_lem_killing` | [source](paper/multifractal.tex) |
| `mfd:cor-finite-exit` | `Paper.cor_finite_exit` | `SubdiffusiveProcess.Paper.cor_finite_exit` | [source](paper/multifractal.tex) |
| `mfd:lem-local-normalizations` | `Paper.lem_local_normalizations` | `SubdiffusiveProcess.Paper.lem_local_normalizations` | [source](paper/multifractal.tex) |
| `mfd:lem-finite-trace-tests` | `Paper.lem_finite_trace_tests` | `SubdiffusiveProcess.Paper.lem_finite_trace_tests` | [source](paper/multifractal.tex) |
| `mfd:lem-finite-good-cell` | `Paper.lem_finite_good_cell` | `SubdiffusiveProcess.Paper.lem_finite_good_cell` | [source](paper/multifractal.tex) |
| `mfd:lem-rare-tests` | `Paper.mfd_lem_rare_tests` | `SubdiffusiveProcess.Paper.mfd_lem_rare_tests` | [source](paper/multifractal.tex) |
| `mfd:lem-finite-good-levels` | `Paper.mfd_lem_finite_good_levels` | `SubdiffusiveProcess.Paper.mfd_lem_finite_good_levels` | [source](paper/multifractal.tex) |
| `mfd:lem-finite-stopping` | `Paper.lem_finite_stopping` | `SubdiffusiveProcess.Paper.lem_finite_stopping` | [source](paper/multifractal.tex) |
| `mfd:lem-finite-source-comparison` | `Paper.lem_finite_source_comparison` | `SubdiffusiveProcess.Paper.lem_finite_source_comparison` | [source](paper/multifractal.tex) |
| `mfd:prop-as-dirichlet` | `Paper.prop_as_dirichlet` | `SubdiffusiveProcess.Paper.prop_as_dirichlet` | [source](paper/multifractal.tex) |
| `mfd:prop-as-response-bank` | `Paper.prop_as_response_bank` | `SubdiffusiveProcess.Paper.prop_as_response_bank` | [source](paper/multifractal.tex) |
| `mfd:lem-as-coarse` | `Paper.lem_as_coarse` | `SubdiffusiveProcess.Paper.lem_as_coarse` | [source](paper/multifractal.tex) |
| `mfd:lem-as-regularity` | `Paper.lem_as_regularity` | `SubdiffusiveProcess.Paper.lem_as_regularity` | [source](paper/multifractal.tex) |
| `mfd:prop-as-forms` | `Paper.mfd_prop_as_forms` | `SubdiffusiveProcess.Paper.mfd_prop_as_forms` | [source](paper/multifractal.tex) |
| `mfd:prop-as-quenched` | `Paper.mfd_prop_as_quenched` | `SubdiffusiveProcess.Paper.mfd_prop_as_quenched` | [source](paper/multifractal.tex) |
| `lim:lem-strict-decay` | `Paper.lim_strict_decay` | `SubdiffusiveProcess.Paper.lim_strict_decay` | [source](paper/multifractal.tex) |
| `lim:lem-mean-exit` | `Paper.lim_lem_mean_exit` | `SubdiffusiveProcess.Paper.lim_lem_mean_exit` | [source](paper/multifractal.tex) |
| `lim:thm-nonbrownian` | `Paper.lim_thm_nonbrownian` | `SubdiffusiveProcess.Paper.lim_thm_nonbrownian` | [source](paper/multifractal.tex) |
| `lim:cor-paths` | `Paper.lim_cor_paths` | `SubdiffusiveProcess.Paper.lim_cor_paths` | [source](paper/multifractal.tex) |
| `lim:cor-exit-moments` | `Paper.lim_cor_exit_moments` | `SubdiffusiveProcess.Paper.lim_cor_exit_moments` | [source](paper/multifractal.tex) |
| `lim:thm-measure` | `Paper.lim_thm_measure` | `SubdiffusiveProcess.Paper.lim_thm_measure` | [source](paper/multifractal.tex) |
| `lim:thm-nongaussian` | `Paper.lim_thm_nongaussian` | `SubdiffusiveProcess.Paper.lim_thm_nongaussian` | [source](paper/multifractal.tex) |
| `e.orlicz.two.sided.definition` | `Paper.app_a_orlicz_notation` | `SubdiffusiveProcess.Paper.app_a_orlicz_notation` | [source](paper/multifractal.tex) |
| `e.orlicz.tail.bound` | `Paper.app_a_orlicz_tail_bound` | `SubdiffusiveProcess.Paper.app_a_orlicz_tail_bound` | [source](paper/multifractal.tex) |
| App.A, Converse of the tail bound (Appendix A) | `Paper.app_a_orlicz_tail_converse` | `SubdiffusiveProcess.Paper.app_a_orlicz_tail_converse` | [passage](paper/multifractal.tex) |
| `e.orlicz.triangle.inequality` | `Paper.app_a_orlicz_triangle_finite` | `SubdiffusiveProcess.Paper.app_a_orlicz_triangle_finite` | [source](paper/multifractal.tex) |
| App.A, Triangle inequality for O\_Γ\_σ, countable nonnegative families (Appendix A) | `Paper.app_a_orlicz_triangle_countable` | `SubdiffusiveProcess.Paper.app_a_orlicz_triangle_countable` | [passage](paper/multifractal.tex) |
| `e.max.scaling.O.Gamma.Two` | `Paper.app_a_orlicz_max_scaling` | `SubdiffusiveProcess.Paper.app_a_orlicz_max_scaling` | [source](paper/multifractal.tex) |
| `e.CLT.scaling.O.Gamma.Two` | `Paper.app_a_orlicz_clt_scaling` | `SubdiffusiveProcess.Paper.app_a_orlicz_clt_scaling` | [source](paper/multifractal.tex) |
| `e.moments.OGamma2` | `Paper.l_moments_OGamma2` | `SubdiffusiveProcess.Paper.l_moments_OGamma2` | [source](paper/multifractal.tex) |
| `l.Rosenthal` | `Paper.l_Rosenthal` | `SubdiffusiveProcess.Paper.l_Rosenthal` | [source](paper/multifractal.tex) |
| `p.concentration.for.scales` | `Paper.p_concentration_for_scales` | `SubdiffusiveProcess.Paper.p_concentration_for_scales` | [source](paper/multifractal.tex) |
| `p.concentration.for.scales.exp.sequence` | `Paper.p_concentration_for_scales_exp_sequence` | `SubdiffusiveProcess.Paper.p_concentration_for_scales_exp_sequence` | [source](paper/multifractal.tex) |
| `p.concentration.for.scales.exp.field` | `Paper.p_concentration_for_scales_exp_field` | `SubdiffusiveProcess.Paper.p_concentration_for_scales_exp_field` | [source](paper/multifractal.tex) |
| `l.concentration.rare.intervals` | `Paper.l_concentration_rare_intervals` | `SubdiffusiveProcess.Paper.l_concentration_rare_intervals` | [source](paper/multifractal.tex) |
| `l.circ.norm.dominates` | `Paper.l_circ_norm_dominates` | `SubdiffusiveProcess.Paper.l_circ_norm_dominates` | [source](paper/multifractal.tex) |
| `l.Wsp.vs.Bspp` | `Paper.l_Wsp_vs_Bspp` | `SubdiffusiveProcess.Paper.l_Wsp_vs_Bspp` | [source](paper/multifractal.tex) |

## Audit exports

For some passages of the paper, the declaration cited in the table above is narrower than the paper's statement
or does not state it in the form in which the paper does. For each of the passages below the library also
contains declarations that state the passage as the paper does; they are in
[`SubdiffusiveProcess/Paper/Foundations/AuditExports/`](SubdiffusiveProcess/Paper/Foundations/AuditExports).
They are ordinary theorems of the library, proved from the same development as the rest. The axiom report of
every declaration in the table below that is given by its full name lists exactly `propext`,
`Classical.choice` and `Quot.sound`; `scripts/check_axioms.py` checks all of them (see
[`README.md`](README.md#building)). The last column says what, if anything, of the paper's statement is not
part of the declarations. Where the table above cites a declaration for the same label, the row below is the one
that states the label as the paper does.

| Paper label | What the paper states | Lean principal(s) | File | What stays outside Lean |
| --- | --- | --- | --- | --- |
| `e.def.bfG.mhq` | the baseline score `G_{k,z}(s)` is the sum of a response term, a block term, an anchor term and a gradient tail, with suprema over empty index sets equal to zero | `SubdiffusiveProcess.AuditExports.baseline_native_finite`, `SubdiffusiveProcess.AuditExports.baseline_scores_finite`, `SubdiffusiveProcess.AuditExports.baseline_relabelled_finite`; the four terms are `baselineResponseTerm`, `baselineBlockTerm`, `baselineAnchorTerm`, `baselineGradientTerm` and their sum is `baselineExtendedScore` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/BaselineFiniteness.lean` | nothing |
| `l.sum.the.errors` | the average over `k = n, …, m` of the scores `G_{k,z}(s)` is at most `C s^{-7/2} δ` plus a `Γ₂` fluctuation of order `C s^{-7/2} δ |log δ|^{1/2} (m-n+1)^{-1/2}` | `SubdiffusiveProcess.AuditExports.baseline_native_finite`, `SubdiffusiveProcess.AuditExports.baseline_scores_finite` (the four terms and their sum are almost surely finite, with `L^q` norm at most `C δ^{1/2}`) | `SubdiffusiveProcess/Paper/Foundations/AuditExports/BaselineFiniteness.lean` | nothing; this export states only the finiteness of the terms, and the averaged bound itself is the declaration in the main table |
| `mfd:lem-cell-ellipticity` | on every cell `z + 3^{-k} □₀` inside a bounded cube `Q`, the `L^p` norm of `Λ_{s,q} + λ_{s,q}^{-1}` of the cutoff coefficient is at most `C exp(C(p+p²)δ²k)`, uniformly in `0 ≤ k ≤ N` | `SubdiffusiveProcess.AuditExports.cell_ellipticity_uniform`, with the conditional form `SubdiffusiveProcess.AuditExports.cell_ellipticity_moment_uniform` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/S11Ellipticity.lean` | nothing |
| `mfd:lem-extremes` | for `δ ≤ c_d/p`, the `L^p` norm of `D_N = 3^{-N} ‖∇ log A_N‖_{L^∞(Q)}` is at most `C_p (1+N)^{1/2}` and that of `‖A_N‖_{L^∞(Q)} + ‖A_N^{-1}‖_{L^∞(Q)}` is at most `C_p e^{(C_d δ + C_p δ²) N}` | `SubdiffusiveProcess.AuditExports.cutoff_extrema_moments` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/S10Extrema.lean` | nothing |
| `mfd:thm-fold` | folding a continuous positive coefficient on a cube by reflections through its centre multiplies the squared multiscale error `E_{s,∞,2}²` by at most `1 + 3d/(3^{1-2s} - 1)`, for every scalar `a₀ > 0` and `s ∈ (0, 1/2)` | `SubdiffusiveProcess.AuditExports.foldingComparison`, `SubdiffusiveProcess.AuditExports.normalizedPotential_coefficient` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/S07.lean` | nothing |
| `mfd:prop-folded-iteration` | for the folded coefficient, the energy decay holds above the minimal scale defined at the tightened exponent `γ_* = 1 - (1-γ)/K`, and this scale has the tail `P[𝓛 > h] ≤ C exp(-(1-γ)² (h-C)_+ / (C K² δ² |log δ|))`, uniformly in `L`, `m` and the centre `z` | `SubdiffusiveProcess.AuditExports.folded_iteration_minimal_scale_tail` (the tail), `SubdiffusiveProcess.AuditExports.folded_iteration_energy_and_tail` (the energy inequality and the tail with the same constants and the same scale) | `SubdiffusiveProcess/Paper/Foundations/AuditExports/FoldedIterationTail.lean` | the energy inequality is formalized for a fold with at least one reflected coordinate direction; the unfolded case (the fold is the identity) is not part of its formal statement. The tail bound has no fold hypothesis |
| `mfd:cor-neumann-source` | for the Neumann problem with mean-zero bounded source, the solution has a Hölder bound and a Morrey-type energy bound with random constants bounded in every finite `L^p`, with one constant for all sources, uniformly over the infrared truncations, for the zero-infrared coefficient and for its translates, and for the maximum over finitely many translates | `SubdiffusiveProcess.AuditExports.neumann_source_infrared_family` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/InfraredFamilyNeumann.lean`, with `InfraredFamilyEnvelope.lean`, `InfraredFamilyRegularity.lean`, `InfraredFamilyTransport.lean` and `InfraredFamilyMicroscopic.lean` in the same directory | nothing |
| `mfd:lem-15` | replacing the field `γ_{-j}` by an independent copy changes the finite-volume energy by at most `C_p δ 3^{-bj/8}` in `L^p`, for `0 ≤ j ≤ N` | `SubdiffusiveProcess.AuditExports.resamplingEstimate` (with the Poincaré inequalities `cubeKilledPoincare`, `cubeMeanZeroPoincare`, `gridKilledPoincare`, `gridMeanZeroPoincare`) | `SubdiffusiveProcess/Paper/Foundations/AuditExports/S07.lean` | nothing |
| `mfd:prop-16` | conditioning on the fields with indices `|j| ≤ ℓ` approximates the finite-volume energy in `L^p` with error `C_p δ 3^{-bℓ/8}` (Dirichlet and source clauses), and approximates the Neumann energy on the unit cube with error `C_p δ^{1/2} 3^{-bℓ/256}` | `SubdiffusiveProcess.AuditExports.conditioningEstimate` (Dirichlet and source clauses), `SubdiffusiveProcess.AuditExports.neumann_conditioning` (Neumann clause) | `SubdiffusiveProcess/Paper/Foundations/AuditExports/S07.lean` and `SubdiffusiveProcess/Paper/Foundations/AuditExports/NeumannResponseMoment.lean` | nothing |
| `mfd:lem-cutoffs` | the harmonic interpolant of a smooth cutoff is continuous, takes values in `[0,1]` and is bounded in energy, Morrey constant and Hölder norm, and the interpolant of a collar profile of width `r` has energy at most `C (K_N + 3^{-ηN} ‖A_N‖_{L^∞}) r^{-1-η}` | `SubdiffusiveProcess.AuditExports.cutoffClauses` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/S08.lean` | the collar clause is formalized for widths that are triadic fractions of the cube side, not for every `r > 0`, and its bound is a combined random majorant with every finite moment, which is not identified with the explicit expression `K_N + 3^{-ηN} ‖A_N‖_{L^∞}` |
| `mfd:lem-borel-weights` | for a bounded Borel weight `g` the form `∫ e^g dΓ_E` is a regular strongly local Dirichlet form, and deleting any one field `γ_{-j}`, `j ≥ 0`, leaves a form measurable with respect to the remaining fields | `SubdiffusiveProcess.AuditExports.borelWeights_deletion`, `SubdiffusiveProcess.AuditExports.deletion_packageClosure` (the deletion clause) | `SubdiffusiveProcess/Paper/Foundations/AuditExports/S09Deletion.lean`, with `S09InfraredVersion.lean` and `S09DeletedCoefficients.lean`; and `SubdiffusiveProcess/Paper/Foundations/AuditExports/S06Deletion.lean` | nothing; the bounded-weight clause is not restated in these exports and is the declaration in the main table |
| `mfd:prop-boundary` | the minimal energies with given boundary values on a cell converge, and the limit is the boundary minimum of the limiting Dirichlet energy over the padded cube | `SubdiffusiveProcess.AuditExports.boundary_response_identity`, `SubdiffusiveProcess.AuditExports.boundary_response_identity_of_infrared` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/BoundaryIdentity.lean` | nothing; the clauses on boundary values, absence of energy on the faces and harmonicity are not restated in this export and are the declaration in the main table |
| `mfd:lem-witness` | for the limiting arrays defining the good event `G_E(q)` and every `A < ∞`, the failure of `G_E(q)` is covered, up to a null set, by events `W_{q,h}` measurable with respect to the fields with indices between `n-h` and `n+2h`, with `P(W_{q,h}) ≤ e^{-Ah}`; the same holds for one additional scalar or matrix condition | `SubdiffusiveProcess.AuditExports.limiting_good_cell_witness_of_limits` (the arrays are given, with their convergence in measure as the hypothesis), `SubdiffusiveProcess.AuditExports.limiting_good_cell_witness` (such arrays exist), `SubdiffusiveProcess.AuditExports.additional_condition_witness` (the additional condition, with the moment order chosen large depending on `A` and the exponent, as in the paper's proof) | `SubdiffusiveProcess/Paper/Foundations/AuditExports/LimitingGoodCellWitness.lean` and `SubdiffusiveProcess/Paper/Foundations/AuditExports/AdditionalConditionWitness.lean` | nothing |
| `mfd:lem-rare-tests` | for a countable family of `[0,1]`-valued observables whose probabilities of exceeding any `ε > 0` tend to zero uniformly in the family, and which are well approximated in `L^p` by functions of the fields in a window of radius `H`, the event that an observable exceeds `1/2` is covered, up to a null set, by events with `P ≤ e^{-Bh}` measurable with respect to windows of radius at most `C h`; the initial window `H_0` depends only on `a`, `p`, `C_*`, `B` | `SubdiffusiveProcess.AuditExports.rare_tests_family` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/RareTestsFamily.lean` | nothing |
| `mfd:prop-as-dirichlet` | for a cube `Q` of triadic side and a smooth boundary datum `g`, `Λ_{N,Q}(g) → Λ_{E,Q}(g)` almost surely along the full sequence of integers | `SubdiffusiveProcess.AuditExports.boundary_response_identity`, `SubdiffusiveProcess.AuditExports.boundary_response_identity_of_infrared` (scalar convergence of the minimal energies for every cube of a countable family, on one common event) | `SubdiffusiveProcess/Paper/Foundations/AuditExports/BoundaryIdentity.lean` | nothing |
| `mfd:prop-as-response-bank` | for the four response quantities on a cube of triadic side, computed for `A_N` or for `A_N^0`, convergence in probability holds with summable error probabilities, with the thresholds independent of the tolerance, uniformly over deterministic translations of the cube for `A_N^0`, and simultaneously along the full sequence for a countable family | `SubdiffusiveProcess.AuditExports.response_bank_fixed_cube_translations`, `SubdiffusiveProcess.AuditExports.response_bank_fixed_cube_translations_of_infrared`, `SubdiffusiveProcess.AuditExports.cutoff_coefficient_zero_infrared_shift` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/ResponseBankTranslations.lean` | nothing |
| `mfd:prop-as-forms` | almost surely, for every cube, the resolvent operators converge in operator norm, the forms converge in the Mosco sense, and the resolvents applied to continuous data converge uniformly with a common Hölder bound | `SubdiffusiveProcess.AuditExports.boundary_response_identity`, `SubdiffusiveProcess.AuditExports.boundary_response_identity_of_infrared` (the operator-norm convergence along the full sequence, with the limit form regular, strongly local and with the padded cube as a core) | `SubdiffusiveProcess/Paper/Foundations/AuditExports/BoundaryIdentity.lean` | nothing; the Mosco convergence, the uniform convergence of the resolvents and their common Hölder bound are not restated in this export and are the declaration in the main table |
| `lim:thm-nongaussian` | almost surely, for every starting point and every positive time, the transition law of the limit process is absolutely continuous with respect to the reversible measure and singular with respect to Lebesgue measure and every Gaussian law, with the bound `C_U t^{-d} μ` before the exit time of a bounded open set `U`, and the joint laws at finitely many times and the path laws on intervals are singular with respect to Gaussian laws | `SubdiffusiveProcess.AuditExports.theoremA_nongaussian` | `SubdiffusiveProcess/Paper/Foundations/AuditExports/S04.lean` | nothing |
