# Paper–Lean correspondence

The included paper is pinned to `c79e174c2d28026ed7b1cec31ab86a6f574164a2`.

Process laws are characterized by their weak elliptic resolvents and their
finite-dimensional distributions under the associated semigroups. This is
the paper's defining analytic construction of `X`, `X^(L)` and the common-scale
cutoff laws. The equivalent SDE description is justified in the paper,
outside the formally verified surface.

`KN 0` is clock-normalized. The physical rescaling uses the `ahom_0` factor
in `SubdiffusiveProcess.physicalTimeFactor`
([PhysicalTimeFactor.lean](SubdiffusiveProcess/Main/PhysicalTimeFactor.lean)).
It must not be identified directly with the unnormalized SDE law of `X`.
The physical energy is `∫ a |∇u|² dx` on `L²(a dx)`; the rescaled energy
and speed measure are the pair specified in the paper.

Build, main-theorem axiom reports and comparator verification are pending
for this release candidate. The index below records source correspondence;
it does not certify every numbered statement or every SDE assertion.

| Paper passage | Public Lean reference | Correspondence treatment |
| --- | --- | --- |
| `t.A`; precise `t.scaling.limit` | `Paper.t_A`; `Paper.thm_A`; `SubdiffusiveProcess.process_convergence` | Scaling limit for analytically characterized laws; release build, axiom and comparator verification pending. |
| `s.fixed.coefficient`, analytic construction; `e.fixed.clock.form` | `Paper.finiteDimensional_cutoff` and its semigroup/path-kernel results; `Paper.in_crossing`; physical attachment results | Analytic process construction/characterization. Physical energy and speed measure differ from the rescaled pair. |
| `s.fixed.coefficient`, SDE interpretation; `e.fixed.clock.sde` | No completed Brownian-driver theorem | **Paper-only; not formally verified.** |
| Former `l.fixed.clock.diffusion` | Historical `l_fixed_clock_diffusion`, depending on `classical_fot_5_5_5`; neither exported | **Superseded, unproved, unused by the main roots; excluded from the certified release surface.** |
| Former `mfd:lem-killed-feller` | Historical `mfd_lem_killed_feller`; not exported | **Superseded and excluded from the certified release surface.** |

Historical declarations are not evidence that the SDE interpretation is
formally verified.

The source links identify the statements in the included paper, including
their explicit disorder quantifiers and probability-one clauses.

| Paper label or passage | Lean declaration | Module | Paper source |
| --- | --- | --- | --- |
| `t.A` | `Paper.t_A` | `SubdiffusiveProcess.Paper.t_A` | [statement](paper/multifractal.tex#L168) |
| `t.B` | `Paper.t_B` | `SubdiffusiveProcess.Paper.t_B` | [statement](paper/multifractal.tex#L233) |
| `t.C` | `Paper.t_C` | `SubdiffusiveProcess.Paper.t_C` | [statement](paper/multifractal.tex#L270) |
| `l.sharp.compare.J` | `Paper.l_sharp_compare_J_convex` | `SubdiffusiveProcess.Paper.l_sharp_compare_J_convex` | [statement](paper/multifractal.tex#L840) |
| §2, Coarse-grained ellipticity constants | `Paper.d_coarse_grained_ellipticity` | `SubdiffusiveProcess.Paper.d_coarse_grained_ellipticity` | [passage](paper/multifractal.tex) |
| `d.mathcal.E` | `Paper.d_mathcal_E` | `SubdiffusiveProcess.Paper.d_mathcal_E` | [statement](paper/multifractal.tex#L1082) |
| `l.lambdas.stability` | `Paper.l_lambdas_stability` | `SubdiffusiveProcess.Paper.l_lambdas_stability` | [statement](paper/multifractal.tex#L1253) |
| `p.coarse.grained.poincare` | `Paper.p_coarse_grained_poincare` | `SubdiffusiveProcess.Paper.p_coarse_grained_poincare` | [statement](paper/multifractal.tex#L1280) |
| `p.coarse.grained.caccioppoli` | `Paper.p_coarse_grained_caccioppoli` | `SubdiffusiveProcess.Paper.p_coarse_grained_caccioppoli` | [statement](paper/multifractal.tex#L1352) |
| `l.sensitivity.general` | `Paper.l_sensitivity_general_convex` | `SubdiffusiveProcess.Paper.l_sensitivity_general_convex` | [statement](paper/multifractal.tex#L1393) |
| `l.J.sensitivity` | `Paper.l_J_sensitivity_convex` | `SubdiffusiveProcess.Paper.l_J_sensitivity_convex` | [statement](paper/multifractal.tex#L1455) |
| `l.coarse.graining.RHS` | `Paper.l_coarse_graining_RHS` | `SubdiffusiveProcess.Paper.l_coarse_graining_RHS` | [statement](paper/multifractal.tex#L1578) |
| `l.coarse.grained.Caccioppoli.RHS.ASD` | `Paper.l_coarse_grained_Caccioppoli_RHS_ASD` | `SubdiffusiveProcess.Paper.l_coarse_grained_Caccioppoli_RHS_ASD` | [statement](paper/multifractal.tex#L1646) |
| `p.general.coarse.graining.ASD` | `Paper.p_general_coarse_graining_ASD` | `SubdiffusiveProcess.Paper.p_general_coarse_graining_ASD` | [statement](paper/multifractal.tex#L1705) |
| `l.sensitivity.for.cutoffs` | `Paper.l_sensitivity_for_cutoffs` | `SubdiffusiveProcess.Paper.l_sensitivity_for_cutoffs` | [statement](paper/multifractal.tex#L1792) |
| `l.aL.negative.Besov` | `Paper.l_aL_negative_Besov` | `SubdiffusiveProcess.Paper.l_aL_negative_Besov` | [statement](paper/multifractal.tex#L1921) |
| `lemma:infrared.approx.cutoffs` | `Paper.lemma_infrared_approx_cutoffs_convex` | `SubdiffusiveProcess.Paper.lemma_infrared_approx_cutoffs_convex` | [statement](paper/multifractal.tex#L2378) |
| `l.annealed.matrix.bounds` | `Paper.l_annealed_matrix_bounds_convex` | `SubdiffusiveProcess.Paper.l_annealed_matrix_bounds_convex` | [statement](paper/multifractal.tex#L2463) |
| `p.special.two.d.exact.formula` | `Paper.p_special_two_d_exact_formula` | `SubdiffusiveProcess.Paper.p_special_two_d_exact_formula` | [statement](paper/multifractal.tex#L2637) |
| `lemma.crude.J.bound` | `Paper.lemma_crude_J_bound_convex` | `SubdiffusiveProcess.Paper.lemma_crude_J_bound_convex` | [statement](paper/multifractal.tex#L2653) |
| `p.coarse.grained.bound` | `Paper.p_coarse_grained_bound` | `SubdiffusiveProcess.Paper.p_coarse_grained_bound` | [statement](paper/multifractal.tex#L2691) |
| `d.mathcalS.def` | `Paper.d_mathcalS_def` | `SubdiffusiveProcess.Paper.d_mathcalS_def` | [statement](paper/multifractal.tex#L2741) |
| `d.bLm` | `Paper.d_bLm` | `SubdiffusiveProcess.Paper.d_bLm` | [statement](paper/multifractal.tex#L2779) |
| `l.ellipticity.bound` | `Paper.l_ellipticity_bound` | `SubdiffusiveProcess.Paper.l_ellipticity_bound` | [statement](paper/multifractal.tex#L2798) |
| `l.multiscale.response.large.cubes` | `Paper.l_multiscale_response_large_cubes` | `SubdiffusiveProcess.Paper.l_multiscale_response_large_cubes` | [statement](paper/multifractal.tex#L3024) |
| `l.J.bound.by.Besov` | `Paper.l_J_bound_by_Besov` | `SubdiffusiveProcess.Paper.l_J_bound_by_Besov` | [statement](paper/multifractal.tex#L3103) |
| `l.Besov.norms` | `Paper.l_Besov_norms` | `SubdiffusiveProcess.Paper.l_Besov_norms` | [statement](paper/multifractal.tex#L3177) |
| `l.var.bounds` | `Paper.l_var_bounds` | `SubdiffusiveProcess.Paper.l_var_bounds` | [statement](paper/multifractal.tex#L3362) |
| `p.combine.under.S` | `Paper.p_combine_under_S` | `SubdiffusiveProcess.Paper.p_combine_under_S` | [statement](paper/multifractal.tex#L3485) |
| `p.homogenization.step` | `Paper.p_homogenization_step` | `SubdiffusiveProcess.Paper.p_homogenization_step` | [statement](paper/multifractal.tex#L3768) |
| `t.renormalized.diffusivities` | `Paper.t_renormalized_diffusivities` | `SubdiffusiveProcess.Paper.t_renormalized_diffusivities` | [statement](paper/multifractal.tex#L4128) |
| `p.sharp.asymptotic` | `Paper.p_sharp_asymptotic` | `SubdiffusiveProcess.Paper.p_sharp_asymptotic` | [statement](paper/multifractal.tex#L4161) |
| `l.laplacian.corrector.energy` | `Paper.l_laplacian_corrector_energy` | `SubdiffusiveProcess.Paper.l_laplacian_corrector_energy` | [statement](paper/multifractal.tex#L4170) |
| `l.one.step.upper` | `Paper.l_one_step_upper` | `SubdiffusiveProcess.Paper.l_one_step_upper` | [statement](paper/multifractal.tex#L4287) |
| `l.one.step.lower` | `Paper.l_one_step_lower` | `SubdiffusiveProcess.Paper.l_one_step_lower` | [statement](paper/multifractal.tex#L4554) |
| `p.homogenized.coefficient.strict.decay` | `Paper.p_homogenized_coefficient_strict_decay` | `SubdiffusiveProcess.Paper.p_homogenized_coefficient_strict_decay` | [statement](paper/multifractal.tex#L4765) |
| `p.homogenized.coefficient.reciprocal.lower` | `Paper.p_homogenized_coefficient_reciprocal_lower` | `SubdiffusiveProcess.Paper.p_homogenized_coefficient_reciprocal_lower` | [statement](paper/multifractal.tex#L4916) |
| `p.Holder.regularity` | `Paper.p_Holder_regularity` | `SubdiffusiveProcess.Paper.p_Holder_regularity` | [statement](paper/multifractal.tex#L5055) |
| `d.good.events` | `Paper.d_good_events` | `SubdiffusiveProcess.Paper.d_good_events` | [statement](paper/multifractal.tex#L5155) |
| `p.good.scale.mathcal.E` | `Paper.p_good_scale_mathcal_E` | `SubdiffusiveProcess.Paper.p_good_scale_mathcal_E` | [statement](paper/multifractal.tex#L5218) |
| `p.density.of.good.scales` | `Paper.p_density_of_good_scales` | `SubdiffusiveProcess.Paper.p_density_of_good_scales` | [statement](paper/multifractal.tex#L5265) |
| `l.bad.scales.for.nabla.gj` | `Paper.l_bad_scales_for_nabla_gj` | `SubdiffusiveProcess.Paper.l_bad_scales_for_nabla_gj` | [statement](paper/multifractal.tex#L5510) |
| `l.exp.goodscales` | `Paper.l_exp_goodscales` | `SubdiffusiveProcess.Paper.l_exp_goodscales` | [statement](paper/multifractal.tex#L5533) |
| `l.discounted.J.local` | `Paper.l_discounted_J_local` | `SubdiffusiveProcess.Paper.l_discounted_J_local` | [statement](paper/multifractal.tex#L5559) |
| `l.harmonic.approximation.good.scales.GMC` | `Paper.l_harmonic_approximation_good_scales_GMC` | `SubdiffusiveProcess.Paper.l_harmonic_approximation_good_scales_GMC` | [statement](paper/multifractal.tex#L5798) |
| `l.excess.decay.good.scales.GMC` | `Paper.l_excess_decay_good_scales_GMC` | `SubdiffusiveProcess.Paper.l_excess_decay_good_scales_GMC` | [statement](paper/multifractal.tex#L5940) |
| `l.iteration.lemma.GMC` | `Paper.l_iteration_lemma_GMC` | `SubdiffusiveProcess.Paper.l_iteration_lemma_GMC` | [statement](paper/multifractal.tex#L6077) |
| `l.sum.the.errors` | `Paper.l_sum_the_errors` | `SubdiffusiveProcess.Paper.l_sum_the_errors` | [statement](paper/multifractal.tex#L6219) |
| `l.min.scale.good.scale` | `Paper.l_min_scale_good_scale` | `SubdiffusiveProcess.Paper.l_min_scale_good_scale` | [statement](paper/multifractal.tex#L6532) |
| `l.cutoff.regularity.response` | `Paper.l_cutoff_regularity_response` | `SubdiffusiveProcess.Paper.l_cutoff_regularity_response` | [statement](paper/multifractal.tex#L7086) |
| `p.cutoff.regularity.good.scales` | `Paper.p_cutoff_regularity_good_scales` | `SubdiffusiveProcess.Paper.p_cutoff_regularity_good_scales` | [statement](paper/multifractal.tex#L7123) |
| `l.cutoff.regularity.good.scale.estimates` | `Paper.cutoff_good_scale_estimates` | `SubdiffusiveProcess.Paper.cutoff_good_scale_estimates` | [statement](paper/multifractal.tex#L7249) |
| `p.cutoff.Holder.regularity` | `Paper.p_cutoff_Holder_regularity` | `SubdiffusiveProcess.Paper.p_cutoff_Holder_regularity` | [statement](paper/multifractal.tex#L7263) |
| `p.cutoff.Holder.bounded.multiplier` | `Paper.p_cutoff_Holder_bounded_multiplier` | `SubdiffusiveProcess.Paper.p_cutoff_Holder_bounded_multiplier` | [statement](paper/multifractal.tex#L7325) |
| `t.cutoff.Dirichlet.homogenization` | `Paper.t_cutoff_Dirichlet_homogenization` | `SubdiffusiveProcess.Paper.t_cutoff_Dirichlet_homogenization` | [statement](paper/multifractal.tex#L7378) |
| `t.fixed.cutoff.Dirichlet.algebraic` | `Paper.t_fixed_cutoff_Dirichlet_algebraic` | `SubdiffusiveProcess.Paper.t_fixed_cutoff_Dirichlet_algebraic` | [statement](paper/multifractal.tex#L7532) |
| `l.finite.cutoff.coefficient.convergence` | `Paper.l_finite_cutoff_coefficient_convergence` | `SubdiffusiveProcess.Paper.l_finite_cutoff_coefficient_convergence` | [statement](paper/multifractal.tex#L7611) |
| `t.large.scale.Holder.multifractal` | `Paper.t_large_scale_Holder_multifractal` | `SubdiffusiveProcess.Paper.t_large_scale_Holder_multifractal` | [statement](paper/multifractal.tex#L7702) |
| `mfd:lem-infrared` | `Paper.mfd_lem_infrared` | `SubdiffusiveProcess.Paper.mfd_lem_infrared` | [statement](paper/multifractal.tex#L7865) |
| `mfd:lem-cell-ellipticity` | `Paper.lem_cell_ellipticity` | `SubdiffusiveProcess.Paper.lem_cell_ellipticity` | [statement](paper/multifractal.tex#L7909) |
| `mfd:lem-coercivity` | `Paper.lem_coercivity` | `SubdiffusiveProcess.Paper.lem_coercivity` | [statement](paper/multifractal.tex#L7927) |
| `mfd:lem-extension` | `Paper.lem_extension` | `SubdiffusiveProcess.Paper.lem_extension` | [statement](paper/multifractal.tex#L7942) |
| `mfd:lem-primitive` | `Paper.lem_primitive` | `SubdiffusiveProcess.Paper.lem_primitive` | [statement](paper/multifractal.tex#L7979) |
| `mfd:lem-extremes` | `Paper.lem_extremes` | `SubdiffusiveProcess.Paper.lem_extremes` | [statement](paper/multifractal.tex#L7992) |
| `mfd:prop-growth` | `Paper.prop_growth` | `SubdiffusiveProcess.Paper.prop_growth` | [statement](paper/multifractal.tex#L8017) |
| `mfd:lem-neumann-error` | `Paper.mfd_lem_neumann_error` | `SubdiffusiveProcess.Paper.mfd_lem_neumann_error` | [statement](paper/multifractal.tex#L8126) |
| `mfd:thm-fold` | `Paper.mfd_thm_fold` | `SubdiffusiveProcess.Paper.mfd_thm_fold` | [statement](paper/multifractal.tex#L8163) |
| `mfd:prop-folded-iteration` | `Paper.prop_folded_iteration` | `SubdiffusiveProcess.Paper.prop_folded_iteration` | [statement](paper/multifractal.tex#L8176) |
| `mfd:cor-neumann-source` | `Paper.mfd_cor_neumann_source` | `SubdiffusiveProcess.Paper.mfd_cor_neumann_source` | [statement](paper/multifractal.tex#L8190) |
| `mfd:cor-14` | `Paper.cor_14` | `SubdiffusiveProcess.Paper.cor_14` | [statement](paper/multifractal.tex#L8240) |
| `mfd:lem-strips` | `Paper.lem_strips` | `SubdiffusiveProcess.Paper.lem_strips` | [statement](paper/multifractal.tex#L8274) |
| `mfd:lem-15` | `Paper.mfd_lem_15` | `SubdiffusiveProcess.Paper.mfd_lem_15` | [statement](paper/multifractal.tex#L8307) |
| `mfd:lem-resampling-sum` | `Paper.lem_resampling_sum` | `SubdiffusiveProcess.Paper.lem_resampling_sum` | [statement](paper/multifractal.tex#L8348) |
| `mfd:prop-16` | `Paper.mfd_prop_16` | `SubdiffusiveProcess.Paper.mfd_prop_16` | [statement](paper/multifractal.tex#L8363) |
| `mfd:prop-response-compact` | `Paper.mfd_prop_response_compact` | `SubdiffusiveProcess.Paper.mfd_prop_response_compact` | [statement](paper/multifractal.tex#L8388) |
| `mfd:prop-killed-inverse` | `Paper.prop_killed_inverse` | `SubdiffusiveProcess.Paper.prop_killed_inverse` | [statement](paper/multifractal.tex#L8425) |
| `mfd:lem-response-reciprocal` | `Paper.lem_response_reciprocal` | `SubdiffusiveProcess.Paper.lem_response_reciprocal` | [statement](paper/multifractal.tex#L8478) |
| `mfd:lem-19` | `Paper.lem_19` | `SubdiffusiveProcess.Paper.lem_19` | [statement](paper/multifractal.tex#L8500) |
| `mfd:lem-cutoffs` | `Paper.mfd_lem_cutoffs` | `SubdiffusiveProcess.Paper.mfd_lem_cutoffs` | [statement](paper/multifractal.tex#L8533) |
| `mfd:prop-regularity` | `Paper.mfd_prop_regularity` | `SubdiffusiveProcess.Paper.mfd_prop_regularity` | [statement](paper/multifractal.tex#L8557) |
| `mfd:prop-locality` | `Paper.prop_locality` | `SubdiffusiveProcess.Paper.prop_locality` | [statement](paper/multifractal.tex#L8576) |
| `mfd:prop-killed-consistency` | `Paper.mfd_prop_killed_consistency` | `SubdiffusiveProcess.Paper.mfd_prop_killed_consistency` | [statement](paper/multifractal.tex#L8597) |
| `mfd:lem-sincos` | `Paper.lem_sincos` | `SubdiffusiveProcess.Paper.lem_sincos` | [statement](paper/multifractal.tex#L8610) |
| `mfd:prop-21` | `Paper.mfd_prop_21` | `SubdiffusiveProcess.Paper.mfd_prop_21` | [statement](paper/multifractal.tex#L8623) |
| `mfd:lem-borel-weights` | `Paper.mfd_lem_borel_weights` | `SubdiffusiveProcess.Paper.mfd_lem_borel_weights` | [statement](paper/multifractal.tex#L8647) |
| `mfd:cor-energy-measures` | `Paper.cor_energy_measures` | `SubdiffusiveProcess.Paper.cor_energy_measures` | [statement](paper/multifractal.tex#L8662) |
| `mfd:lem-truncation` | `Paper.lem_truncation` | `SubdiffusiveProcess.Paper.lem_truncation` | [statement](paper/multifractal.tex#L8685) |
| `mfd:prop-boundary` | `Paper.mfd_prop_boundary` | `SubdiffusiveProcess.Paper.mfd_prop_boundary` | [statement](paper/multifractal.tex#L8696) |
| `mfd:prop-gluing` | `Paper.mfd_prop_gluing` | `SubdiffusiveProcess.Paper.mfd_prop_gluing` | [statement](paper/multifractal.tex#L8729) |
| `mfd:lem-skeleton` | `Paper.lem_skeleton` | `SubdiffusiveProcess.Paper.lem_skeleton` | [statement](paper/multifractal.tex#L8754) |
| `mfd:in-deterministic` | `Paper.in_deterministic` | `SubdiffusiveProcess.Paper.in_deterministic` | [statement](paper/multifractal.tex#L8795) |
| `mfd:lem-prefix-limit` | `Paper.lem_prefix_limit` | `SubdiffusiveProcess.Paper.lem_prefix_limit` | [statement](paper/multifractal.tex#L8809) |
| `mfd:lem-band` | `Paper.mfd_lem_band` | `SubdiffusiveProcess.Paper.mfd_lem_band` | [statement](paper/multifractal.tex#L8836) |
| `mfd:in-prefix` | `Paper.mfd_in_prefix` | `SubdiffusiveProcess.Paper.mfd_in_prefix` | [statement](paper/multifractal.tex#L8863) |
| `mfd:lem-witness` | `Paper.lem_witness` | `SubdiffusiveProcess.Paper.lem_witness` | [statement](paper/multifractal.tex#L8874) |
| `mfd:prop-allchain` | `Paper.prop_allchain` | `SubdiffusiveProcess.Paper.prop_allchain` | [statement](paper/multifractal.tex#L8892) |
| `mfd:lem-goodext` | `Paper.mfd_lem_goodext_uniform` | `SubdiffusiveProcess.Paper.mfd_lem_goodext_uniform` | [statement](paper/multifractal.tex#L8952) |
| `mfd:prop-density` | `Paper.mfd_prop_density` | `SubdiffusiveProcess.Paper.mfd_prop_density` | [statement](paper/multifractal.tex#L8974) |
| `mfd:thm-C0` | `Paper.mfd_thm_C0` | `SubdiffusiveProcess.Paper.mfd_thm_C0` | [statement](paper/multifractal.tex#L9008) |
| `mfd:lem-endpoints` | `Paper.mfd_lem_endpoints` | `SubdiffusiveProcess.Paper.mfd_lem_endpoints` | [statement](paper/multifractal.tex#L9034) |
| `mfd:lem-diff` | `Paper.lem_diff` | `SubdiffusiveProcess.Paper.lem_diff` | [statement](paper/multifractal.tex#L9050) |
| `mfd:lem-relvar` | `Paper.lem_relvar` | `SubdiffusiveProcess.Paper.lem_relvar` | [statement](paper/multifractal.tex#L9080) |
| `mfd:prop-conc` | `Paper.prop_conc` | `SubdiffusiveProcess.Paper.prop_conc` | [statement](paper/multifractal.tex#L9123) |
| `mfd:cor-32` | `Paper.cor_32` | `SubdiffusiveProcess.Paper.cor_32` | [statement](paper/multifractal.tex#L9168) |
| `mfd:lem-affine` | `Paper.lem_affine` | `SubdiffusiveProcess.Paper.lem_affine` | [statement](paper/multifractal.tex#L9183) |
| `mfd:lem-shifts` | `Paper.lem_shifts` | `SubdiffusiveProcess.Paper.lem_shifts` | [statement](paper/multifractal.tex#L9238) |
| `mfd:lem-mass` | `Paper.lem_mass` | `SubdiffusiveProcess.Paper.lem_mass` | [statement](paper/multifractal.tex#L9252) |
| `mfd:lem-replace` | `Paper.lem_replace` | `SubdiffusiveProcess.Paper.lem_replace` | [statement](paper/multifractal.tex#L9267) |
| `mfd:thm-prop` | `Paper.mfd_thm_prop` | `SubdiffusiveProcess.Paper.mfd_thm_prop` | [statement](paper/multifractal.tex#L9282) |
| `mfd:thm-eta` | `Paper.thm_eta` | `SubdiffusiveProcess.Paper.thm_eta` | [statement](paper/multifractal.tex#L9324) |
| `mfd:thm-c1` | `Paper.mfd_thm_c1` | `SubdiffusiveProcess.Paper.mfd_thm_c1` | [statement](paper/multifractal.tex#L9380) |
| `mfd:lem-chaos-moments` | `Paper.lem_chaos_moments` | `SubdiffusiveProcess.Paper.lem_chaos_moments` | [statement](paper/multifractal.tex#L9458) |
| `mfd:prop-chaos-growth` | `Paper.prop_chaos_growth` | `SubdiffusiveProcess.Paper.prop_chaos_growth` | [statement](paper/multifractal.tex#L9478) |
| `mfd:lem-varying-trace` | `Paper.lem_varying_trace` | `SubdiffusiveProcess.Paper.lem_varying_trace` | [statement](paper/multifractal.tex#L9512) |
| `mfd:prop-speed-resolvent` | `Paper.prop_speed_resolvent` | `SubdiffusiveProcess.Paper.prop_speed_resolvent` | [statement](paper/multifractal.tex#L9539) |
| `mfd:prop-uniform-resolvent` | `Paper.mfd_prop_uniform_resolvent` | `SubdiffusiveProcess.Paper.mfd_prop_uniform_resolvent` | [statement](paper/multifractal.tex#L9561) |
| `tight:lem-static` | `Paper.tight_lem_static` | `SubdiffusiveProcess.Paper.tight_lem_static` | [statement](paper/multifractal.tex#L9655) |
| `tight:lem-subharmonic` | `Paper.tight_lem_subharmonic` | `SubdiffusiveProcess.Paper.tight_lem_subharmonic` | [statement](paper/multifractal.tex#L9742) |
| `tight:prop-tightness` | `Paper.tight_prop_tightness` | `SubdiffusiveProcess.Paper.tight_prop_tightness` | [statement](paper/multifractal.tex#L9819) |
| `mfd:prop-quenched-convergence` | `Paper.mfd_prop_quenched_convergence` | `SubdiffusiveProcess.Paper.mfd_prop_quenched_convergence` | [statement](paper/multifractal.tex#L9928) |
| `mfd:prop-limit-properties` | `Paper.prop_limit_properties` | `SubdiffusiveProcess.Paper.prop_limit_properties` | [statement](paper/multifractal.tex#L9970) |
| `mfd:lem-killing` | `Paper.mfd_lem_killing` | `SubdiffusiveProcess.Paper.mfd_lem_killing` | [statement](paper/multifractal.tex#L9989) |
| `mfd:cor-finite-exit` | `Paper.cor_finite_exit` | `SubdiffusiveProcess.Paper.cor_finite_exit` | [statement](paper/multifractal.tex#L10009) |
| `mfd:lem-local-normalizations` | `Paper.lem_local_normalizations` | `SubdiffusiveProcess.Paper.lem_local_normalizations` | [statement](paper/multifractal.tex#L10031) |
| `mfd:lem-finite-trace-tests` | `Paper.lem_finite_trace_tests` | `SubdiffusiveProcess.Paper.lem_finite_trace_tests` | [statement](paper/multifractal.tex#L10058) |
| `mfd:lem-finite-good-cell` | `Paper.lem_finite_good_cell` | `SubdiffusiveProcess.Paper.lem_finite_good_cell` | [statement](paper/multifractal.tex#L10084) |
| `mfd:lem-rare-tests` | `Paper.mfd_lem_rare_tests` | `SubdiffusiveProcess.Paper.mfd_lem_rare_tests` | [statement](paper/multifractal.tex#L10121) |
| `mfd:lem-finite-good-levels` | `Paper.mfd_lem_finite_good_levels` | `SubdiffusiveProcess.Paper.mfd_lem_finite_good_levels` | [statement](paper/multifractal.tex#L10144) |
| `mfd:lem-finite-stopping` | `Paper.lem_finite_stopping` | `SubdiffusiveProcess.Paper.lem_finite_stopping` | [statement](paper/multifractal.tex#L10161) |
| `mfd:lem-finite-source-comparison` | `Paper.lem_finite_source_comparison` | `SubdiffusiveProcess.Paper.lem_finite_source_comparison` | [statement](paper/multifractal.tex#L10207) |
| `mfd:prop-as-dirichlet` | `Paper.prop_as_dirichlet` | `SubdiffusiveProcess.Paper.prop_as_dirichlet` | [statement](paper/multifractal.tex#L10232) |
| `mfd:prop-as-response-bank` | `Paper.prop_as_response_bank` | `SubdiffusiveProcess.Paper.prop_as_response_bank` | [statement](paper/multifractal.tex#L10253) |
| `mfd:lem-as-coarse` | `Paper.lem_as_coarse` | `SubdiffusiveProcess.Paper.lem_as_coarse` | [statement](paper/multifractal.tex#L10291) |
| `mfd:lem-as-regularity` | `Paper.lem_as_regularity` | `SubdiffusiveProcess.Paper.lem_as_regularity` | [statement](paper/multifractal.tex#L10328) |
| `mfd:prop-as-forms` | `Paper.mfd_prop_as_forms` | `SubdiffusiveProcess.Paper.mfd_prop_as_forms` | [statement](paper/multifractal.tex#L10390) |
| `mfd:prop-as-quenched` | `Paper.mfd_prop_as_quenched` | `SubdiffusiveProcess.Paper.mfd_prop_as_quenched` | [statement](paper/multifractal.tex#L10407) |
| `lim:lem-strict-decay` | `Paper.lim_strict_decay` | `SubdiffusiveProcess.Paper.lim_strict_decay` | [statement](paper/multifractal.tex#L10448) |
| `lim:lem-mean-exit` | `Paper.lim_lem_mean_exit` | `SubdiffusiveProcess.Paper.lim_lem_mean_exit` | [statement](paper/multifractal.tex#L10474) |
| `lim:thm-nonbrownian` | `Paper.lim_thm_nonbrownian` | `SubdiffusiveProcess.Paper.lim_thm_nonbrownian` | [statement](paper/multifractal.tex#L10525) |
| `lim:cor-paths` | `Paper.lim_cor_paths` | `SubdiffusiveProcess.Paper.lim_cor_paths` | [statement](paper/multifractal.tex#L10563) |
| `lim:cor-exit-moments` | `Paper.lim_cor_exit_moments` | `SubdiffusiveProcess.Paper.lim_cor_exit_moments` | [statement](paper/multifractal.tex#L10601) |
| `lim:thm-measure` | `Paper.lim_thm_measure` | `SubdiffusiveProcess.Paper.lim_thm_measure` | [statement](paper/multifractal.tex#L10660) |
| `lim:thm-nongaussian` | `Paper.lim_thm_nongaussian` | `SubdiffusiveProcess.Paper.lim_thm_nongaussian` | [statement](paper/multifractal.tex#L10701) |
| App.A, The Orlicz notation X≤O\_Γ\_σ(A) (Appendix A) | `Paper.app_a_orlicz_notation` | `SubdiffusiveProcess.Paper.app_a_orlicz_notation` | [passage](paper/multifractal.tex) |
| App.A, Tail bound for X≤O\_Γ\_σ(A) (Appendix A) | `Paper.app_a_orlicz_tail_bound` | `SubdiffusiveProcess.Paper.app_a_orlicz_tail_bound` | [passage](paper/multifractal.tex) |
| App.A, Converse of the tail bound (Appendix A) | `Paper.app_a_orlicz_tail_converse` | `SubdiffusiveProcess.Paper.app_a_orlicz_tail_converse` | [passage](paper/multifractal.tex) |
| App.A, Triangle inequality for O\_Γ\_σ, finite sums (Appendix A) | `Paper.app_a_orlicz_triangle_finite` | `SubdiffusiveProcess.Paper.app_a_orlicz_triangle_finite` | [passage](paper/multifractal.tex) |
| App.A, Maximum of k variables with O\_Γ\_s tails (Appendix A) | `Paper.app_a_orlicz_max_scaling` | `SubdiffusiveProcess.Paper.app_a_orlicz_max_scaling` | [passage](paper/multifractal.tex) |
| App.A, Triangle inequality for O\_Γ\_σ, countable nonnegative families (Appendix A) | `Paper.app_a_orlicz_triangle_countable` | `SubdiffusiveProcess.Paper.app_a_orlicz_triangle_countable` | [passage](paper/multifractal.tex) |
| App.A, Independent mean-zero sums with O\_Γ\_s tails (Appendix A) | `Paper.app_a_orlicz_clt_scaling` | `SubdiffusiveProcess.Paper.app_a_orlicz_clt_scaling` | [passage](paper/multifractal.tex) |
| App.A, unnumbered lemma | `Paper.l_moments_OGamma2` | `SubdiffusiveProcess.Paper.l_moments_OGamma2` | [passage](paper/multifractal.tex) |
| `l.Rosenthal` | `Paper.l_Rosenthal` | `SubdiffusiveProcess.Paper.l_Rosenthal` | [statement](paper/multifractal.tex#L10865) |
| `p.concentration.for.scales` | `Paper.p_concentration_for_scales` | `SubdiffusiveProcess.Paper.p_concentration_for_scales` | [statement](paper/multifractal.tex#L10887) |
| `p.concentration.for.scales.exp.sequence` | `Paper.p_concentration_for_scales_exp_sequence` | `SubdiffusiveProcess.Paper.p_concentration_for_scales_exp_sequence` | [statement](paper/multifractal.tex#L10918) |
| `p.concentration.for.scales.exp.field` | `Paper.p_concentration_for_scales_exp_field` | `SubdiffusiveProcess.Paper.p_concentration_for_scales_exp_field` | [statement](paper/multifractal.tex#L10932) |
| `l.concentration.rare.intervals` | `Paper.l_concentration_rare_intervals` | `SubdiffusiveProcess.Paper.l_concentration_rare_intervals` | [statement](paper/multifractal.tex#L10949) |
| `l.circ.norm.dominates` | `Paper.l_circ_norm_dominates` | `SubdiffusiveProcess.Paper.l_circ_norm_dominates` | [statement](paper/multifractal.tex#L11016) |
| `l.Wsp.vs.Bspp` | `Paper.l_Wsp_vs_Bspp` | `SubdiffusiveProcess.Paper.l_Wsp_vs_Bspp` | [statement](paper/multifractal.tex#L11059) |
