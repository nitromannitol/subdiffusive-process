import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationRadial
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationGenerator
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationSemigroup

/-!
# The generator on the radial exhaustion

Linear growth relative to the speed measure gives a uniform generator bound
proportional to the radial exponent.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec
open Filter Topology MeasureTheory MarkovProcess MarkovProcess.Semigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty

/-- The lower bound complements the supersolution estimate for the radial profile. -/
theorem coeffFluxDiv_radialBarrier_lower {d : ℕ} {c rho : Vec d → ℝ}
    (hc : Differentiable ℝ c) (hcnn : ∀ x, 0 ≤ c x)
    {K A beta : ℝ} (hK : 0 ≤ K) (hA : 0 < A)
    (hrho : ∀ x, 0 < rho x)
    (hgrowth : ∀ x, euclideanNorm (euclideanGradient c x) + c x ≤
      K * rho x * (1 + ‖x‖)) (hbeta : 0 ≤ beta) (x : Vec d) :
    -(beta * K * (2 * Real.sqrt d + 2 * (d : ℝ)) * rho x * radialBarrier A beta x) ≤
      coeffFluxDiv c (radialBarrier A beta) x := by
  have hq := vecNormSq_nonneg x
  have hs : 0 < 1 + vecNormSq x := by positivity
  have hscalar := radial_growth_scalar_bound
    (euclideanNorm_nonneg (euclideanGradient c x)) (hcnn x) (norm_nonneg x)
    hK (hrho x).le (Real.sqrt_nonneg (d : ℝ)) (Nat.cast_nonneg d)
    (euclideanNorm_le_sqrt_dim_mul_norm x) (hgrowth x) (one_add_norm_sq_le_vecNormSq x)
  have hkey : beta * (euclideanNorm x * euclideanNorm (euclideanGradient c x) +
      (d : ℝ) * c x) ≤
      (beta * K * (2 * Real.sqrt d + 2 * (d : ℝ))) * rho x * (1 + vecNormSq x) := by
    convert mul_le_mul_of_nonneg_left hscalar hbeta using 1
    ring
  have hdot : vecDot x (euclideanGradient c x) ≤
      euclideanNorm x * euclideanNorm (euclideanGradient c x) :=
    (le_abs_self _).trans (abs_vecDot_le_euclideanNorm_mul x (euclideanGradient c x))
  have h := radial_flux_lower_bound (radialProfileD_mul_one_add (A := A) (beta := beta) hq)
    (radialProfileDD_nonneg hA.le hbeta hq) (radialBarrier_pos hA beta x).le hs hq hbeta
    (Nat.cast_nonneg d) (hcnn x) hdot hkey
  change -(beta * K * (2 * Real.sqrt d + 2 * (d : ℝ)) * rho x *
    radialProfile A beta (vecNormSq x)) ≤ _ at h ⊢
  change _ ≤ coeffFluxDiv c (fun y : Vec d ↦ radialProfile A beta (vecNormSq y)) x
  rw [coeffFluxDiv_compVecNormSq hc
    (fun t ht ↦ hasDerivAt_radialProfile A beta ht)
    (fun t ht ↦ hasDerivAt_radialProfileD A beta ht)]
  exact h

/-- Both signs of the weighted generator are controlled by the free exponent. -/
theorem abs_weightedFluxDiv_radialBarrier_le {d : ℕ} {c rho : Vec d → ℝ}
    (hc : Differentiable ℝ c) (hcnn : ∀ x, 0 ≤ c x)
    {K A beta : ℝ} (hK : 0 ≤ K) (hA : 0 < A)
    (hrho : ∀ x, 0 < rho x)
    (hgrowth : ∀ x, euclideanNorm (euclideanGradient c x) + c x ≤
      K * rho x * (1 + ‖x‖)) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (x : Vec d) :
    |coeffFluxDiv c (radialBarrier A beta) x / rho x| ≤
      (K * (4 * Real.sqrt d + 2 * (d : ℝ) + 6) * beta) * radialBarrier A beta x := by
  have hlower := coeffFluxDiv_radialBarrier_lower hc hcnn hK hA hrho hgrowth hbeta.le x
  have hupper := coeffFluxDiv_radialBarrier_le hc hcnn hK hA hrho hgrowth hbeta hbeta1
    (mu := 2 * (beta * K * (2 * Real.sqrt d + 6))) (by ring_nf; exact le_rfl) x
  have hupper' : coeffFluxDiv c (radialBarrier A beta) x ≤
      (beta * K * (2 * Real.sqrt d + 6)) * rho x * radialBarrier A beta x := by
    convert hupper using 1
    ring
  have h := abs_div_le_sum_bounds
    (a := beta * K * (2 * Real.sqrt d + 2 * (d : ℝ)))
    (b := beta * K * (2 * Real.sqrt d + 6))
    (by positivity) (by positivity) (hrho x) (radialBarrier_pos hA beta x).le hlower hupper'
  convert h using 1
  ring

/-- The radial functions belong to the actual generated semigroup's domain,
and their generators are uniformly small when the exponent is small. -/
theorem exists_radial_generator {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D) (hcnn : ∀ x, 0 ≤ c x)
    {K beta : ℝ} (hK : 0 ≤ K)
    (hgrowth : ∀ x, euclideanNorm (euclideanGradient c x) + c x ≤
      K * rho x * (1 + ‖x‖)) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    ∃ w : (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense).c0Semigroup.generatorDomain,
      (∀ x, (w : C₀(Vec d, ℝ)) x = radialBarrier 1 beta x) ∧
      ‖(D.isFellerKernelSemigroup_fellerKernelSemigroup hdense).c0Semigroup.generator w‖ ≤
        K * (4 * Real.sqrt d + 2 * (d : ℝ) + 6) * beta := by
  let hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  let w := radialBarrierC0 (d := d) beta hbeta
  let C := K * (4 * Real.sqrt d + 2 * (d : ℝ) + 6) * beta
  let f : Vec d → ℝ := fun x ↦ coeffFluxDiv c (radialBarrier 1 beta) x / rho x
  have hfc : Continuous f :=
    (continuous_coeffFluxDiv hc (contDiff_radialBarrier 1 beta)).div hrho
      (fun x ↦ (B.weight_pos x).ne')
  have hbound : ∀ x, ‖f x‖ ≤ C * w x := by
    intro x
    exact abs_weightedFluxDiv_radialBarrier_le (hc.differentiable le_rfl) hcnn hK
      zero_lt_one B.weight_pos hgrowth hbeta hbeta1 x
  let g := dominatedC0 f hfc w C hbound
  have hgnorm : ‖g‖ ≤ C :=
    norm_c0_le_const_of_dominated g w (by dsimp [C]; positivity)
      (fun x ↦ radialBarrier_one_le_one hbeta.le x) hbound
  let mu : PositiveShift := ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩
  let forcing : C₀(Vec d, ℝ) := (mu : ℝ) • w - g
  have hsol : D.solution mu forcing = w :=
    solution_eq_of_smoothMassiveForcing B hc D hD mu w forcing
      (contDiff_radialBarrier 1 beta) (fun _ ↦ rfl)
  have hres : hF.c0Semigroup.resolvent mu forcing = w :=
    (Section7Clock.resolvent_c0Semigroup_eq_solution hdense hF rfl mu forcing).trans hsol
  obtain ⟨hw, hgen⟩ := generator_eq_of_resolvent_witness hF.c0Semigroup mu w forcing hres
  refine ⟨⟨w, hw⟩, fun _ ↦ rfl, ?_⟩
  rw [hgen]
  have hcancel : (mu : ℝ) • w - forcing = g := by dsimp [forcing]; abel
  rw [hcancel]
  exact hgnorm

/-- Conservativity follows from the weak resolvent and linear coefficient growth.
It is proved before constructing or using a continuous-path law. -/
theorem isConservative_of_weakResolvent_linearGrowth {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D) (hcnn : ∀ x, 0 ≤ c x)
    {K : ℝ} (hK : 0 ≤ K)
    (hgrowth : ∀ x, euclideanNorm (euclideanGradient c x) + c x ≤
      K * rho x * (1 + ‖x‖)) :
    (D.fellerKernelSemigroup hdense).IsConservative := by
  have hex := fun n ↦ exists_radial_generator B hc hrho D hdense hD hcnn hK hgrowth
    (reciprocalNatSucc_pos_le_one n).1 (reciprocalNatSucc_pos_le_one n).2
  choose f hf hgen using hex
  apply isConservative_of_generator_approximation
    (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense) f
  · intro n x
    rw [hf n x]
    exact radialBarrier_one_le_one (reciprocalNatSucc_pos_le_one n).1.le x
  · intro x
    simp_rw [hf]
    exact (tendsto_radialBarrier_beta_zero x).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · refine squeeze_zero (fun n ↦ norm_nonneg _) hgen ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (K * (4 * Real.sqrt d + 2 * (d : ℝ) + 6))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
