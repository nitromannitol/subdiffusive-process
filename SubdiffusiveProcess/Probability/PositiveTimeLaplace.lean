module

public import SubdiffusiveProcess.Probability.PositiveTimeMeasure
public import SubdiffusiveProcess.Probability.BoundedMomentDensities
@[expose] public section

open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction ENNReal
namespace SubdiffusiveProcess

/-- Positive integer Laplace integrals determine bounded continuous signed functions on the positive time orthant. -/
theorem boundedContinuous_eq_of_positiveInteger_laplace
    {k : ℕ}
    (F G : {s : Fin k → ℝ // ∀ i, 0 < s i} →ᵇ ℝ)
    (hm : ∀ m : Fin k → ℕ,
      (∫ s : {s : Fin k → ℝ // ∀ i, 0 < s i},
        Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s.val i)) * F s
        ∂(Measure.comap (fun s : {s : Fin k → ℝ // ∀ i, 0 < s i} => (s : Fin k → ℝ))
          (volume : Measure (Fin k → ℝ)))) =
      ∫ s : {s : Fin k → ℝ // ∀ i, 0 < s i},
        Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s.val i)) * G s
        ∂(Measure.comap (fun s : {s : Fin k → ℝ // ∀ i, 0 < s i} => (s : Fin k → ℝ))
          (volume : Measure (Fin k → ℝ)))) :
    F = G := by
  classical
  let S : Set (Fin k → ℝ) := {s | ∀ i, 0 < s i}
  have hS_open : IsOpen S := by
    rw [show S = Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)) by
      ext s
      simp only [S, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, forall_const]]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  letI : PolishSpace {s : Fin k → ℝ // ∀ i, 0 < s i} := hS_open.polishSpace
  let base : Measure {s : Fin k → ℝ // ∀ i, 0 < s i} :=
    Measure.comap
      (fun s : {s : Fin k → ℝ // ∀ i, 0 < s i} => (s : Fin k → ℝ))
    (volume : Measure (Fin k → ℝ))
  let density : {s : Fin k → ℝ // ∀ i, 0 < s i} → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (Real.exp (-(∑ i : Fin k, s.val i)))
  let μ : Measure {s : Fin k → ℝ // ∀ i, 0 < s i} := base.withDensity density
  have hμ := positiveOrthant_expDensity_probability_and_openPos k
  letI : IsProbabilityMeasure μ := by simpa only [μ, base, density] using hμ.1
  letI : μ.IsOpenPosMeasure := by simpa only [μ, base, density] using hμ.2
  let coord : Fin k → ({s : Fin k → ℝ // ∀ i, 0 < s i} →ᵇ ℝ) := fun i =>
    BoundedContinuousFunction.mkOfBound
      ⟨fun s => Real.exp (-s.val i), by
        exact Real.continuous_exp.comp
          (((continuous_apply i).comp continuous_subtype_val).neg)⟩ 2 (by
        intro x y
        calc
          dist (Real.exp (-x.val i)) (Real.exp (-y.val i))
              ≤ dist (Real.exp (-x.val i)) 0 + dist 0 (Real.exp (-y.val i)) :=
                dist_triangle _ _ _
          _ ≤ 2 := by
            simp only [Real.dist_eq, sub_zero, zero_sub, abs_neg,
              abs_of_pos (Real.exp_pos _)]
            have hx : Real.exp (-x.val i) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (x.property i).le)
            have hy : Real.exp (-y.val i) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (y.property i).le)
            linarith)
  refine boundedContinuous_eq_of_monomial_integrals coord ?_ μ F G ?_
  · intro x y hxy
    have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hval
    refine ⟨i, ?_⟩
    intro he
    apply hi
    have hneg : -x.val i = -y.val i := Real.exp_injective he
    linarith
  · intro m
    have hweight (s : {s : Fin k → ℝ // ∀ i, 0 < s i}) :
        Real.exp (-(∑ i : Fin k, s.val i)) *
            ∏ i : Fin k, Real.exp (-s.val i) ^ m i =
          Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s.val i)) := by
      simp_rw [← Real.exp_nat_mul]
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      simp_rw [add_mul, one_mul]
      rw [Finset.sum_add_distrib]
      simp_rw [mul_neg]
      rw [Finset.sum_neg_distrib]
      ring
    have hdensity_meas : Measurable density := by
      dsimp only [density]
      fun_prop
    have hdensity_top : ∀ᵐ s ∂base, density s < ∞ := by
      filter_upwards with s
      exact ENNReal.ofReal_lt_top
    rw [show μ = base.withDensity density by rfl,
      integral_withDensity_eq_integral_toReal_smul hdensity_meas hdensity_top,
      integral_withDensity_eq_integral_toReal_smul hdensity_meas hdensity_top]
    simp only [density, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    change (∫ x, Real.exp (-(∑ i : Fin k, x.val i)) *
        (F x * ∏ i : Fin k, Real.exp (-x.val i) ^ m i) ∂base) =
      ∫ x, Real.exp (-(∑ i : Fin k, x.val i)) *
        (G x * ∏ i : Fin k, Real.exp (-x.val i) ^ m i) ∂base
    rw [show (fun x => Real.exp (-(∑ i : Fin k, x.val i)) *
          (F x * ∏ i : Fin k, Real.exp (-x.val i) ^ m i)) =
        fun x => Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * x.val i)) * F x by
          funext x
          rw [mul_comm (F x), ← mul_assoc, hweight],
      show (fun x => Real.exp (-(∑ i : Fin k, x.val i)) *
          (G x * ∏ i : Fin k, Real.exp (-x.val i) ^ m i)) =
        fun x => Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * x.val i)) * G x by
          funext x
          rw [mul_comm (G x), ← mul_assoc, hweight]]
    simpa only [base] using hm m

end SubdiffusiveProcess
