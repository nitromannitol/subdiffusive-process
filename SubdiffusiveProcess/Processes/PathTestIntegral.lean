module

public import SubdiffusiveProcess.Processes.PathTests
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators BoundedContinuousFunction
namespace SubdiffusiveProcess

/-- Fubini for the actual bounded integrated path test; integrability is proved. -/
theorem integral_integrated_path_test
    {d k : ℕ}
    [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (P : ProbabilityMeasure C(ℝ≥0, SpatialCoordinates d))
    (f : Fin k → (SpatialCoordinates d →ᵇ ℝ))
    (ν : Fin k → ℝ) (hν : ∀ i, 0 < ν i) :
    (∫ z : C(ℝ≥0, SpatialCoordinates d),
      (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
        Real.exp (-(∑ i : Fin k, ν i * s i)) *
          ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
      ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
    ∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
      Real.exp (-(∑ i : Fin k, ν i * s i)) *
        ∫ z : C(ℝ≥0, SpatialCoordinates d),
          ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))
          ∂(P : Measure C(ℝ≥0, SpatialCoordinates d)) := by
  classical
  let S : Set (Fin k → ℝ) := {s | ∀ i, 0 < s i}
  have hS : MeasurableSet S := by
    rw [show S = Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)) by
      ext s
      simp only [S, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, forall_const]]
    exact (measurableSet_pi Set.finite_univ.countable).2 <|
      Or.inl fun _ _ => measurableSet_Ioi
  let w : (Fin k → ℝ) → ℝ := fun s => Real.exp (-(∑ i : Fin k, ν i * s i))
  have hw_int : Integrable w (volume.restrict S) := by
    have hone : ∀ i : Fin k,
        Integrable ((Set.Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-ν i * x))) := by
      intro i
      rw [integrable_indicator_iff measurableSet_Ioi]
      exact exp_neg_integrableOn_Ioi 0 (hν i)
    have hp := MeasureTheory.Integrable.fintype_prod (μ := fun _ : Fin k => volume) hone
    have hp_on : IntegrableOn
        (fun s : Fin k → ℝ => ∏ i : Fin k, Real.exp (-ν i * s i)) S := by
      refine (hp.integrableOn).congr_fun ?_ hS
      intro s hs
      change ∀ i, 0 < s i at hs
      apply Finset.prod_congr rfl
      intro i hi
      rw [Set.indicator_of_mem]
      exact hs i
    refine hp_on.congr_fun ?_ hS
    intro s hs
    change (∏ i : Fin k, Real.exp (-ν i * s i)) =
      Real.exp (-(∑ i : Fin k, ν i * s i))
    rw [← Real.exp_sum]
    congr 1
    simp only [neg_mul, Finset.sum_neg_distrib]
  let C : ℝ := ∏ i : Fin k, ‖f i‖
  let F : C(ℝ≥0, SpatialCoordinates d) × (Fin k → ℝ) → ℝ := fun p =>
    w p.2 * ∏ i : Fin k,
      f i (p.1 (Real.toNNReal (∑ j ∈ Finset.Iic i, p.2 j)))
  have hF_meas : AEStronglyMeasurable F
      ((P : Measure C(ℝ≥0, SpatialCoordinates d)).prod (volume.restrict S)) :=
    Continuous.aestronglyMeasurable (by
      dsimp only [F, w]
      fun_prop)
  have hdom : Integrable (fun p : C(ℝ≥0, SpatialCoordinates d) × (Fin k → ℝ) =>
      C * w p.2)
      ((P : Measure C(ℝ≥0, SpatialCoordinates d)).prod (volume.restrict S)) := by
    exact (integrable_const C).mul_prod hw_int
  have hF_int : Integrable F
      ((P : Measure C(ℝ≥0, SpatialCoordinates d)).prod (volume.restrict S)) := by
    refine hdom.mono hF_meas ?_
    filter_upwards with p
    change |w p.2 * ∏ i : Fin k,
      f i (p.1 (Real.toNNReal (∑ j ∈ Finset.Iic i, p.2 j)))| ≤ |C * w p.2|
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
    change Real.exp (-∑ i, ν i * p.2 i) * _ ≤ C * Real.exp (-∑ i, ν i * p.2 i)
    rw [mul_comm C]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
      BoundedContinuousFunction.norm_coe_le_norm (f i) _
  change Integrable (Function.uncurry (fun z s =>
    Real.exp (-(∑ i : Fin k, ν i * s i)) *
      ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))))
      ((P : Measure C(ℝ≥0, SpatialCoordinates d)).prod (volume.restrict S)) at hF_int
  rw [integral_integral_swap hF_int]
  apply integral_congr_ae
  filter_upwards with s
  rw [integral_const_mul]

end SubdiffusiveProcess
