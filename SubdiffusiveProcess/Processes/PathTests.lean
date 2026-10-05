module

public import SubdiffusiveProcess.Processes.PathLaw
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators BoundedContinuousFunction
/-! Continuity of the literal integrated path tests used for law determination.
The determining property is a separate assertion from the construction of
the path tests in this module. -/

namespace SubdiffusiveProcess

theorem continuous_integrated_path_test
    {d k : ℕ} (f : Fin k → (SpatialCoordinates d →ᵇ ℝ))
    (ν : Fin k → ℝ) (hν : ∀ i, 0 < ν i) :
    Continuous (fun z : C(ℝ≥0, SpatialCoordinates d) =>
      ∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
        Real.exp (-(∑ i : Fin k, ν i * s i)) *
          ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))) := by
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
  have hbound_int : Integrable (fun s => C * w s) (volume.restrict S) := hw_int.const_mul C
  rw [continuous_iff_continuousAt]
  intro z
  apply tendsto_integral_filter_of_dominated_convergence (fun s => C * w s)
  · filter_upwards with y
    exact Continuous.aestronglyMeasurable (by
      fun_prop)
  · filter_upwards with y
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    change Real.exp (-∑ i, ν i * s i) * _ ≤ C * Real.exp (-∑ i, ν i * s i)
    rw [mul_comm C]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
      BoundedContinuousFunction.norm_coe_le_norm (f i) _
  · exact hbound_int
  · filter_upwards with s
    apply Tendsto.mul tendsto_const_nhds
    apply tendsto_finsetProd
    intro i hi
    exact (f i).continuous.continuousAt.tendsto.comp
      ((continuous_eval_const (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))).tendsto z)



/-- Uniform bound on the full positive-time path test. -/
theorem norm_integrated_path_test_le
    {d k : ℕ} (f : Fin k → (SpatialCoordinates d →ᵇ ℝ))
    (ν : Fin k → ℝ) (hν : ∀ i, 0 < ν i)
    (z : C(ℝ≥0, SpatialCoordinates d)) :
    ‖∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
      Real.exp (-(∑ i : Fin k, ν i * s i)) *
        ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))‖ ≤
      ∏ i : Fin k, (‖f i‖ / ν i) := by
  classical
  let S : Set (Fin k → ℝ) := {s | ∀ i, 0 < s i}
  let g : (Fin k → ℝ) → ℝ := fun s => ∏ i : Fin k, Real.exp (-ν i * s i)
  let C : ℝ := ∏ i : Fin k, ‖f i‖
  have hS : MeasurableSet S := by
    rw [show S = Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)) by
      ext s
      simp only [S, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, forall_const]]
    exact (measurableSet_pi Set.finite_univ.countable).2 <|
      Or.inl fun _ _ => measurableSet_Ioi
  have hone : ∀ i : Fin k,
      Integrable ((Set.Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-ν i * x))) := by
    intro i
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact exp_neg_integrableOn_Ioi 0 (hν i)
  have hg_indicator :
      S.indicator g = fun s : Fin k → ℝ =>
        ∏ i : Fin k, (Set.Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-ν i * x)) (s i) := by
    funext s
    by_cases hs : s ∈ S
    · rw [Set.indicator_of_mem hs]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Set.indicator_of_mem]
      exact hs i
    · rw [Set.indicator_of_notMem hs]
      simp only [S, Set.mem_ofPred_eq, not_forall] at hs
      obtain ⟨i, hi⟩ := hs
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      exact show (Set.Ioi (0 : ℝ)).indicator
        (fun x : ℝ => Real.exp (-ν i * x)) (s i) = 0 by
          have hi' : s i ∉ Set.Ioi (0 : ℝ) := hi
          simp only [Set.indicator, ite_eq_right hi']
  have hg_int : Integrable g (volume.restrict S) := by
    change IntegrableOn g S
    rw [← integrable_indicator_iff hS]
    rw [hg_indicator]
    exact MeasureTheory.Integrable.fintype_prod (μ := fun _ : Fin k => volume) hone
  have hdom : Integrable (fun s => C * g s) (volume.restrict S) := hg_int.const_mul C
  calc
    ‖∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
        Real.exp (-(∑ i : Fin k, ν i * s i)) *
          ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))‖
        ≤ ∫ s in S, C * g s := by
          apply norm_integral_le_of_norm_le hdom
          rw [ae_restrict_iff' hS]
          filter_upwards with s hs
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          change Real.exp (-∑ i, ν i * s i) * _ ≤ C * g s
          rw [show Real.exp (-∑ i, ν i * s i) = g s by
            simp only [g, ← Real.exp_sum, neg_mul, Finset.sum_neg_distrib]]
          rw [mul_comm C (g s)]
          apply mul_le_mul_of_nonneg_left _
            (Finset.prod_pos fun _ _ => Real.exp_pos _).le
          rw [Finset.abs_prod]
          exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
            BoundedContinuousFunction.norm_coe_le_norm (f i) _
    _ = C * ∏ i : Fin k, (1 / ν i) := by
      rw [integral_const_mul]
      congr 1
      rw [← integral_indicator hS, hg_indicator,
        MeasureTheory.integral_fintype_prod_volume_eq_prod]
      apply Finset.prod_congr rfl
      intro i hi
      rw [integral_indicator measurableSet_Ioi]
      have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
          HasDerivAt (fun x : ℝ => Real.exp (-ν i * x) / (-ν i))
            (Real.exp (-ν i * x)) x := by
        intro x hx
        simpa [hν i |>.ne'] using
          (((hasDerivAt_id x).const_mul (-ν i)).exp.div_const (-ν i))
      have htend : Tendsto (fun x : ℝ => Real.exp (-ν i * x) / (-ν i))
          atTop (𝓝 0) := by
        convert (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 (hν i)))).div_const (-ν i)
          using 1
        all_goals simp
      simpa [hν i |>.ne'] using
        integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (exp_neg_integrableOn_Ioi 0 (hν i)) htend
    _ = ∏ i : Fin k, (‖f i‖ / ν i) := by
      simp only [C, div_eq_mul_inv, Finset.prod_mul_distrib, one_mul]

theorem continuous_path_product_expectation
    {d k : ℕ}
    [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (P : ProbabilityMeasure C(ℝ≥0, SpatialCoordinates d))
    (f : Fin k → (SpatialCoordinates d →ᵇ ℝ)) :
    Continuous (fun t : Fin k → ℝ≥0 =>
      ∫ z : C(ℝ≥0, SpatialCoordinates d),
        ∏ i : Fin k, f i (z (t i)) ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) := by
  classical
  let C : ℝ := ∏ i : Fin k, ‖f i‖
  apply continuous_of_dominated (bound := fun _ => C)
  · intro t
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · intro t
    filter_upwards with z
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
      BoundedContinuousFunction.norm_coe_le_norm (f i) _
  · exact integrable_const C
  · filter_upwards with z
    apply continuous_finsetProd
    intro i hi
    exact (f i).continuous.comp (z.continuous.comp (continuous_apply i))

end SubdiffusiveProcess
