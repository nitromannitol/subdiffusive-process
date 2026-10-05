module

public import SubdiffusiveProcess.Processes.PathTests
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace SubdiffusiveProcess

/-- The exponential reference measure on the positive time orthant has mass one and full support. -/
theorem positiveOrthant_expDensity_probability_and_openPos
    (k : ℕ) :
    IsProbabilityMeasure
      ((Measure.comap
        (fun s : {s : Fin k → ℝ // ∀ i, 0 < s i} => (s : Fin k → ℝ))
        (volume : Measure (Fin k → ℝ))).withDensity
          (fun s => ENNReal.ofReal (Real.exp (-(∑ i : Fin k, s.val i))))) ∧
    (((Measure.comap
        (fun s : {s : Fin k → ℝ // ∀ i, 0 < s i} => (s : Fin k → ℝ))
        (volume : Measure (Fin k → ℝ))).withDensity
          (fun s => ENNReal.ofReal (Real.exp (-(∑ i : Fin k, s.val i))))).IsOpenPosMeasure) := by
  classical
  let S : Set (Fin k → ℝ) := {s | ∀ i, 0 < s i}
  let e : S → (Fin k → ℝ) := fun s => s
  let w : (Fin k → ℝ) → ℝ := fun s => Real.exp (-(∑ i : Fin k, s i))
  have hS : MeasurableSet S := by
    rw [show S = Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)) by
      ext s
      simp only [S, mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, forall_const]]
    exact (measurableSet_pi Set.finite_univ.countable).2 <|
      Or.inl fun _ _ => measurableSet_Ioi
  have hS_open : IsOpen S := by
    rw [show S = Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)) by
      ext s
      simp only [S, mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, forall_const]]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  have hw_int : Integrable w (volume.restrict S) := by
    have hone : ∀ i : Fin k,
        Integrable ((Set.Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-x))) := by
      intro i
      rw [integrable_indicator_iff measurableSet_Ioi]
      simpa using exp_neg_integrableOn_Ioi (0 : ℝ) zero_lt_one
    have hp := MeasureTheory.Integrable.fintype_prod (μ := fun _ : Fin k => volume) hone
    have hp_on : IntegrableOn
        (fun s : Fin k → ℝ => ∏ i : Fin k, Real.exp (-s i)) S := by
      refine (hp.integrableOn).congr_fun ?_ hS
      intro s hs
      apply Finset.prod_congr rfl
      intro i hi
      rw [Set.indicator_of_mem]
      exact hs i
    refine hp_on.congr_fun ?_ hS
    intro s hs
    change (∏ i : Fin k, Real.exp (-s i)) = Real.exp (-(∑ i : Fin k, s i))
    rw [← Real.exp_sum]
    simp only [Finset.sum_neg_distrib]
  have hw_integral : ∫ s in S, w s = 1 := by
    rw [← integral_indicator hS]
    have hindicator :
        S.indicator w = fun s : Fin k → ℝ =>
          ∏ i : Fin k, (Set.Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-x)) (s i) := by
      funext s
      by_cases hs : s ∈ S
      · rw [Set.indicator_of_mem hs]
        change Real.exp (-(∑ i : Fin k, s i)) = _
        rw [show -(∑ i : Fin k, s i) = ∑ i : Fin k, -s i by
          simp only [Finset.sum_neg_distrib], Real.exp_sum]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Set.indicator_of_mem]
        exact hs i
      · rw [Set.indicator_of_notMem hs]
        simp only [S, mem_ofPred_eq, not_forall] at hs
        obtain ⟨i, hi⟩ := hs
        rw [Finset.prod_eq_zero (Finset.mem_univ i)]
        rw [Set.indicator_of_notMem (show s i ∉ Set.Ioi (0 : ℝ) from hi)]
    rw [hindicator, MeasureTheory.integral_fintype_prod_volume_eq_prod]
    simp only [integral_indicator measurableSet_Ioi, integral_exp_neg_Ioi_zero,
      Finset.prod_const_one]
  have hdensity_meas : Measurable (fun s : S => ENNReal.ofReal (w s)) := by
    fun_prop
  have hmass :
      ((Measure.comap e (volume : Measure (Fin k → ℝ))).withDensity
        (fun s => ENNReal.ofReal (w s))) univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [MeasureTheory.lintegral_subtype_comap hS (fun s => ENNReal.ofReal (w s))]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hw_int
      (ae_of_all _ fun s => (Real.exp_pos _).le)]
    rw [hw_integral]
    norm_num
  have hprob : IsProbabilityMeasure
      ((Measure.comap e (volume : Measure (Fin k → ℝ))).withDensity
        (fun s => ENNReal.ofReal (w s))) :=
    IsProbabilityMeasure.mk hmass
  let : Measure.IsOpenPosMeasure (Measure.comap e (volume : Measure (Fin k → ℝ))) :=
    Measure.IsOpenPosMeasure.comap volume hS_open.isOpenEmbedding_subtypeVal
  have hopen : Measure.IsOpenPosMeasure
      ((Measure.comap e (volume : Measure (Fin k → ℝ))).withDensity
        (fun s => ENNReal.ofReal (w s))) := by
    refine ⟨?_⟩
    intro U hU hUne hzero
    have hbasezero : (Measure.comap e (volume : Measure (Fin k → ℝ))) U = 0 := by
      rw [withDensity_apply_eq_zero hdensity_meas] at hzero
      have hposset : {x : S | ENNReal.ofReal (w x) ≠ 0} = Set.univ := by
        ext x
        simp only [mem_ofPred_eq, Set.mem_univ, iff_true, ENNReal.ofReal_ne_zero_iff]
        exact Real.exp_pos _
      rwa [hposset, Set.univ_inter] at hzero
    exact (Measure.IsOpenPosMeasure.open_pos U hU hUne) hbasezero
  simpa only [S, e, w] using! And.intro hprob hopen

end SubdiffusiveProcess
