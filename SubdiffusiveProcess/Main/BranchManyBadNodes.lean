module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import SubdiffusiveProcess.Probability.DisjointWitnessSelection
public import SubdiffusiveProcess.Probability.OriginalWindowIndependence
public import SubdiffusiveProcess.Probability.WeightedWitnessEnumeration

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SubdiffusiveProcess

/-- The exact branch bound  using only original-layer independence. -/
theorem branch_many_bad_nodes
    (J : ℕ)
    (A θ : ℝ)
    (hA : 0 < A)
    (_hθ₀ : 0 < θ)
    (_hθ₁ : θ < 1)
    (Ω X : Type*)
    [mΩ : MeasurableSpace Ω]
    [mX : MeasurableSpace X]
    (P : Measure Ω)
    [_hP : IsProbabilityMeasure P]
    (g : ℤ → Ω → X)
    (hg_meas : ∀ j : ℤ, Measurable (g j))
    (hg_indep : iIndepFun g P)
    (n : Fin J → ℤ)
    (hn : Function.Injective n)
    (failure : Fin J → Set Ω)
    (W : Fin J → ℕ+ → Set Ω)
    (hW_meas : ∀ (i : Fin J) (h : ℕ+),
      @MeasurableSet Ω
        (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (n i - (h : ℤ)) (n i + 2 * (h : ℤ))),
          MeasurableSpace.comap (g (-j)) (inferInstance : MeasurableSpace X))
        (W i h))
    (hW_prob : ∀ (i : Fin J) (h : ℕ+),
      P (W i h) ≤ ENNReal.ofReal (Real.exp (-A * (h : ℝ))))
    (hfailure : ∀ i : Fin J, failure i ⊆ ⋃ h : ℕ+, W i h) :
    P { ω | θ * (J : ℝ) ≤
        (Set.ncard {i : Fin J | ω ∈ failure i} : ℝ) } ≤
      ENNReal.ofReal (Real.exp
        (-((A * θ / 24) + Real.log (1 - Real.exp (-A / 2))) * (J : ℝ)))
:= by
  classical
  let S : (Fin J → Option ℕ+) → Finset (Fin J) := fun w =>
    Finset.univ.filter (fun i => ∃ h : ℕ+, w i = some h)
  let rN : (Fin J → Option ℕ+) → Fin J → ℕ := fun w i =>
    (w i).elim (0 : ℕ) (fun h => (h : ℕ))
  let r : (Fin J → Option ℕ+) → Fin J → ℝ := fun w i =>
    (rN w i : ℝ)
  let E : (Fin J → Option ℕ+) → Fin J → Set Ω := fun w i =>
    (w i).elim Set.univ (fun h => W i h)
  let V : (Fin J → Option ℕ+) → Fin J → Finset ℤ := fun w i =>
    (w i).elim ∅ (fun h => Finset.Icc (n i - (h : ℤ)) (n i + 2 * (h : ℤ)))
  let I : (Fin J → Option ℕ+) → Set Ω := fun w =>
    ⋂ i ∈ S w, E w i
  let Admissible : (Fin J → Option ℕ+) → Prop := fun w =>
    (∀ ⦃i⦄, i ∈ S w → ∀ ⦃k⦄, k ∈ S w → i ≠ k →
      Disjoint (V w i) (V w k)) ∧
    θ * (J : ℝ) ≤ 12 * ∑ i ∈ S w, r w i
  let K : (Fin J → Option ℕ+) → Set Ω := fun w =>
    if h : Admissible w then I w else ∅
  let weight : (Fin J → Option ℕ+) → ℝ≥0∞ := fun w =>
    ∏ i : Fin J, (w i).elim (1 : ℝ≥0∞)
      (fun h => ENNReal.ofReal (Real.exp (-A * (h : ℝ) / 2)))
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-A * θ * (J : ℝ) / 24))
  have hcover :
      {ω | θ * (J : ℝ) ≤
          (Set.ncard {i : Fin J | ω ∈ failure i} : ℝ)} ⊆ ⋃ w, K w := by
    intro ω hω
    obtain ⟨w, hwW, hwdisj, hwbound⟩ :=
      exists_optional_disjoint_witnesses_of_many_failures J θ n hn failure W
        hfailure ω hω
    apply Set.mem_iUnion.2
    refine ⟨w, ?_⟩
    have hadm : Admissible w := by
      constructor
      · intro i hi k hk hik
        have hi' : ∃ h : ℕ+, w i = some h := by simpa [S] using hi
        have hk' : ∃ h : ℕ+, w k = some h := by simpa [S] using hk
        obtain ⟨hi', hwi⟩ := hi'
        obtain ⟨hk', hwk⟩ := hk'
        simpa [V, hwi, hwk] using hwdisj i k hi' hk' hik hwi hwk
      · have hsum :
            (∑ i : Fin J, (w i).elim (0 : ℕ) (fun h => (h : ℕ))) =
            ∑ i ∈ S w, (w i).elim (0 : ℕ) (fun h => (h : ℕ)) := by
          rw [show S w = Finset.univ.filter (fun i => ∃ h : ℕ+, w i = some h) by rfl]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases his : ∃ h : ℕ+, w i = some h
          · obtain ⟨h, hwi⟩ := his
            simp [hwi]
          · have hnone : w i = none := by
              cases hwi : w i with
              | none => rfl
              | some h => exact (his ⟨h, hwi⟩).elim
            simp [hnone]
        have hsumR :
            (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) =
              ∑ i ∈ S w, r w i := by
          rw [show S w = Finset.univ.filter (fun i => ∃ h : ℕ+, w i = some h) by rfl]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases his : ∃ h : ℕ+, w i = some h
          · obtain ⟨h, hwi⟩ := his
            simp [r, rN, hwi]
          · have hnone : w i = none := by
              cases hwi : w i with
              | none => rfl
              | some h => exact (his ⟨h, hwi⟩).elim
            simp [r, hnone]
        calc
          θ * (J : ℝ) ≤
              12 * (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) := by
            simpa using hwbound
          _ = 12 * ∑ i ∈ S w, r w i := by rw [hsumR]
    simp only [K]
    rw [dite_eq_left hadm]
    change ω ∈ (⋂ i ∈ S w, E w i)
    simp only [Set.mem_iInter]
    intro i hi
    have hi' : ∃ h : ℕ+, w i = some h := by
      simpa [S] using hi
    obtain ⟨h, hwi⟩ := hi'
    have hiW : ω ∈ W i h := hwW i h hwi
    simpa [I, E, hwi] using hiW
  have hfixed : ∀ w : Fin J → Option ℕ+, P (K w) ≤ C * weight w := by
    intro w
    by_cases hadm : Admissible w
    · simp only [K]
      rw [dite_eq_left hadm]
      rcases hadm with ⟨hdisj, hsum_bound⟩
      have hsupport : ∀ i : Fin J, i ∈ S w → ∃ h : ℕ+, w i = some h := by
        intro i hi
        simpa [S] using hi
      have hE : ∀ i, i ∈ S w →
          @MeasurableSet Ω
            (⨆ j : ℤ, ⨆ (_ : j ∈ V w i),
              MeasurableSpace.comap (g (-j)) (inferInstance : MeasurableSpace X))
            (E w i) := by
        intro i hi
        obtain ⟨h, hwi⟩ := hsupport i hi
        have hVeq : V w i = Finset.Icc (n i - (h : ℤ)) (n i + 2 * (h : ℤ)) := by
          simp [V, hwi]
        rw [hVeq]
        simpa [E, hwi] using hW_meas i h
      have hprod :=
        measure_biInter_eq_prod_of_disjoint_measurable_original_windows
          P g hg_meas hg_indep (S w) (V w) hdisj (E w) hE
      have hprod_le :
          P (I w) ≤ ∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i)) := by
        change P (⋂ i ∈ S w, E w i) ≤ _
        rw [hprod]
        apply Finset.prod_le_prod
        intro i hi
        obtain ⟨h, hwi⟩ := hsupport i hi
        simpa [E, r, rN, hwi] using hW_prob i h
      have hsum : 0 ≤ ∑ i ∈ S w, r w i := by
        apply Finset.sum_nonneg
        intro i hi
        obtain ⟨h, hwi⟩ := hsupport i hi
        simp [r]
      have hsum_boundR : θ * (J : ℝ) ≤ 12 * ∑ i ∈ S w, r w i := by
        exact hsum_bound
      have hexp_prod :
          (∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i))) =
            ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i))) := by
        induction S w using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.prod_insert hi, ih, ← ENNReal.ofReal_mul (by positivity)]
            simp only [Finset.sum_insert hi]
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring_nf
      have hscaled : A * (θ * (J : ℝ)) ≤ A * (12 * ∑ i ∈ S w, r w i) :=
        mul_le_mul_of_nonneg_left hsum_boundR hA.le
      have harg : -A * (∑ i ∈ S w, r w i) / 2 ≤
          -A * θ * (J : ℝ) / 24 := by
        nlinarith [hscaled]
      have hfirst :
          ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) ≤ C := by
        apply ENNReal.ofReal_le_ofReal
        exact (Real.exp_le_exp.mpr harg)
      have hsplit :
          ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i))) =
            ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) *
              ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← Real.exp_add]
        ring
      have hweight :
          (∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i / 2))) = weight w := by
        rw [show S w = Finset.univ.filter (fun i => ∃ h : ℕ+, w i = some h) by rfl]
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : ∃ h : ℕ+, w i = some h
        · obtain ⟨h, hwi⟩ := his
          simp [r, rN, hwi]
        · have hnone : w i = none := by
            cases hwi : w i with
            | none => rfl
            | some h => exact (his ⟨h, hwi⟩).elim
          simp [hnone]
      have hhalf_prod :
          (∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i / 2))) =
            ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) := by
        induction S w using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.prod_insert hi, ih, ← ENNReal.ofReal_mul (by positivity)]
            simp only [Finset.sum_insert hi]
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring_nf
      calc
        P (I w) ≤ ∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i)) := hprod_le
        _ = ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i))) := hexp_prod
        _ = ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) *
            ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) := hsplit
        _ ≤ C * ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) :=
          mul_le_mul_left hfirst _
        _ = C * weight w := by rw [← hhalf_prod, hweight]
    · simp only [K]
      rw [dite_eq_right hadm]
      simp
  calc
    P {ω | θ * (J : ℝ) ≤
        (Set.ncard {i : Fin J | ω ∈ failure i} : ℝ)} ≤ P (⋃ w, K w) :=
      measure_mono hcover
    _ ≤ ∑' w, P (K w) := measure_iUnion_le _
    _ ≤ ∑' w, C * weight w := ENNReal.tsum_le_tsum hfixed
    _ = C * ∑' w, weight w := ENNReal.tsum_mul_left
    _ = C * ENNReal.ofReal (((1 - Real.exp (-A / 2))⁻¹) ^ J) := by
      rw [tsum_optional_witness_weights J A hA]
    _ = ENNReal.ofReal (Real.exp
        (-((A * θ / 24) + Real.log (1 - Real.exp (-A / 2))) * (J : ℝ))) := by
      have hpos : 0 < 1 - Real.exp (-A / 2) := by
        rw [sub_pos]
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      have hqpos : 0 < (1 - Real.exp (-A / 2))⁻¹ := inv_pos.mpr hpos
      have hinv : (1 - Real.exp (-A / 2))⁻¹ =
          Real.exp (-Real.log (1 - Real.exp (-A / 2))) := by
        rw [Real.exp_neg, Real.exp_log hpos]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hinv, ← Real.exp_nat_mul]
      rw [← Real.exp_add]
      congr 1
      ring


end SubdiffusiveProcess
