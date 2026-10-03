module

public import Mathlib
public import SubdiffusiveProcess.Gluing.Cutoff

@[expose] public section

/-!
# Gluing: the `L¹` bound for the partial derivatives of the cell cutoffs
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ}

theorem abs_deriv_gcEta_le {T : ℝ} (hT : ∀ s, |deriv Real.smoothTransition s| ≤ T) {α β ε : ℝ}
    (hε : 0 < ε) (t : ℝ) :
    |deriv (gcEta α β ε) t| ≤ T / ε *
      ((Icc (α + ε) (α + 2 * ε)).indicator (fun _ => (1 : ℝ)) t +
        (Icc (β - 2 * ε) (β - ε)).indicator (fun _ => (1 : ℝ)) t) := by
  rw [(hasDerivAt_gcEta α β ε t hε).deriv]
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hT 0)
  set u1 := (t - α) / ε - 1 with hu1
  set u2 := (β - t) / ε - 1 with hu2
  have hA0 := Real.smoothTransition.nonneg u1
  have hA1 := Real.smoothTransition.le_one u1
  have hB0 := Real.smoothTransition.nonneg u2
  have hB1 := Real.smoothTransition.le_one u2
  have ha1 : |deriv Real.smoothTransition u1 / ε| ≤
      T / ε * (Icc (α + ε) (α + 2 * ε)).indicator (fun _ => (1 : ℝ)) t := by
    by_cases hm : t ∈ Icc (α + ε) (α + 2 * ε)
    · rw [Set.indicator_of_mem hm, mul_one, abs_div, abs_of_pos hε]
      exact div_le_div_of_nonneg_right (hT _) hε.le
    · rw [Set.indicator_of_notMem hm, mul_zero]
      have : deriv Real.smoothTransition u1 = 0 := by
        apply deriv_st_eq_zero
        simp only [mem_Icc, not_and_or, not_le] at hm
        rcases hm with h | h
        · left
          rw [hu1, sub_nonpos, div_le_one hε]; linarith
        · right
          rw [hu1, le_sub_iff_add_le, le_div_iff₀ hε]; linarith
      rw [this]; simp
  have ha2 : |deriv Real.smoothTransition u2 / ε| ≤
      T / ε * (Icc (β - 2 * ε) (β - ε)).indicator (fun _ => (1 : ℝ)) t := by
    by_cases hm : t ∈ Icc (β - 2 * ε) (β - ε)
    · rw [Set.indicator_of_mem hm, mul_one, abs_div, abs_of_pos hε]
      exact div_le_div_of_nonneg_right (hT _) hε.le
    · rw [Set.indicator_of_notMem hm, mul_zero]
      have : deriv Real.smoothTransition u2 = 0 := by
        apply deriv_st_eq_zero
        simp only [mem_Icc, not_and_or, not_le] at hm
        rcases hm with h | h
        · right
          rw [hu2, le_sub_iff_add_le, le_div_iff₀ hε]; linarith
        · left
          rw [hu2, sub_nonpos, div_le_one hε]; linarith
      rw [this]; simp
  calc |deriv Real.smoothTransition u1 / ε * Real.smoothTransition u2 -
        Real.smoothTransition u1 * (deriv Real.smoothTransition u2 / ε)|
      ≤ |deriv Real.smoothTransition u1 / ε * Real.smoothTransition u2| +
        |Real.smoothTransition u1 * (deriv Real.smoothTransition u2 / ε)| := abs_sub _ _
    _ ≤ |deriv Real.smoothTransition u1 / ε| + |deriv Real.smoothTransition u2 / ε| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hB0]
        gcongr <;> nlinarith [abs_nonneg (deriv Real.smoothTransition u1 / ε),
          abs_nonneg (deriv Real.smoothTransition u2 / ε)]
    _ ≤ _ := by linarith

/-- The two boxes carrying the derivative of `gcTheta` in direction `j`. -/
def gcL1 (c : Fin d → ℝ) (h δ : ℝ) (j : Fin d) : Set (Fin d → ℝ) :=
  Icc (Function.update (fun k => c k - h) j (c j - h + δ * h))
    (Function.update (fun k => c k + h) j (c j - h + 2 * (δ * h)))

def gcL2 (c : Fin d → ℝ) (h δ : ℝ) (j : Fin d) : Set (Fin d → ℝ) :=
  Icc (Function.update (fun k => c k - h) j (c j + h - 2 * (δ * h)))
    (Function.update (fun k => c k + h) j (c j + h - δ * h))

theorem mem_gcL1_iff (c : Fin d → ℝ) (h δ : ℝ) (j : Fin d) (x : Fin d → ℝ) :
    x ∈ gcL1 c h δ j ↔ (x j ∈ Icc (c j - h + δ * h) (c j - h + 2 * (δ * h))) ∧
      ∀ i, i ≠ j → x i ∈ Icc (c i - h) (c i + h) := by
  classical
  unfold gcL1
  rw [mem_Icc, Pi.le_def, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by simpa using h1 j, by simpa using h2 j⟩, fun i hi => ⟨?_, ?_⟩⟩
    · simpa [Function.update_of_ne hi] using h1 i
    · simpa [Function.update_of_ne hi] using h2 i
  · rintro ⟨hj, hi⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hij : i = j
      · subst hij; simpa using hj.1
      · simpa [Function.update_of_ne hij] using (hi i hij).1
    · by_cases hij : i = j
      · subst hij; simpa using hj.2
      · simpa [Function.update_of_ne hij] using (hi i hij).2

theorem mem_gcL2_iff (c : Fin d → ℝ) (h δ : ℝ) (j : Fin d) (x : Fin d → ℝ) :
    x ∈ gcL2 c h δ j ↔ (x j ∈ Icc (c j + h - 2 * (δ * h)) (c j + h - δ * h)) ∧
      ∀ i, i ≠ j → x i ∈ Icc (c i - h) (c i + h) := by
  classical
  unfold gcL2
  rw [mem_Icc, Pi.le_def, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by simpa using h1 j, by simpa using h2 j⟩, fun i hi => ⟨?_, ?_⟩⟩
    · simpa [Function.update_of_ne hi] using h1 i
    · simpa [Function.update_of_ne hi] using h2 i
  · rintro ⟨hj, hi⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hij : i = j
      · subst hij; simpa using hj.1
      · simpa [Function.update_of_ne hij] using (hi i hij).1
    · by_cases hij : i = j
      · subst hij; simpa using hj.2
      · simpa [Function.update_of_ne hij] using (hi i hij).2

/-- Pointwise bound of the directional derivative of the cutoff by the two layer indicators. -/
theorem abs_fderiv_gcTheta_le {T : ℝ} (hT : ∀ s, |deriv Real.smoothTransition s| ≤ T)
    {c : Fin d → ℝ} {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (j : Fin d) (x : Fin d → ℝ) :
    |fderiv ℝ (gcTheta c h δ) x (Pi.single j 1)| ≤ T / (δ * h) *
      ((gcL1 c h δ j).indicator (fun _ => (1 : ℝ)) x +
        (gcL2 c h δ j).indicator (fun _ => (1 : ℝ)) x) := by
  classical
  have hε : 0 < δ * h := mul_pos hδ hh
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hT 0)
  have hform := fderiv_prod_coord' (f := fun k => gcEta (c k - h) (c k + h) (δ * h))
    (fun k => gcEta_contDiff _ _ _) x j
  have hrhs_nonneg : 0 ≤ T / (δ * h) *
      ((gcL1 c h δ j).indicator (fun _ => (1 : ℝ)) x +
        (gcL2 c h δ j).indicator (fun _ => (1 : ℝ)) x) := by
    have h1 : 0 ≤ (gcL1 c h δ j).indicator (fun _ => (1 : ℝ)) x :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have h2 : 0 ≤ (gcL2 c h δ j).indicator (fun _ => (1 : ℝ)) x :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) x
    positivity
  show |fderiv ℝ (fun y : Fin d → ℝ => ∏ k, gcEta (c k - h) (c k + h) (δ * h) (y k)) x
    (Pi.single j 1)| ≤ _
  rw [hform, abs_mul]
  set P := ∏ i ∈ Finset.univ.erase j, gcEta (c i - h) (c i + h) (δ * h) (x i) with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => gcEta_nonneg _ _ _ _
  have hP1 : P ≤ 1 := Finset.prod_le_one₀ (fun i _ => gcEta_nonneg _ _ _ _)
    fun i _ => gcEta_le_one _ _ _ _
  by_cases hok : ∀ i, i ≠ j → x i ∈ Icc (c i - h) (c i + h)
  · have hd := abs_deriv_gcEta_le hT hε (α := c j - h) (β := c j + h) (x j)
    have e1 : (Icc (c j - h + δ * h) (c j - h + 2 * (δ * h))).indicator (fun _ => (1 : ℝ)) (x j) =
        (gcL1 c h δ j).indicator (fun _ => (1 : ℝ)) x := by
      by_cases hm : x j ∈ Icc (c j - h + δ * h) (c j - h + 2 * (δ * h))
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((mem_gcL1_iff _ _ _ _ _).2 ⟨hm, hok⟩)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem]
        intro hx; exact hm ((mem_gcL1_iff _ _ _ _ _).1 hx).1
    have e2 : (Icc (c j + h - 2 * (δ * h)) (c j + h - δ * h)).indicator (fun _ => (1 : ℝ)) (x j) =
        (gcL2 c h δ j).indicator (fun _ => (1 : ℝ)) x := by
      by_cases hm : x j ∈ Icc (c j + h - 2 * (δ * h)) (c j + h - δ * h)
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((mem_gcL2_iff _ _ _ _ _).2 ⟨hm, hok⟩)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem]
        intro hx; exact hm ((mem_gcL2_iff _ _ _ _ _).1 hx).1
    have e1' : c j - h + δ * h = c j - h + δ * h := rfl
    have hd' : |deriv (gcEta (c j - h) (c j + h) (δ * h)) (x j)| ≤ T / (δ * h) *
        ((gcL1 c h δ j).indicator (fun _ => (1 : ℝ)) x +
          (gcL2 c h δ j).indicator (fun _ => (1 : ℝ)) x) := by
      rw [← e1, ← e2]
      have : c j - h + δ * h = (c j - h) + δ * h := rfl
      exact hd
    calc |deriv (gcEta (c j - h) (c j + h) (δ * h)) (x j)| * |P|
        ≤ |deriv (gcEta (c j - h) (c j + h) (δ * h)) (x j)| * 1 := by
          rw [abs_of_nonneg hP0]
          exact mul_le_mul_of_nonneg_left hP1 (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hd'
  · have hP_zero : P = 0 := by
      push_neg at hok
      obtain ⟨i, hij, hi⟩ := hok
      refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩) ?_
      rw [mem_Icc, not_and_or, not_le, not_le] at hi
      rcases hi with h1 | h1
      · exact gcEta_eq_zero_of_le hε (by linarith)
      · exact gcEta_eq_zero_of_ge hε (by linarith)
    rw [hP_zero]
    simpa using hrhs_nonneg

theorem volume_real_gcL1 (c : Fin d → ℝ) {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (j : Fin d) :
    volume.real (gcL1 c h δ j) = δ * h * (2 * h) ^ (d - 1) := by
  classical
  have hle : Function.update (fun k => c k - h) j (c j - h + δ * h) ≤
      Function.update (fun k => c k + h) j (c j - h + 2 * (δ * h)) := by
    intro k
    by_cases hk : k = j
    · subst hk; simp; nlinarith [mul_pos hδ hh]
    · simp [Function.update_of_ne hk]; linarith
  unfold gcL1
  rw [Measure.real, Real.volume_Icc_pi_toReal hle]
  rw [Fintype.prod_eq_mul_prod_compl j]
  have h1 : (Function.update (fun k => c k + h) j (c j - h + 2 * (δ * h)) j -
      Function.update (fun k => c k - h) j (c j - h + δ * h) j) = δ * h := by
    simp; ring
  have h2 : ∀ i ∈ ({j}ᶜ : Finset (Fin d)),
      (Function.update (fun k => c k + h) j (c j - h + 2 * (δ * h)) i -
        Function.update (fun k => c k - h) j (c j - h + δ * h) i) = 2 * h := by
    intro i hi
    have hij : i ≠ j := by simpa using hi
    simp [Function.update_of_ne hij]; ring
  rw [h1, Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_compl, Finset.card_singleton,
    Fintype.card_fin]

theorem volume_real_gcL2 (c : Fin d → ℝ) {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (j : Fin d) :
    volume.real (gcL2 c h δ j) = δ * h * (2 * h) ^ (d - 1) := by
  classical
  have hle : Function.update (fun k => c k - h) j (c j + h - 2 * (δ * h)) ≤
      Function.update (fun k => c k + h) j (c j + h - δ * h) := by
    intro k
    by_cases hk : k = j
    · subst hk; simp; nlinarith [mul_pos hδ hh]
    · simp [Function.update_of_ne hk]; linarith
  unfold gcL2
  rw [Measure.real, Real.volume_Icc_pi_toReal hle]
  rw [Fintype.prod_eq_mul_prod_compl j]
  have h1 : (Function.update (fun k => c k + h) j (c j + h - δ * h) j -
      Function.update (fun k => c k - h) j (c j + h - 2 * (δ * h)) j) = δ * h := by
    simp; ring
  have h2 : ∀ i ∈ ({j}ᶜ : Finset (Fin d)),
      (Function.update (fun k => c k + h) j (c j + h - δ * h) i -
        Function.update (fun k => c k - h) j (c j + h - 2 * (δ * h)) i) = 2 * h := by
    intro i hi
    have hij : i ≠ j := by simpa using hi
    simp [Function.update_of_ne hij]; ring
  rw [h1, Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_compl, Finset.card_singleton,
    Fintype.card_fin]

theorem integrable_indicator_gcL1 (c : Fin d → ℝ) (h δ : ℝ) (j : Fin d) :
    Integrable ((gcL1 c h δ j).indicator (fun _ => (1 : ℝ))) := by
  unfold gcL1
  exact (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const isCompact_Icc.measure_lt_top.ne)

theorem integrable_indicator_gcL2 (c : Fin d → ℝ) (h δ : ℝ) (j : Fin d) :
    Integrable ((gcL2 c h δ j).indicator (fun _ => (1 : ℝ))) := by
  unfold gcL2
  exact (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const isCompact_Icc.measure_lt_top.ne)

/-- **`L¹` bound of the cutoff's partial derivatives, uniform in `δ`.** -/
theorem integral_abs_fderiv_gcTheta_le {T : ℝ} (hT : ∀ s, |deriv Real.smoothTransition s| ≤ T)
    {c : Fin d → ℝ} {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (j : Fin d) :
    ∫ x, |fderiv ℝ (gcTheta c h δ) x (Pi.single j 1)| ≤ 2 * T * (2 * h) ^ (d - 1) := by
  classical
  have hε : 0 < δ * h := mul_pos hδ hh
  have hint : Integrable (fun x => T / (δ * h) *
      ((gcL1 c h δ j).indicator (fun _ => (1 : ℝ)) x +
        (gcL2 c h δ j).indicator (fun _ => (1 : ℝ)) x)) :=
    ((integrable_indicator_gcL1 c h δ j).add (integrable_indicator_gcL2 c h δ j)).const_mul _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hint
    (Eventually.of_forall fun x => abs_fderiv_gcTheta_le hT hh hδ j x)).trans ?_
  rw [integral_const_mul, integral_add (integrable_indicator_gcL1 c h δ j)
    (integrable_indicator_gcL2 c h δ j)]
  have i1 : ∫ x, (gcL1 c h δ j).indicator (fun _ => (1 : ℝ)) x = volume.real (gcL1 c h δ j) :=
    integral_indicator_one (by unfold gcL1; exact measurableSet_Icc)
  have i2 : ∫ x, (gcL2 c h δ j).indicator (fun _ => (1 : ℝ)) x = volume.real (gcL2 c h δ j) :=
    integral_indicator_one (by unfold gcL2; exact measurableSet_Icc)
  rw [i1, i2, volume_real_gcL1 c hh hδ j, volume_real_gcL2 c hh hδ j]
  apply le_of_eq
  field_simp
  ring

end SubdiffusiveProcess.Gluing
