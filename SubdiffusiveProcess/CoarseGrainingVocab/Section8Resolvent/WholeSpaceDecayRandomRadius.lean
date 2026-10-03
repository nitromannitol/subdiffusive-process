module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.DepthGammaOne
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayExterior

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]



def wholeSpaceDecayRadius (R : ℝ) (D : Omega → ℕ) : Omega → ℝ :=
  fun omega ↦ R * (3 : ℝ) ^ D omega

omit [MeasurableSpace Omega] in


theorem le_wholeSpaceDecayRadius {R : ℝ} (hR : 0 ≤ R)
    (D : Omega → ℕ) (omega : Omega) :
    R ≤ wholeSpaceDecayRadius R D omega := by
  unfold wholeSpaceDecayRadius
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ D omega := one_le_pow₀ (by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hR



theorem measurable_wholeSpaceDecayRadius {R : ℝ} {D : Omega → ℕ}
    (hD : Measurable D) : Measurable (wholeSpaceDecayRadius R D) := by
  unfold wholeSpaceDecayRadius
  fun_prop

omit [MeasurableSpace Omega] in


private theorem max_log_wholeSpaceDecayRadius_sub_log_three
    {R : ℝ} (hR : 0 < R) (D : Omega → ℕ) (omega : Omega) :
    max (Real.log (wholeSpaceDecayRadius R D omega / R) - Real.log 3) 0 =
      Real.log 3 * depthObservable D omega := by
  have hlogThree : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hquotient : wholeSpaceDecayRadius R D omega / R =
      (3 : ℝ) ^ D omega := by
    unfold wholeSpaceDecayRadius
    field_simp
  rw [hquotient, Real.log_pow]
  by_cases hzero : D omega = 0
  · simp only [hzero, Nat.cast_zero, zero_mul, zero_sub, max_eq_right,
      neg_nonpos, hlogThree.le, depthObservable]
    norm_num
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [hn]
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hproduct : 0 ≤ (n : ℝ) * Real.log 3 :=
      mul_nonneg hnnonneg hlogThree.le
    rw [Nat.cast_succ]
    have hsub : ((n : ℝ) + 1) * Real.log 3 - Real.log 3 =
        (n : ℝ) * Real.log 3 := by ring
    rw [hsub, max_eq_left hproduct]
    unfold depthObservable
    rw [hn, Nat.cast_succ]
    have hdepth : max ((n : ℝ) + 1 - 1) 0 = (n : ℝ) := by
      rw [add_sub_cancel_right, max_eq_left hnnonneg]
    rw [hdepth]
    ring



theorem ogammaLE_log_wholeSpaceDecayRadius
    {μ : Measure Omega} [IsProbabilityMeasure μ]
    (D : Omega → ℕ) (hD : Measurable D)
    {R K r : ℝ} (hR : 0 < R) (hK : 1 ≤ K) (hr : 0 < r)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < D omega} ≤
        K * Real.exp (-(r * max ((q : ℝ) - 1) 0))) :
    SubdiffusiveProcess.OGammaLE μ 1
      (Real.log 3 * depthGammaOneScale K r)
      (fun omega ↦
        Real.log (wholeSpaceDecayRadius R D omega / R) - Real.log 3) := by
  have hbase := ogammaLE_one_depthObservable (μ := μ) hD hK hr htail
  have hlogThree : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hscale : 0 < depthGammaOneScale K r :=
    depthGammaOneScale_pos hK hr
  have hnormalized : ∀ omega,
      (Real.log 3 * depthGammaOneScale K r)⁻¹ *
          max (Real.log (wholeSpaceDecayRadius R D omega / R) -
            Real.log 3) 0 =
        (depthGammaOneScale K r)⁻¹ * max (depthObservable D omega) 0 := by
    intro omega
    rw [max_log_wholeSpaceDecayRadius_sub_log_three hR D omega,
      max_eq_left (depthObservable_nonneg D omega)]
    field_simp
  unfold SubdiffusiveProcess.OGammaLE at hbase ⊢
  simpa only [hnormalized] using hbase

omit [MeasurableSpace Omega] in


def wholeSpaceDecayFactor (C : ℝ) (X : Omega → ℝ) : Omega → ℝ :=
  fun omega ↦ Real.exp (C + X omega)

omit [MeasurableSpace Omega] in


theorem one_le_wholeSpaceDecayFactor {C : ℝ} (hC : 0 ≤ C)
    {X : Omega → ℝ} (hX : ∀ omega, 0 ≤ X omega) (omega : Omega) :
    1 ≤ wholeSpaceDecayFactor C X omega := by
  rw [wholeSpaceDecayFactor, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (add_nonneg hC (hX omega))

omit [MeasurableSpace Omega] in


theorem log_wholeSpaceDecayFactor_sub {C : ℝ} {X : Omega → ℝ}
    (omega : Omega) :
    Real.log (wholeSpaceDecayFactor C X omega) - C = X omega := by
  rw [wholeSpaceDecayFactor, Real.log_exp]
  ring



theorem ogammaLE_log_wholeSpaceDecayFactor_sub
    {mu : Measure Omega} {C A : ℝ} {X : Omega → ℝ}
    (hX : SubdiffusiveProcess.OGammaLE mu 1 A X) :
    SubdiffusiveProcess.OGammaLE mu 1 A
      (fun omega ↦ Real.log (wholeSpaceDecayFactor C X omega) - C) := by
  simpa only [log_wholeSpaceDecayFactor_sub] using hX

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
