module

public import SubdiffusiveProcess.Paper.lem_as_regularity_reference_ratio
public import SubdiffusiveProcess.Analysis.ReflectedScaleWindow

@[expose] public section

/-! The original error-score budget controls the reference ratios in a native
iteration window. This is a pointwise consequence of the signed-level ratio
bound, without a stopping-time or regularity assumption.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- Reversing a positive ratio preserves a symmetric exponential bound. -/
theorem aux_lem_as_regularity_native_reference_reverse (a b K : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (h : Real.exp (-K) ≤ a / b ∧ a / b ≤ Real.exp K) :
    Real.exp (-K) ≤ b / a ∧ b / a ≤ Real.exp K := by
  have hlo := inv_anti₀ (div_pos ha hb) h.2
  have hhi := inv_anti₀ (Real.exp_pos (-K)) h.1
  rw [inv_div, ← Real.exp_neg] at hlo hhi
  rw [neg_neg] at hhi
  exact ⟨hlo, hhi⟩

/-- Native score budgets bound both directions of every reference ratio used by iteration. -/
theorem lem_as_regularity_native_reference {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N m n j : ℕ) (hnj : n ≤ j) (hjm : j + 5 ≤ m)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (s eps : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (F P R D : ℕ → Vec d → ℝ≥0∞) (Z : ℕ → Vec d → ℝ)
    (good : ℕ → Vec d → Prop) (hPS : primitive_scores d M s eps eta F P R D Z good)
    (w : SpatialCoordinates d) (lam : ℝ) (hlam : 0 ≤ lam)
    (hdelta : M.delta ^ 2 ≤ 2 * lam)
    (hfin : ∀ k : ℕ, k ≤ m → D k ((3 : ℝ) ^ N • w) ≠ ⊤)
    (hsum : (∑ k ∈ Finset.Icc n m, (D k ((3 : ℝ) ^ N • w)).toReal) ≤
      lam * ((m : ℝ) - n)) :
    Real.exp (-(4 * (lam * ((m : ℝ) - n)))) ≤
        aux_in_deterministic_onestep_sref M H omega N ((N : ℤ) - (j + 2 : ℕ)) w /
          aux_in_deterministic_onestep_sref M H omega N ((N : ℤ) - m) w ∧
      aux_in_deterministic_onestep_sref M H omega N ((N : ℤ) - (j + 2 : ℕ)) w /
          aux_in_deterministic_onestep_sref M H omega N ((N : ℤ) - m) w ≤
        Real.exp (4 * (lam * ((m : ℝ) - n))) := by
  have hnm : n ≤ m := by omega
  have hlen : 0 ≤ (m : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast hnm)
  let S := Finset.Icc ((N : ℤ) - m) ((N : ℤ) - n)
  have hsub : Finset.Ico ((N : ℤ) - m) ((N : ℤ) - (j + 2 : ℕ)) ⊆ S := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
    exact Finset.mem_Icc.mpr ⟨hlo, by omega⟩
  have hsfin : ∀ i ∈ S, D ((N : ℤ) - i).toNat ((3 : ℝ) ^ N • w) ≠ ⊤ := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
    exact hfin _ (by omega)
  have hSig : (∑ i ∈ S, (D ((N : ℤ) - i).toNat ((3 : ℝ) ^ N • w)).toReal) ≤
      lam * ((m : ℝ) - n) := by
    rw [show S = Finset.Icc ((N : ℤ) - m) ((N : ℤ) - n) from rfl,
      sum_reflected_scale_window N n m hnm (fun k => (D k ((3 : ℝ) ^ N • w)).toReal)]
    exact hsum
  have hrat := lem_as_regularity_reference_ratio M Rm H omega N eta hEta s eps hs
    F P R D Z good hPS w ((N : ℤ) - m) ((N : ℤ) - (j + 2 : ℕ))
    (by omega) (by omega) S hsub hsfin (lam * ((m : ℝ) - n)) hSig
  have hrev := aux_lem_as_regularity_native_reference_reverse _ _ _
    (aux_in_deterministic_onestep_sref_pos M H omega N _ w)
    (aux_in_deterministic_onestep_sref_pos M H omega N _ w) hrat
  have hgap : ((((N : ℤ) - (j + 2 : ℕ)) - ((N : ℤ) - m) : ℤ) : ℝ) ≤ (m : ℝ) - n := by
    have hjn : (n : ℝ) ≤ (j : ℝ) + 2 := by exact_mod_cast (show n ≤ j + 2 by omega)
    push_cast
    linarith only [hjn]
  have hrate : ((((N : ℤ) - (j + 2 : ℕ)) - ((N : ℤ) - m) : ℤ) : ℝ) * M.delta ^ 2 +
      2 * (lam * ((m : ℝ) - n)) ≤ 4 * (lam * ((m : ℝ) - n)) := by
    have h1 := mul_le_mul_of_nonneg_right hgap (sq_nonneg M.delta)
    have h2 := mul_le_mul_of_nonneg_left hdelta hlen
    nlinarith only [h1, h2]
  exact ⟨(Real.exp_le_exp.mpr (neg_le_neg hrate)).trans hrev.1,
    hrev.2.trans (Real.exp_le_exp.mpr hrate)⟩

end Paper
