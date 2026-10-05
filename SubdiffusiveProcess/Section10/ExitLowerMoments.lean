module

public import SubdiffusiveProcess.Section10.ExitTailMomentsPhysical

@[expose] public section

/-! Fast-exit complement at a time fixed independently of the environment.
The probability kernels, fast-exit estimate and measurable infimum envelope
are explicit inputs. No mean-exit lower bound or Jensen argument is used. -/
open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitLowerMoments

/-- A deterministic time depending on the averaged fast-exit coefficient. -/
def lowerTime (M : ℝ≥0) : ℝ≥0 := ((2 * M)⁻¹) ^ (2 : ℕ)

lemma lowerTime_pos (M : ℝ≥0) (hM : 1 ≤ M) : 0 < lowerTime M := by
  unfold lowerTime
  exact pow_pos (inv_pos.mpr (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hM))) _

lemma mean_mul_sqrt_lowerTime (M : ℝ≥0) (hM : 1 ≤ M) :
    (M : ℝ≥0∞) * (NNReal.sqrt (lowerTime M) : ℝ≥0∞) = 1 / 2 := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hM))
  have hnn : M * NNReal.sqrt (lowerTime M) = (1 / 2 : ℝ≥0) := by
    apply NNReal.coe_injective
    simp only [lowerTime, NNReal.sqrt_sq, NNReal.coe_mul, NNReal.coe_inv,
      NNReal.coe_ofNat, NNReal.coe_div, NNReal.coe_one]
    field_simp
  rw [← ENNReal.coe_mul, hnn]
  norm_num

/-- Complementation of the literal measurable exit event. -/
lemma survival_lower_of_fast_exit {W : Type*} [MeasurableSpace W]
    (mu : Measure W) [IsProbabilityMeasure mu] (tau : W → ℝ≥0∞)
    (htau : Measurable tau) (c : ℝ≥0) (b : ℝ≥0∞)
    (hfast : mu {w | tau w ≤ (c : ℝ≥0∞)} ≤ b) :
    1 - b ≤ mu {w | (c : ℝ≥0∞) < tau w} := by
  have hE : MeasurableSet {w | tau w ≤ (c : ℝ≥0∞)} :=
    measurableSet_le htau measurable_const
  have hcomp : {w | tau w ≤ (c : ℝ≥0∞)}ᶜ = {w | (c : ℝ≥0∞) < tau w} := by
    ext w
    simp only [Set.mem_compl_iff, mem_ofPred_eq, not_le]
  apply tsub_le_iff_right.mpr
  calc (1 : ℝ≥0∞) = mu {w | (c : ℝ≥0∞) < tau w} + mu {w | tau w ≤ (c : ℝ≥0∞)} := by
        rw [← hcomp, add_comm, measure_add_measure_compl hE, measure_univ]
    _ ≤ _ := add_le_add_right hfast _

/-- Average inf-start survival using only the first moment of the fast-exit
coefficient, at the deterministic time lowerTime M. -/
theorem averaged_survival_lower {Ω α W : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace W]
    (nu : Measure Ω) [IsProbabilityMeasure nu]
    (law : Ω → Kernel α W) [∀ omega, IsMarkovKernel (law omega)]
    (V : Set α) (tau : W → ℝ≥0∞) (htau : Measurable tau)
    (K : Ω → ℝ≥0) (hK : Measurable K) (M : ℝ≥0) (hM : 1 ≤ M)
    (hmean : (∫⁻ omega, (K omega : ℝ≥0∞) ∂nu) ≤ (M : ℝ≥0∞))
    (hfast : ∀ omega, ∀ x ∈ V, ∀ t : ℝ≥0, 0 < t →
      law omega x {w | tau w ≤ (t : ℝ≥0∞)} ≤
        ENNReal.ofReal ((K omega : ℝ) * Real.sqrt (t : ℝ)))
    (henv : Measurable (fun omega => ⨅ x ∈ V,
      law omega x {w | (lowerTime M : ℝ≥0∞) < tau w})) :
    (1 / 2 : ℝ≥0∞) ≤ ∫⁻ omega, (⨅ x ∈ V,
      law omega x {w | (lowerTime M : ℝ≥0∞) < tau w}) ∂nu := by
  let A : Ω → ℝ≥0∞ := fun omega => ⨅ x ∈ V,
    law omega x {w | (lowerTime M : ℝ≥0∞) < tau w}
  let b : Ω → ℝ≥0∞ := fun omega =>
    (K omega : ℝ≥0∞) * (NNReal.sqrt (lowerTime M) : ℝ≥0∞)
  have hb : Measurable b := hK.coe_nnreal_ennreal.mul_const _
  have hpoint : ∀ omega, (1 : ℝ≥0∞) ≤ A omega + b omega := by
    intro omega
    apply tsub_le_iff_right.mp
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    apply survival_lower_of_fast_exit _ tau htau (lowerTime M) (b omega)
    have hf := hfast omega x hx (lowerTime M) (lowerTime_pos M hM)
    have heq : ENNReal.ofReal ((K omega : ℝ) * Real.sqrt (lowerTime M : ℝ)) = b omega := by
      rw [← Real.coe_sqrt, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]
      exact ENNReal.coe_mul _ _
    exact hf.trans_eq heq
  have hbmean : (∫⁻ omega, b omega ∂nu) ≤ (1 / 2 : ℝ≥0∞) := by
    calc (∫⁻ omega, b omega ∂nu) =
        (NNReal.sqrt (lowerTime M) : ℝ≥0∞) * ∫⁻ omega, (K omega : ℝ≥0∞) ∂nu := by
          simp only [b, mul_comm _ (NNReal.sqrt (lowerTime M) : ℝ≥0∞)]
          exact lintegral_const_mul _ hK.coe_nnreal_ennreal
      _ ≤ (NNReal.sqrt (lowerTime M) : ℝ≥0∞) * (M : ℝ≥0∞) := mul_le_mul_right hmean _
      _ = 1 / 2 := by rw [mul_comm]; exact mean_mul_sqrt_lowerTime M hM
  have hsum : (1 : ℝ≥0∞) ≤ (∫⁻ omega, A omega ∂nu) + 1 / 2 := by
    calc (1 : ℝ≥0∞) = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂nu := by rw [lintegral_one, measure_univ]
      _ ≤ ∫⁻ omega, A omega + b omega ∂nu := lintegral_mono hpoint
      _ = (∫⁻ omega, A omega ∂nu) + ∫⁻ omega, b omega ∂nu := lintegral_add_left henv _
      _ ≤ _ := add_le_add_right hbmean _
  have h := tsub_le_iff_right.mpr hsum
  norm_num at h ⊢
  exact h

/-- Literal event-to-powered-moment lower bound, also for p below one. -/
lemma survival_mul_rpow_le_moment {W : Type*} [MeasurableSpace W]
    (mu : Measure W) (tau : W → ℝ≥0∞) (htau : Measurable tau)
    (c : ℝ≥0) (p : ℝ) (hp : 0 < p) :
    (c : ℝ≥0∞) ^ p * mu {w | (c : ℝ≥0∞) < tau w} ≤ ∫⁻ w, tau w ^ p ∂mu := by
  let E := {w | (c : ℝ≥0∞) < tau w}
  have hE : MeasurableSet E := measurableSet_lt measurable_const htau
  calc (c : ℝ≥0∞) ^ p * mu E = ∫⁻ w, E.indicator (fun _ => (c : ℝ≥0∞) ^ p) w ∂mu := by
        rw [lintegral_indicator hE, setLIntegral_const]
    _ ≤ ∫⁻ w, tau w ^ p ∂mu := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ E
      · rw [Set.indicator_of_mem hw]
        exact ENNReal.rpow_le_rpow (le_of_lt hw) hp.le
      · rw [Set.indicator_of_notMem hw]
        exact bot_le

/-- Infima commute with the finite positive factor. No measurable moment
envelope is required for this nonnegative lintegral lower inequality. -/
theorem averaged_moment_lower {Ω α W : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace W]
    (nu : Measure Ω) (law : Ω → Kernel α W) (V : Set α)
    (tau : W → ℝ≥0∞) (htau : Measurable tau) (c : ℝ≥0) (p : ℝ) (hp : 0 < p)
    (henv : Measurable (fun omega => ⨅ x ∈ V, law omega x {w | (c : ℝ≥0∞) < tau w}))
    (hsurv : (1 / 2 : ℝ≥0∞) ≤ ∫⁻ omega, (⨅ x ∈ V,
      law omega x {w | (c : ℝ≥0∞) < tau w}) ∂nu) :
    ENNReal.ofReal ((c : ℝ) ^ p / 2) ≤ ∫⁻ omega, (⨅ x ∈ V,
      ∫⁻ w, tau w ^ p ∂law omega x) ∂nu := by
  have hcoef : ENNReal.ofReal ((c : ℝ) ^ p) = (c : ℝ≥0∞) ^ p := by
    calc ENNReal.ofReal ((c : ℝ) ^ p) = ENNReal.ofReal (c : ℝ) ^ p :=
        (ENNReal.ofReal_rpow_of_nonneg c.property hp.le).symm
      _ = (c : ℝ≥0∞) ^ p := by congr 1; exact ENNReal.ofReal_coe_nnreal
  calc ENNReal.ofReal ((c : ℝ) ^ p / 2) = (c : ℝ≥0∞) ^ p * (1 / 2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_ofNat, hcoef, div_eq_mul_inv, one_div]
    _ ≤ (c : ℝ≥0∞) ^ p * ∫⁻ omega, (⨅ x ∈ V,
        law omega x {w | (c : ℝ≥0∞) < tau w}) ∂nu := mul_le_mul_right hsurv _
    _ = ∫⁻ omega, (c : ℝ≥0∞) ^ p * (⨅ x ∈ V,
        law omega x {w | (c : ℝ≥0∞) < tau w}) ∂nu := (lintegral_const_mul _ henv).symm
    _ ≤ ∫⁻ omega, (⨅ x ∈ V, ∫⁻ w, tau w ^ p ∂law omega x) ∂nu := by
      apply lintegral_mono
      intro omega
      apply le_iInf
      intro x
      apply le_iInf
      intro hx
      exact (mul_le_mul_right (iInf_le_of_le x (iInf_le _ hx)) _).trans
        (survival_mul_rpow_le_moment _ tau htau c p hp)

end SubdiffusiveProcess.Section10.ExitLowerMoments
