module

public import SubdiffusiveProcess.Analysis.RawLp

@[expose] public section

/-! Hölder-at-doubled-order transfer: a pointwise product bound with two
`2p`-controlled factors gives a single `p`-norm product bound, and when the two
factors carry opposite base-3 power rates the product bound is geometric with
the net rate. This is the moment-absorption step of MATH-FIXES Fix 6 (P:3555-3584):
"the layer-supremum estimate absorbs `S e^{CS}` into any reserved positive
fraction of the power of `r`". -/

open MeasureTheory
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Probability

/-- A pointwise product bound with two `2p`-controlled factors transfers to a
single `p`-norm product bound (Hölder at the doubled moment order). -/

theorem eLpNorm_le_of_ae_abs_le_mul
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {D U V : α → ℝ} (hUm : AEStronglyMeasurable U μ) (hVm : AEStronglyMeasurable V μ)
    (hDUV : ∀ᵐ x ∂μ, |D x| ≤ U x * V x)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (_hpt : p ≠ ⊤)
    {CU CV : ℝ}
    (hU : MeasureTheory.eLpNorm U (2 * p) μ ≤ ENNReal.ofReal CU)
    (hV : MeasureTheory.eLpNorm V (2 * p) μ ≤ ENNReal.ofReal CV) :
    RawLp.eLpNorm D p μ ≤ ENNReal.ofReal CU * ENNReal.ofReal CV := by
  haveI hHT : ENNReal.HolderTriple (2 * p) (2 * p) p := by
    refine ⟨?_⟩
    have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl h2')]
    rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) h2', one_mul]
  calc
    RawLp.eLpNorm D p μ ≤ RawLp.eLpNorm (fun x => U x * V x) p μ := by
      apply RawLp.eLpNorm_mono_ae
      filter_upwards [hDUV] with x hx
      calc ‖D x‖ = |D x| := Real.norm_eq_abs _
        _ ≤ U x * V x := hx
        _ ≤ |U x * V x| := le_abs_self _
        _ = ‖U x * V x‖ := (Real.norm_eq_abs _).symm
    _ = MeasureTheory.eLpNorm (fun x => U x * V x) p μ :=
      RawLp.eLpNorm_eq_guarded (hUm.mul hVm)
    _ ≤ (1 : ℝ≥0) * MeasureTheory.eLpNorm U (2 * p) μ *
        MeasureTheory.eLpNorm V (2 * p) μ := by
      have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := 2 * p) (q := 2 * p) (r := p)
        (fun a b : ℝ => a * b) (1 : ℝ≥0) continuous_mul hUm hVm
        (Filter.Eventually.of_forall fun x => by simp only [norm_mul, NNReal.coe_one, one_mul, le_refl])
      simpa only using h
    _ ≤ ENNReal.ofReal CU * ENNReal.ofReal CV := by
      simp only [ENNReal.coe_one, one_mul]
      exact mul_le_mul' hU hV

theorem eLpNorm_le_geometric_of_ae_abs_le_mul
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {D U V : α → ℝ} (hUm : AEStronglyMeasurable U μ) (hVm : AEStronglyMeasurable V μ)
    (hDUV : ∀ᵐ x ∂μ, |D x| ≤ U x * V x)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    {CU CV a1 a2 : ℝ} (hCU : 0 ≤ CU) (_hCV : 0 ≤ CV) (n : ℝ)
    (hU : MeasureTheory.eLpNorm U (2 * p) μ ≤ ENNReal.ofReal (CU * (3 : ℝ) ^ (-a1 * n)))
    (hV : MeasureTheory.eLpNorm V (2 * p) μ ≤ ENNReal.ofReal (CV * (3 : ℝ) ^ (a2 * n))) :
    RawLp.eLpNorm D p μ ≤ ENNReal.ofReal (CU * CV * (3 : ℝ) ^ (-(a1 - a2) * n)) := by
  have h := eLpNorm_le_of_ae_abs_le_mul hUm hVm hDUV hp1 hpt hU hV
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [show CU * (3 : ℝ) ^ (-a1 * n) * (CV * (3 : ℝ) ^ (a2 * n)) =
      CU * CV * ((3 : ℝ) ^ (-a1 * n) * (3 : ℝ) ^ (a2 * n)) by ring,
    ← Real.rpow_add h3]
  congr 2
  ring


end SubdiffusiveProcess.Probability
