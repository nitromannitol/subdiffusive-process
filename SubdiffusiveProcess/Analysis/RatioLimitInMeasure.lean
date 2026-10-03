module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! # Identification of an in-measure limit of ratios

If `aₙ → A` and `bₙ → B ≠ 0` almost surely and `aₙ / bₙ → R` in measure, then `R = A / B`
almost surely.  Nothing else is claimed. -/

open Filter MeasureTheory
open scoped Topology

namespace SubdiffusiveProcess

/-- An in-measure limit of ratios of almost surely convergent sequences is the ratio of limits. -/
theorem ae_eq_div_of_tendstoInMeasure_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (a b : ℕ → Ω → ℝ) (A B R : Ω → ℝ)
    (ha : ∀ᵐ ω ∂P, Tendsto (fun n => a n ω) atTop (𝓝 (A ω)))
    (hb : ∀ᵐ ω ∂P, B ω ≠ 0 ∧ Tendsto (fun n => b n ω) atTop (𝓝 (B ω)))
    (hR : TendstoInMeasure P (fun n ω => a n ω / b n ω) atTop R) :
    ∀ᵐ ω ∂P, R ω = A ω / B ω := by
  obtain ⟨ns, hns, hae⟩ := hR.exists_seq_tendsto_ae
  filter_upwards [ha, hb, hae] with ω haω hbω hRω
  have hdiv : Tendsto (fun n => a (ns n) ω / b (ns n) ω) atTop (𝓝 (A ω / B ω)) :=
    ((haω.comp hns.tendsto_atTop).div (hbω.2.comp hns.tendsto_atTop) hbω.1)
  exact tendsto_nhds_unique hRω hdiv

end SubdiffusiveProcess

namespace SubdiffusiveProcess

/-- If the in-measure limit of `aₙ/bₙ` lies in `(1/2, 2)` on a set, the almost sure limits of
`a` and `b` satisfy `B⁻¹ ≤ 2 A⁻¹` there. -/
theorem ae_inv_le_two_mul_inv_of_ratio_mem_Ioo {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (Good : Set Ω) (a b : ℕ → Ω → ℝ) (A B R : Ω → ℝ)
    (ha : ∀ᵐ ω ∂P, 0 < A ω ∧ Tendsto (fun n => a n ω) atTop (𝓝 (A ω)))
    (hb : ∀ᵐ ω ∂P, 0 < B ω ∧ Tendsto (fun n => b n ω) atTop (𝓝 (B ω)))
    (hR : TendstoInMeasure P (fun n ω => a n ω / b n ω) atTop R)
    (hGood : ∀ ω ∈ Good, R ω ∈ Set.Ioo (1 / 2 : ℝ) 2) :
    ∀ᵐ ω ∂P, ω ∈ Good → (B ω)⁻¹ ≤ 2 * (A ω)⁻¹ := by
  have hEq := ae_eq_div_of_tendstoInMeasure_div a b A B R
    (by filter_upwards [ha] with ω h; exact h.2)
    (by filter_upwards [hb] with ω h; exact ⟨h.1.ne', h.2⟩) hR
  filter_upwards [ha, hb, hEq] with ω haω hbω hEqω
  intro hG
  have hlt : A ω / B ω < 2 := hEqω ▸ (hGood ω hG).2
  have hA := haω.1
  have hB := hbω.1
  rw [div_lt_iff₀ hB] at hlt
  rw [inv_le_iff_one_le_mul₀ hB]
  have : 2 * (A ω)⁻¹ * B ω = 2 * B ω / A ω := by field_simp
  rw [this, le_div_iff₀ hA]
  linarith only [hlt]

end SubdiffusiveProcess
