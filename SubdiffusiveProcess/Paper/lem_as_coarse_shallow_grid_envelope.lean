module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_numeric_tail
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The $L^p$ moment-to-tail step for one retained cell. -/
private theorem aux_shallow_grid_envelope_probability_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (p B T : ℝ)
    (hp : 0 < p) (hT : 0 < T)
    (_hX : AEStronglyMeasurable X P)
    (hLp : eLpNorm X (ENNReal.ofReal p) P ≤ ENNReal.ofReal B) :
    P {ω | T ≤ |X ω|} ≤ ENNReal.ofReal (B / T) ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hT0 : ENNReal.ofReal T ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hT
  have hpReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hLp' : eLpNorm X (ENNReal.ofReal p) P ^ p ≤ ENNReal.ofReal B ^ p := by
    gcongr
  have hmarkov :=
    meas_ge_le_mul_pow_eLpNorm_enorm P hp0 hptop (f := X) hT0 (by simp)
  have hbound :
      P {ω | ENNReal.ofReal T ≤ ‖X ω‖ₑ} ≤
        (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p := by
    calc
      P {ω | ENNReal.ofReal T ≤ ‖X ω‖ₑ} ≤
          (ENNReal.ofReal T)⁻¹ ^ p * eLpNorm X (ENNReal.ofReal p) P ^ p := by
            simpa [hpReal] using hmarkov
      _ ≤ (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p := by
            exact mul_le_mul_right hLp' _
  have hrhs :
      (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p = ENNReal.ofReal (B / T) ^ p := by
    rw [ENNReal.ofReal_div_of_pos hT]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hp)]
    congr 1
    rw [div_eq_mul_inv]
    simp [mul_comm]
  have hevent :
      {ω | T ≤ |X ω|} = {ω | ENNReal.ofReal T ≤ ‖X ω‖ₑ} := by
    ext ω
    change (T ≤ |X ω|) ↔ ENNReal.ofReal T ≤ ‖X ω‖ₑ
    rw [Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg (X ω))).symm
  rw [hevent]
  exact hbound.trans_eq hrhs

/-- The finite-grid Borel--Cantelli step directly from coordinate moment bounds.
The numerical series is kept explicit so that it can be discharged by the
separate retained-grid cardinality calculation. -/
theorem aux_shallow_grid_eventual_of_moments
    {Ω α : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : ℕ → Finset α)
    (X : ℕ → α → Ω → ℝ) (p : ℝ) (B T : ℕ → ℝ)
    (hp : 0 < p) (hT : ∀ k, 0 < T k)
    (hX : ∀ k i, i ∈ G k → AEStronglyMeasurable (X k i) P)
    (hLp : ∀ k i, i ∈ G k →
      eLpNorm (X k i) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (B k))
    (hsum : (∑' k : ℕ,
      (G k).card * (ENNReal.ofReal (B k / T k) ^ p)) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ G k, |X k i ω| < T k := by
  let bad : ℕ → α → Set Ω := fun k i => {ω | T k ≤ |X k i ω|}
  have hcell : ∀ k i, i ∈ G k →
      P (bad k i) ≤ ENNReal.ofReal (B k / T k) ^ p := by
    intro k i hi
    exact aux_shallow_grid_envelope_probability_tail P (X k i) p (B k)
      (T k) hp (hT k) (hX k i hi) (hLp k i hi)
  have hae := aux_lem_as_coarse_shallow_grid_numeric_tail_finite_grid_eventual
    P G bad (fun k => ENNReal.ofReal (B k / T k) ^ p) hcell hsum
  filter_upwards [hae] with ω hω
  exact hω.mono (fun k hk i hi => lt_of_not_ge (hk i hi))

/-- Absorb finitely many exceptional depths into one sample-dependent constant. -/
theorem aux_shallow_grid_global_constant_of_eventual
    {Ω α : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : ℕ → Finset α)
    (X : ℕ → α → Ω → ℝ) (T : ℕ → ℝ)
    (hT : ∀ k, 0 < T k)
    (hae : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ G k, |X k i ω| < T k) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, 1 ≤ K ∧
      ∀ k i, i ∈ G k → |X k i ω| ≤ K * T k := by
  filter_upwards [hae] with ω hω
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hω
  let K : ℝ := 1 + ∑ k ∈ Finset.range N,
    ∑ i ∈ G k, |X k i ω| / T k
  have hterm : ∀ k i, 0 ≤ |X k i ω| / T k := by
    intro k i
    exact div_nonneg (abs_nonneg _) (hT k).le
  have hK : 1 ≤ K := by
    dsimp [K]
    have hs : 0 ≤ ∑ k ∈ Finset.range N,
        ∑ i ∈ G k, |X k i ω| / T k := by
      apply Finset.sum_nonneg
      intro k hk
      exact Finset.sum_nonneg (fun i hi => hterm k i)
    linarith
  refine ⟨K, hK, ?_⟩
  intro k i hi
  by_cases hk : N ≤ k
  · have hsmall := (hN k hk) i hi
    calc
      |X k i ω| ≤ T k := hsmall.le
      _ = 1 * T k := by ring
      _ ≤ K * T k := mul_le_mul_of_nonneg_right hK (hT k).le
  · have hk' : k ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hk)
    have hinner : |X k i ω| / T k ≤
        ∑ j ∈ G k, |X k j ω| / T k :=
      Finset.single_le_sum (fun j hj => hterm k j) hi
    have houter : (∑ j ∈ G k, |X k j ω| / T k) ≤
        ∑ j ∈ Finset.range N, ∑ i ∈ G j, |X j i ω| / T j := by
      apply Finset.single_le_sum _ hk'
      intro j hj
      exact Finset.sum_nonneg (fun m hm => hterm j m)
    have hratio : |X k i ω| / T k ≤ K := by
      dsimp [K]
      linarith [hinner.trans houter]
    exact (div_le_iff₀ (hT k)).mp hratio

/-- The complete finite-grid almost-sure envelope under an explicit numeric
summability premise, which is available for the paper's retained grid. -/
theorem lem_as_coarse_shallow_grid_envelope
    {Ω α : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : ℕ → Finset α)
    (X : ℕ → α → Ω → ℝ) (p : ℝ) (B T : ℕ → ℝ)
    (hp : 0 < p) (hT : ∀ k, 0 < T k)
    (hX : ∀ k i, i ∈ G k → AEStronglyMeasurable (X k i) P)
    (hLp : ∀ k i, i ∈ G k →
      eLpNorm (X k i) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (B k))
    (hsum : (∑' k : ℕ,
      (G k).card * (ENNReal.ofReal (B k / T k) ^ p)) ≠ ∞) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, 1 ≤ K ∧
      ∀ k i, i ∈ G k → |X k i ω| ≤ K * T k := by
  apply aux_shallow_grid_global_constant_of_eventual P G X T hT
  exact aux_shallow_grid_eventual_of_moments P G X p B T hp hT hX hLp hsum

end SubdiffusiveProcess.Paper
