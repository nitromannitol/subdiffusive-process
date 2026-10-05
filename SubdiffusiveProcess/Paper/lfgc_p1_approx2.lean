module

public import SubdiffusiveProcess.Paper.lfgc_p1_approx

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Approximants of the prefix sums: `L^p` error and sure convergence

The prefix sum minus its approximant is a sum over the level window of aux_lfgc_sum_band_summand errors, each
bounded by the band error `E_b 3^{-aH}` (while `H < m`) or the truncation error
`E_t 3^{-σ'(cL H + L0)}` (once `H ≥ m`); the window has at most `(2 + 2 buffer) D` levels.
On every sample where each aux_lfgc_sum_band_summand has its literal formula at the canonical sample and the drift
scores are finite, the approximants converge to the prefix sum.
-/

open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The prefix sum as a sum over its level window. -/
theorem aux_lfgc_p1_approx2_p1T_eq_pre (en nc ns : ℕ) (enDepth : Fin en → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (buffer : ℕ) (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) (m k : ℕ)
    (z : SpatialCoordinates d) (D : ℕ) (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D) :
    aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i =
      fun omega => ∑ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D (enDepth i.1.1),
        if 0 ≤ ((m + k : ℕ) : ℤ) - j then aux_lfgc_sum_band_summand i.2.2 Draw Z (m + k) j i.2.1.1 omega else 0 := by
  funext omega
  exact aux_lfgc_p1_index_p1T_eq_sum en nc ns enDepth cmpShift shift buffer Draw Z m k z D i omega

/-- `L^p` error of the approximants. -/
theorem lfgc_p1_approx2 [NeZero d] (M : GMCModel d) (s eps : ℝ) (m k buffer cL L0 e : ℕ)
    (w : SpatialCoordinates d) (b : Bool)
    (Y : Bool → ℤ → SpatialCoordinates d → ℕ → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) (p : ℝ) (hp : 1 ≤ p)
    {Eb Et a σ' : ℝ} (hEb : 0 ≤ Eb)
    (hYm : ∀ j h, AEStronglyMeasurable (Y b j w h) (chaosSampleLaw M).toMeasure)
    (hSm : ∀ j, AEStronglyMeasurable (aux_lfgc_sum_band_summand b Draw Z (m + k) j w) (chaosSampleLaw M).toMeasure)
    (hTm : ∀ j L, AEStronglyMeasurable (aux_lfgc_sum_trunc_summandTr b M s eps (m + k) j w L)
      (chaosSampleLaw M).toMeasure)
    (hYe : ∀ j h, j ≤ ((m + k : ℕ) : ℤ) → 1 ≤ h →
      eLpNorm (fun omega => aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega - Y b j w h omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Eb * (3 : ℝ) ^ (-(a * h))))
    (hTe : ∀ j L, j ≤ ((m + k : ℕ) : ℤ) →
      eLpNorm (fun omega => aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega -
          aux_lfgc_sum_trunc_summandTr b M s eps (m + k) j w L omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Et * (3 : ℝ) ^ (-(σ' * L))))
    (D H : ℕ) (hD : 1 ≤ D) (hDH : D ≤ H) :
    eLpNorm (fun omega => (∑ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e,
        if 0 ≤ ((m + k : ℕ) : ℤ) - j then aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega else 0) -
        aux_lfgc_p1_approx_p1U M s eps m k buffer cL L0 e w b Y D H omega)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2 + 2 * buffer) * D *
        max (Eb * (3 : ℝ) ^ (-(a * H))) (Et * (3 : ℝ) ^ (-(σ' * ((cL * H + L0 : ℕ) : ℝ))))) := by
  set μ := (chaosSampleLaw M).toMeasure
  set B := max (Eb * (3 : ℝ) ^ (-(a * H))) (Et * (3 : ℝ) ^ (-(σ' * ((cL * H + L0 : ℕ) : ℝ))))
  set g : ℤ → BilateralField d → ℝ := fun j omega =>
    if 0 ≤ ((m + k : ℕ) : ℤ) - j then
      aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega -
        (if H < m then Y b j w H omega else aux_lfgc_sum_trunc_summandTr b M s eps (m + k) j w (cL * H + L0) omega)
    else 0 with hg
  have hfun : (fun omega => (∑ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e,
        if 0 ≤ ((m + k : ℕ) : ℤ) - j then aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega else 0) -
        aux_lfgc_p1_approx_p1U M s eps m k buffer cL L0 e w b Y D H omega) =
      ∑ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e, g j := by
    funext omega
    rw [Finset.sum_apply]
    unfold aux_lfgc_p1_approx_p1U
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hg]
    split_ifs <;> ring
  have hgm : ∀ j, AEStronglyMeasurable (g j) μ := by
    intro j
    simp only [hg]
    split_ifs
    · exact (hSm j).sub (hYm j H)
    · exact (hSm j).sub (hTm j _)
    · exact aestronglyMeasurable_const
  have hgb : ∀ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e, eLpNorm (g j) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal B := by
    intro j _
    simp only [hg]
    by_cases hN : 0 ≤ ((m + k : ℕ) : ℤ) - j
    · have hjN : j ≤ ((m + k : ℕ) : ℤ) := by omega
      simp only [hN, ite_true]
      by_cases hHm : H < m
      · simp only [hHm, ite_true]
        exact (hYe j H hjN (by omega)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      · simp only [hHm, ite_false]
        exact (hTe j _ hjN).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    · simp only [hN, ite_false, eLpNorm_fun_zero]
      exact zero_le
  have h1p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hB0 : 0 ≤ B := le_trans (mul_nonneg hEb (Real.rpow_nonneg (by norm_num) _)) (le_max_left _ _)
  rw [hfun]
  refine (eLpNorm_sum_le h1p).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hgb).trans ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc := aux_lfgc_p1_approx_card_p1Pre_le (m + k) k buffer D e hD
  calc ((aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e).card : ℝ) * B ≤ (2 + 2 * buffer) * D * B :=
        mul_le_mul_of_nonneg_right hc hB0
    _ = _ := rfl

/-- Sure convergence of the approximants on samples with literal summands. -/
theorem aux_lfgc_p1_approx2_p1U_tendsto [NeZero d] (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (m k buffer cL L0 e : ℕ) (hcL : 1 ≤ cL) (w : SpatialCoordinates d) (b : Bool)
    (Y : Bool → ℤ → SpatialCoordinates d → ℕ → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) (D : ℕ)
    (omega : BilateralField d)
    (hform : ∀ j, j ≤ ((m + k : ℕ) : ℤ) →
      Draw (m + k) (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • w) omega =
        aux_lfgc_p_trunc_dfull M s (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • w) (aux_lfgc_layer_tail_canonEta (m + k) omega) ∧
      Z (m + k) (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • w) omega =
        aux_lfgc_p_trunc_zfull M s eps (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • w)
          (aux_lfgc_layer_tail_canonEta (m + k) omega) ∧
      Draw (m + k) (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • w) omega ≠ ⊤) :
    Tendsto (fun H => aux_lfgc_p1_approx_p1U M s eps m k buffer cL L0 e w b Y D H omega) atTop
      (𝓝 (∑ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e,
        if 0 ≤ ((m + k : ℕ) : ℤ) - j then aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega else 0)) := by
  have hL : Tendsto (fun H : ℕ => cL * H + L0) atTop atTop :=
    tendsto_atTop_atTop.mpr fun B => ⟨B, fun a ha => by nlinarith⟩
  have hlim : Tendsto (fun H => ∑ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e,
      if 0 ≤ ((m + k : ℕ) : ℤ) - j then aux_lfgc_sum_trunc_summandTr b M s eps (m + k) j w (cL * H + L0) omega
      else 0) atTop
      (𝓝 (∑ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e,
        if 0 ≤ ((m + k : ℕ) : ℤ) - j then aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega else 0)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    by_cases hN : 0 ≤ ((m + k : ℕ) : ℤ) - j
    · simp only [hN, ite_true]
      obtain ⟨h1, h2, h3⟩ := hform j (by omega)
      exact lfgc_sum_trunc b M s eps heps Draw Z (m + k) j w omega h1 h2 h3 hL
    · simp only [hN, ite_false]
      exact tendsto_const_nhds
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop m] with H hH
  unfold aux_lfgc_p1_approx_p1U
  refine Finset.sum_congr rfl fun j _ => ?_
  have hHm : ¬ H < m := by omega
  simp only [hHm, ite_false]

end SubdiffusiveProcess.Paper
