module

public import SubdiffusiveProcess.Paper.lfgc_p1_wit

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The `L^p` error hypothesis of the witness. -/
theorem lfgc_p1_main [NeZero d] (M : GMCModel d) (s eps : ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞) (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (en nc ns : ℕ) (enDepth : Fin en → ℕ) (cmpShift : Fin nc → Vec d) (shift : Fin ns → Vec d)
    (buffer m k : ℕ) (z : Vec d) (cL L0 : ℕ)
    (Y : Bool → ℤ → Vec d → ℕ → BilateralField d → ℝ) (p : ℝ) (hp : 1 ≤ p)
    {Eb Et a' Merr κ R : ℝ} (hEb0 : 0 ≤ Eb) (hEt0 : 0 ≤ Et)
    (hYm : ∀ b j w h, AEStronglyMeasurable (Y b j w h) (chaosSampleLaw M).toMeasure)
    (hSm : ∀ b j w, AEStronglyMeasurable (aux_lfgc_sum_band_summand b Draw Z (m + k) j w) (chaosSampleLaw M).toMeasure)
    (hTm : ∀ b j w L, AEStronglyMeasurable (aux_lfgc_sum_trunc_summandTr b M s eps (m + k) j w L)
      (chaosSampleLaw M).toMeasure)
    (hYe : ∀ b j w h, j ≤ ((m + k : ℕ) : ℤ) → 1 ≤ h →
      eLpNorm (fun omega => aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega - Y b j w h omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Eb * (3 : ℝ) ^ (-(a' * h))))
    (hTe : ∀ b j w L,
      eLpNorm (fun omega => aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega -
          aux_lfgc_sum_trunc_summandTr b M s eps (m + k) j w L omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Et * (3 : ℝ) ^ (-(s / 16 * (L : ℝ)))))
    (hEb : (2 + 2 * (buffer : ℝ)) * Eb ≤ Merr)
    (hL0 : (2 + 2 * (buffer : ℝ)) * Et * (3 : ℝ) ^ (-(s / 16 * (L0 : ℝ))) ≤
      κ * Real.exp (-(R * L0 / p)))
    (hMerr : Merr = κ * Real.exp (-(R * L0 / p))) (ha' : 0 < a') (ha'1 : a' ≤ 1)
    (hcL : 1 ≤ s * cL / 16) (hs : 0 < s)
    (D H : ℕ) (hD : 1 ≤ D) (hDH : D ≤ H) (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D) :
    eLpNorm (fun omega => aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i omega -
        aux_lfgc_p1_approx_p1U M s eps m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y D H omega)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((D : ℝ) * Merr * ((3 : ℝ) ^ (-a')) ^ H) := by
  rw [aux_lfgc_p1_approx2_p1T_eq_pre]
  refine (lfgc_p1_approx2 M s eps m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y Draw Z p hp hEb0
    (fun j h => hYm _ j _ h) (fun j => hSm _ j _) (fun j L => hTm _ j _ L)
    (fun j h hj hh => hYe _ j _ h hj hh) (fun j L _ => hTe _ j _ L) D H hD hDH).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  exact lfgc_p1_fin (by positivity) hEb hEb0 hEt0 hL0 hMerr ha' ha'1 hcL hs

/-- Sure convergence hypothesis of the witness on the carrier. -/
theorem aux_lfgc_p1_main_p1_hlimit [NeZero d] (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (en nc ns : ℕ) (enDepth : Fin en → ℕ) (cmpShift : Fin nc → Vec d) (shift : Fin ns → Vec d)
    (buffer m k : ℕ) (z : Vec d) (cL L0 : ℕ) (hcL : 1 ≤ cL)
    (Y : Bool → ℤ → Vec d → ℕ → BilateralField d → ℝ) (omega : BilateralField d)
    (h1 : ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
      omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (h2 : ∀ N, Paper.primitive_scores d M s eps (eta N omega)
      (fun m y => F N m y omega) (fun m y => Praw N m y omega)
      (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
      (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (h3 : ∀ (N n : ℕ) (y : Vec d), Draw N n y omega ≠ ⊤)
    (D : ℕ) (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D) :
    Tendsto (fun H => aux_lfgc_p1_approx_p1U M s eps m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y D H omega) atTop
      (𝓝 (aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i omega)) := by
  rw [aux_lfgc_p1_approx2_p1T_eq_pre]
  refine aux_lfgc_p1_approx2_p1U_tendsto M s eps heps m k buffer cL L0 (enDepth i.1.1) hcL i.2.1.1 i.2.2 Y Draw Z D omega
    fun j _ => ?_
  have hc : eta (m + k) omega = aux_lfgc_layer_tail_canonEta (m + k) omega :=
    aux_lfgc_layer_tail_canonEta_eq (m + k) (eta (m + k)) omega (fun ii y => h1 (m + k) ii y)
  have hf := aux_lfgc_sum_trunc_scores_formula M s eps (eta (m + k) omega) _ _ _ _ _ _ (h2 (m + k))
    (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • i.2.1.1)
  rw [hc] at hf
  exact ⟨hf.1, hf.2, h3 _ _ _⟩

end Paper
