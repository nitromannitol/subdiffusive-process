module

public import SubdiffusiveProcess.Paper.lfgc_p1_final2

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The measurability, error, window and convergence hypotheses of the prefix witness. -/
theorem lfgc_p1_final3 [NeZero d] (M : GMCModel d) (sigma eps : ℝ) (hs0 : 0 < sigma) (heps0 : 0 < eps)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      _root_.SubdiffusiveProcess.Paper.primitive_scores d M sigma eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (Carrier : Set (BilateralField d))
    (hC1 : ∀ omega ∈ Carrier, ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
      omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (hC2 : ∀ omega ∈ Carrier, ∀ N, _root_.SubdiffusiveProcess.Paper.primitive_scores d M sigma eps (eta N omega)
      (fun m y => F N m y omega) (fun m y => Praw N m y omega)
      (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
      (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (hC3 : ∀ omega ∈ Carrier, ∀ (N n : ℕ) (y : Vec d), Draw N n y omega ≠ ⊤)
    (en nc ns : ℕ) (enDepth : Fin en → ℕ) (hdepth : ∀ e, enDepth e ≤ 3)
    (cmpShift : Fin nc → Vec d) (shift : Fin ns → Vec d) (buffer k0 : ℕ) (hk0 : 1 ≤ k0)
    (m k : ℕ) (z : Vec d) (cL L0 width : ℕ) (hcL1 : 1 ≤ cL) (hcL : 1 ≤ sigma * cL / 16)
    (Y : Bool → ℤ → Vec d → ℕ → BilateralField d → ℝ)
    (hYwin : ∀ b j w h, j ≤ ((m + k : ℕ) : ℤ) → 1 ≤ h →
      StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
        (Set.Icc (-j - (width * (h + 1) : ℕ)) (-j + (width * (h + 1) : ℕ)))] (Y b j w h))
    (hYmeas : ∀ b j w h, Measurable (Y b j w h))
    {p Eb Et a' Merr κ R : ℝ} (hp1 : 1 ≤ p) (hEb0 : 0 ≤ Eb) (hEt0 : 0 ≤ Et)
    (hYe : ∀ b j w h, j ≤ ((m + k : ℕ) : ℤ) → 1 ≤ h →
      eLpNorm (fun omega => aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega - Y b j w h omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Eb * (3 : ℝ) ^ (-(a' * h))))
    (hTe : ∀ b j w L,
      eLpNorm (fun omega => aux_lfgc_sum_band_summand b Draw Z (m + k) j w omega -
          aux_lfgc_sum_trunc_summandTr b M sigma eps (m + k) j w L omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Et * (3 : ℝ) ^ (-(sigma / 16 * (L : ℝ)))))
    (hEb : (2 + 2 * (buffer : ℝ)) * Eb ≤ Merr)
    (hL0 : (2 + 2 * (buffer : ℝ)) * Et * (3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ))) ≤
      κ * Real.exp (-(R * L0 / p)))
    (hMerr : Merr = κ * Real.exp (-(R * L0 / p))) (ha'0 : 0 < a') (ha'1 : a' ≤ 1) :
    (∀ D (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D),
      AEStronglyMeasurable (aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i)
        (chaosSampleLaw M).toMeasure) ∧
    (∀ D (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D) H,
      AEStronglyMeasurable (aux_lfgc_p1_approx_p1U M sigma eps m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y D H)
        (chaosSampleLaw M).toMeasure) ∧
    (∀ D H, k0 ≤ D → D ≤ H → ∀ i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D,
      eLpNorm (fun omega => aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i omega -
          aux_lfgc_p1_approx_p1U M sigma eps m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y D H omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((D : ℝ) * Merr * ((3 : ℝ) ^ (-a')) ^ H)) ∧
    (∀ D H j, k0 ≤ D → D ≤ j → j ≤ H → ∀ i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D,
      StronglyMeasurable[aux_lfgc_family_cover_nodeWin d k (aux_lfgc_p1_approx_p1Wfun (width + cL + 1) L0 buffer H)]
        (aux_lfgc_p1_approx_p1U M sigma eps m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y D j)) ∧
    (∀ omega ∈ Carrier, ∀ D (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D),
      Tendsto (fun H => aux_lfgc_p1_approx_p1U M sigma eps m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y D H omega)
        atTop (𝓝 (aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i omega))) := by
  refine ⟨fun D i => lfgc_p1_wit M sigma eps heps0 eta hEta F Praw Rraw Draw Z rawGood hPrim en nc ns
      enDepth cmpShift shift buffer m k z D i,
    fun D i H => aux_lfgc_p1_wit_p1U_aesm M sigma eps heps0 m k buffer cL L0 (enDepth i.1.1) i.2.1.1 i.2.2 Y
      (fun j h => hYmeas _ j _ h) D H,
    fun D H hD hDH i => lfgc_p1_main M sigma eps Draw Z en nc ns enDepth cmpShift shift buffer m k z cL
      L0 Y p hp1 hEb0 hEt0 (fun b j w h => (hYmeas b j w h).aestronglyMeasurable)
      (fun b j w => lfgc_p1_help M sigma eps heps0 eta hEta F Praw Rraw Draw Z rawGood hPrim b
        (m + k) j w)
      (fun b j w L => (aux_lfgc_p1_help_summandTr_measurable b M sigma eps heps0 (m + k) j w L).aestronglyMeasurable)
      hYe hTe hEb hL0 hMerr ha'0 ha'1 hcL hs0 D H (le_trans hk0 hD) hDH i,
    fun D H j hD hDj hjH i => (lfgc_p1_approx M sigma eps heps0 m k buffer cL L0 width (enDepth i.1.1)
      (hdepth _) i.2.1.1 i.2.2 Y (fun jj hh hjj hh1 => hYwin _ jj _ hh hjj hh1) D j
      (le_trans hk0 hD) hDj).mono (aux_lfgc_chain_cover_nodeWin_mono k (aux_lfgc_p1_approx_p1Wfun_mono (width + cL + 1) L0 buffer hjH)),
    fun omega homega D i => aux_lfgc_p1_main_p1_hlimit M sigma eps heps0 eta F Praw Rraw Draw Z rawGood en nc ns
      enDepth cmpShift shift buffer m k z cL L0 hcL1 Y omega (hC1 omega homega) (hC2 omega homega)
      (hC3 omega homega) D i⟩

end SubdiffusiveProcess.Paper
