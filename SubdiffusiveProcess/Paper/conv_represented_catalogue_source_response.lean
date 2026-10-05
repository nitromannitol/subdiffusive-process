module

public import Mathlib
public import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
public import SubdiffusiveProcess.Main.InfraredCharacterization

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Elementary bound: an energy `x = ⟨g,u⟩ ≥ 0` with `‖u‖² ≤ K x` satisfies `x ≤ K ‖g‖²`. -/
theorem aux_conv_represented_source_response_bound (x K ng nu : ℝ) (hx : 0 ≤ x) (hK : 0 ≤ K)
    (hxle : x ≤ ng * nu) (hnu2 : nu ^ 2 ≤ K * x) :
    x ≤ K * ng ^ 2 := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have h1 : x ^ 2 ≤ ng ^ 2 * nu ^ 2 := by
      have := mul_self_le_mul_self hx hxle
      nlinarith [this]
    have h2 : x ^ 2 ≤ ng ^ 2 * (K * x) := h1.trans (mul_le_mul_of_nonneg_left hnu2 (sq_nonneg _))
    have h3 : x * x ≤ (K * ng ^ 2) * x := by nlinarith [h2]
    exact le_of_mul_le_mul_right h3 hpos

/-- **Source responses of the catalogue: measurability, nonnegativity and domination by the coercivity
constant.**  For an `L²` source `g` and the killed space, the inverse response
`⟨g, Φ_N(β) g⟩` of the actual cutoff killed inverse is measurable in the environment, nonnegative, and
bounded by `KH N β · ‖g‖²` whenever `KH` is a coercivity constant for the `L²` norm on the killed space
(the `L²`-part of catalogue clause H). Hence it is tight along any cutoff sequence along which `KH`
is bounded in probability. -/
theorem conv_represented_catalogue_source_response
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (KH : ℕ → BilateralField d → ℝ) (G : Set (BilateralField d))
    (hKHnn : ∀ N β, 0 ≤ KH N β)
    (hKH : ∀ N, ∀ β ∈ G, ∀ v : S.space,
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ^ 2 ≤
        KH N β * responseForm S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr) v v)
    (g : DomainL2 (centeredCube z r hr))
    (P0 : Measure (BilateralField d)) (hG : P0 Gᶜ = 0) (Ns : ℕ → ℕ)
    (hKHtight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      P0 {β | Mb < KH (Ns n) β} ≤ ENNReal.ofReal rho) :
    (∀ N, Measurable (fun β => inverseResponse S
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr)
      ((sobolevVolumeLoad g).comp S.space.subtypeL))) ∧
    (∀ N β, 0 ≤ inverseResponse S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr)
      ((sobolevVolumeLoad g).comp S.space.subtypeL)) ∧
    (∀ N, ∀ β ∈ G, inverseResponse S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr)
      ((sobolevVolumeLoad g).comp S.space.subtypeL) ≤ KH N β * ‖g‖ ^ 2) ∧
    (∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      P0 {β | Mb < |inverseResponse S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ns n) z hr)
        ((sobolevVolumeLoad g).comp S.space.subtypeL)|} ≤ ENNReal.ofReal rho) := by
  have hdom : ∀ N, ∀ β ∈ G, inverseResponse S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr)
      ((sobolevVolumeLoad g).comp S.space.subtypeL) ≤ KH N β * ‖g‖ ^ 2 := by
    intro N β hβ
    set a := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr
    set u := responseSolution S a ((sobolevVolumeLoad g).comp S.space.subtypeL)
    have hx : 0 ≤ inverseResponse S a ((sobolevVolumeLoad g).comp S.space.subtypeL) :=
      inverseResponse_nonneg _ _ _
    have hxle : inverseResponse S a ((sobolevVolumeLoad g).comp S.space.subtypeL) ≤
        ‖g‖ * ‖(u : SobolevData (centeredCube z r hr)).1‖ := by
      rw [inverseResponse_eq_load]
      change ⟪g, (u : SobolevData (centeredCube z r hr)).1⟫_ℝ ≤ _
      exact real_inner_le_norm _ _
    have hnu2 : ‖(u : SobolevData (centeredCube z r hr)).1‖ ^ 2 ≤
        KH N β * inverseResponse S a ((sobolevVolumeLoad g).comp S.space.subtypeL) := hKH N β hβ u
    exact aux_conv_represented_source_response_bound _ _ ‖g‖ _ hx (hKHnn N β) hxle hnu2
  refine ⟨fun N => ?_, fun N β => inverseResponse_nonneg _ _ _, hdom, ?_⟩
  · -- measurability through the strongly measurable cutoff operator
    have hc : Continuous (fun T : DomainL2 (centeredCube z r hr) →L[ℝ]
        DomainL2 (centeredCube z r hr) => ⟪g, T g⟫_ℝ) :=
      continuous_const.inner ((ContinuousLinearMap.apply ℝ _ g).continuous)
    have hm : Measurable (fun β => ⟪g, volumeResponseOperator S
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr) g⟫_ℝ) :=
      (hc.comp_stronglyMeasurable
        (stronglyMeasurable_cutoffVolumeResponseOperator M H hH.1 N z r hr S)).measurable
    have hfun : (fun β => inverseResponse S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr)
        ((sobolevVolumeLoad g).comp S.space.subtypeL)) =
        fun β => ⟪g, volumeResponseOperator S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr) g⟫_ℝ :=
      funext fun β => (volumeResponseOperator_quadratic S _ g).symm
    rw [hfun]
    exact hm
  · -- tightness: on `G`, `|resp| ≤ KH ‖g‖²`
    intro rho hrho
    obtain ⟨Mb, hMb⟩ := hKHtight rho hrho
    refine ⟨Mb * ‖g‖ ^ 2, fun n => ?_⟩
    have hsub : {β | Mb * ‖g‖ ^ 2 < |inverseResponse S
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ns n) z hr)
        ((sobolevVolumeLoad g).comp S.space.subtypeL)|} ⊆
        {β | Mb < KH (Ns n) β} ∪ Gᶜ := by
      intro β hβ
      by_cases hβG : β ∈ G
      · left
        have hle := hdom (Ns n) β hβG
        have hnn := inverseResponse_nonneg S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ns n) z hr)
          ((sobolevVolumeLoad g).comp S.space.subtypeL)
        rw [Set.mem_ofPred_eq, abs_of_nonneg hnn] at hβ
        have hlt : Mb * ‖g‖ ^ 2 < KH (Ns n) β * ‖g‖ ^ 2 := lt_of_lt_of_le hβ hle
        exact lt_of_mul_lt_mul_right hlt (sq_nonneg _)
      · exact Or.inr hβG
    calc P0 _ ≤ P0 ({β | Mb < KH (Ns n) β} ∪ Gᶜ) := measure_mono hsub
      _ ≤ P0 {β | Mb < KH (Ns n) β} + P0 Gᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal rho := by rw [hG, add_zero]; exact hMb n

end SubdiffusiveProcess.Paper
