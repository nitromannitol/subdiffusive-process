module

public import SubdiffusiveProcess.Section10.PhysicalSobolevBankLargeResponse
public import SubdiffusiveProcess.Section10.KilledSobolevMoment
public import SubdiffusiveProcess.Section10.PhysicalLocalTransportEnvironment

@[expose] public section

/-! An unconditional, scale-uniform moment bank for the precise saturated
lower ellipticity factor, and its actual anchored physical-law application. -/
open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The moment-order parameter precedes the disorder threshold; the bound
constant precedes both cutoff and reference-cube scale. -/
theorem physical_large_lower_ellipticity_bank {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ →
        ∀ l m : ℕ, l ≤ m → ∀ z : SpatialCoordinates d,
          paperENNRealLpNorm M.P.toMeasure q (fun ω => ENNReal.ofReal
            (ahom M l * fluxRowMomentTranslatedLowerInv M l m z ω)) ≤
              ENNReal.ofReal C := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨δ, Ce, hδ, hCe, hresponse⟩ := physical_large_response_bank hd q hq
  refine ⟨δ, (1 + Real.sqrt 2 * Ce) ^ 2, hδ, by positivity, ?_⟩
  intro M hM l m hlm z
  have h := paperENNRealLpNorm_ahom_mul_fluxRowMomentTranslatedLowerInv_le
    M l m z hq
  refine h.trans (le_trans (pow_le_pow_left' (show
    1 + ENNReal.ofReal (Real.sqrt 2) * paperENNRealLpNorm M.P.toMeasure (2 * q)
      (translatedHomogenizationErrorRandom M l m z (1 / 16) 1) ≤
    1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal Ce from by
      gcongr; exact hresponse M hM l m hlm z) 2) (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (by positivity),
    ← ENNReal.ofReal_pow (by positivity)]

/-- Convert the positive finite manuscript Lq norm into its literal moment. -/
theorem physical_large_moment_of_paperNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} {q C : ℝ} (hq : 0 < q) (hX : ∀ ω, 0 ≤ X ω)
    (hC : 0 ≤ C)
    (h : paperENNRealLpNorm μ q (fun ω => ENNReal.ofReal (X ω)) ≤ ENNReal.ofReal C) :
    (∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂μ) ≤ ENNReal.ofReal (C ^ q) := by
  have hh := ENNReal.rpow_le_rpow h hq.le
  simp only [paperENNRealLpNorm, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ hq.ne', ENNReal.rpow_one] at hh
  simpa only [ENNReal.ofReal_rpow_of_nonneg hC hq.le,
    ENNReal.ofReal_rpow_of_nonneg (hX _) hq.le] using hh

/-- A measurable >=1 physical-law factor controlling the literal saturated
`ahom_l * lambda^-1` on the physical scale-m cube. This is an ellipticity
bank, not the native H10 coercivity projection. -/
theorem physical_large_ellipticity_physical_bank {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∀ l m : ℕ, l ≤ m → ∀ z : SpatialCoordinates d,
        ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
            ENNReal.ofReal C ∧
          ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
            ahom M l * (Ch04.lambdaSqCoeffField (originCube d (m : ℤ))
              (1 / 16) (.finite 1)
              (aCutoffRegCoeffField M l (translatePotentialSample z ω.val)))⁻¹ ≤ K ω := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨δ, Ce, hδ, hCe, hfactor⟩ := physical_large_lower_ellipticity_bank hd q hq
  refine ⟨δ, 1 + Ce ^ q, hδ, by positivity, ?_⟩
  intro M hM l m hlm z
  let X := fun ω : PotentialSample d => ahom M l * fluxRowMomentTranslatedLowerInv M l m z ω
  have hX : Measurable X := (measurable_fluxRowMomentTranslatedLowerInv M l m z).const_mul _
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => mul_nonneg (ahom_pos M l).le
    (fluxRowMomentTranslatedLowerInv_nonneg M l m z ω)
  let K := fun ω : AnchoredC11Sample d => max 1 (X ω.val)
  refine ⟨K, measurable_const.max (hX.comp measurable_subtype_coe),
    fun ω => le_max_left _ _, ?_, ?_⟩
  · have hmoment := physical_large_moment_of_paperNorm M.P.toMeasure
      (zero_lt_one.trans_le hq) hX0 hCe.le (hfactor M hM l m hlm z)
    have hmphys : (∫⁻ ω, ENNReal.ofReal (X ω.val ^ q)
        ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal (Ce ^ q) :=
      ((physicalLaw_val_preserving M).lintegral_comp
        (ENNReal.measurable_ofReal.comp (hX.pow measurable_const))).trans_le hmoment
    have hconst : (∫⁻ _ω : AnchoredC11Sample d, ENNReal.ofReal ((1 : ℝ) ^ q)
        ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal 1 := by simp
    exact lintegral_max_rpow_le (PhysicalAttachment.physicalLaw M).toMeasure
      measurable_const (fun _ => zero_le_one) (fun ω => hX0 ω.val) (zero_le_one.trans hq) zero_le_one
      (Real.rpow_nonneg hCe.le _) hconst hmphys
  · have heq : fluxRowMomentTranslatedLowerInv M l m z =ᵐ[M.P.toMeasure]
        fun ω => (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 16) (.finite 1)
          (aCutoffRegCoeffField M l (translatePotentialSample z ω)))⁻¹ := by
      simpa only [fluxRowMomentTranslatedLowerInv, Function.comp_apply] using!
        (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.measurePreserving_translatePotentialSequence M z).quasiMeasurePreserving.ae_eq_comp (fluxRowMomentLowerInvMeasurable_ae_eq M l m)
    filter_upwards [(physicalLaw_val_preserving M).quasiMeasurePreserving.ae heq] with ω hω
    exact (le_max_right (1 : ℝ) (X ω.val)).trans' (by dsimp only [X]; rw [hω])


end SubdiffusiveProcess.Section10
