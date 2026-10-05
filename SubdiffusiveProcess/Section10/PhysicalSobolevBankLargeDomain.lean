module

public import SubdiffusiveProcess.Section10.PhysicalSobolevBankBounds
public import SubdiffusiveProcess.Section10.PhysicalLocalTransportUniqueness

@[expose] public section

/-! Exact retained-window reduction of the finite l<m branch. The conditional
pullback below is only a transport helper, not a completed uniform bank. -/
open MeasureTheory Homogenization SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10

def retainedWindowSpeed {d : ℕ} (M : GMCModel d) (l : ℕ)
    (ξ : Fin (l + 1) → C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) : ℝ :=
  Real.exp ((∑ j : Fin (l + 1), ξ j x) - (l + 1 : ℝ) * tauSq M.P)

def retainedWindowCoefficient {d : ℕ} (M : GMCModel d) (l : ℕ)
    (ξ : Fin (l + 1) → C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) : ℝ :=
  (ahom M l)⁻¹ * retainedWindowSpeed M l ξ x

theorem retainedWindowSpeed_physical {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m) (z : SpatialCoordinates d)
    (ω : AnchoredC11Sample d) :
    retainedWindowSpeed M l (physicalWindow l m z ω) = localSpeed M l m z ω := by
  funext x
  rw [localSpeed, localFactor_eq_one M hlm]
  simp only [inv_one, one_mul]
  change Real.exp ((∑ j : Fin (l + 1), ω.val j (z + (3 : ℝ) ^ m • x)) -
    (l + 1 : ℝ) * tauSq M.P) = aCutoff M l ω.val (z + (3 : ℝ) ^ m • x)
  unfold aCutoff
  congr 1
  have hh := Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ω.val k (z + (3 : ℝ) ^ m • x)) (l + 1)
  rw [hh, Finset.sum_sub_distrib]
  simp

theorem retainedWindowCoefficient_physical {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m) (z : SpatialCoordinates d)
    (ω : AnchoredC11Sample d) :
    retainedWindowCoefficient M l (physicalWindow l m z ω) = localCoefficient M l m z ω := by
  unfold retainedWindowCoefficient localCoefficient
  rw [activeScale_coe, min_eq_right hlm, retainedWindowSpeed_physical M hlm]

/-- The exact further-dilated density and saturated ahom_l coefficient.
This identity does not declare a growing-reference-cube moment uniform. -/
theorem physical_retained_further_dilation {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m) (z : SpatialCoordinates d)
    (ω : AnchoredC11Sample d) (x : SpatialCoordinates d) :
    localSpeed M l m z ω x = localSpeed M l l z ω ((3 : ℝ) ^ (m - l) • x) ∧
    localCoefficient M l m z ω x = localCoefficient M l l z ω ((3 : ℝ) ^ (m - l) • x) :=
  ⟨localSpeed_further_dilation M hlm z ω x, localCoefficient_further_dilation M hlm z ω x⟩

/-- Direct physical-window pushforward. Once a scale-uniform retained-window
bank is proved, this helper attaches it without an additional coupling constant. -/
theorem physicalRetainedWindow_bank_pullback {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m) (z : SpatialCoordinates d)
    {K : (Fin (l + 1) → C(SpatialCoordinates d, ℝ)) → ℝ} (hK : Measurable K)
    (hone : ∀ ξ, 1 ≤ K ξ) {B Q C : ℝ}
    (hm : (∫⁻ ξ, ENNReal.ofReal (K ξ ^ Q) ∂windowLaw M l m) ≤ ENNReal.ofReal C)
    (hs : ∀ᵐ ξ ∂windowLaw M l m,
      PhysicalStaticBounds (retainedWindowSpeed M l ξ) (retainedWindowCoefficient M l ξ) B (K ξ)) :
    ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧ (∀ ω, 1 ≤ Kphys ω) ∧
      (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
        ENNReal.ofReal C ∧
      ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        PhysicalStaticBounds (localSpeed M l m z ω) (localCoefficient M l m z ω) B (Kphys ω) := by
  let Kphys := K ∘ physicalWindow l m z
  refine ⟨Kphys, hK.comp (measurable_physicalWindow l m z), fun ω => hone _, ?_, ?_⟩
  · exact ((physicalWindow_preserving M l m z).lintegral_comp
      (ENNReal.measurable_ofReal.comp (hK.pow measurable_const))).trans_le hm
  · filter_upwards [(physicalWindow_preserving M l m z).quasiMeasurePreserving.ae hs] with ω hω
    rw [retainedWindowSpeed_physical M hlm, retainedWindowCoefficient_physical M hlm] at hω
    exact hω

end SubdiffusiveProcess.Section10
