module

public import SubdiffusiveProcess.Section10.TorsionExitMassive
public import SubdiffusiveProcess.Section10.TorsionExitPointwise

@[expose] public section

/-! Same-speed, same-energy LocalDiffusion consumers. The pointwise theorem
states its precise starting-point regularity input separately from FOT association. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- The actual unnormalized discounted occupation inherits the torsion cap. -/
theorem localDiffusion_discountedUnitOccupation_ae_le {d : ℕ}
    {A b : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    (hlocal : LocalDiffusion A b law) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (hb : CoefficientOn U b)
    {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ x ∂(weightedMeasure b).restrict U,
      discountedUnitOccupation law U s x ≤
        ENNReal.ofReal (torsionConstant p * Ksob *
          (weightedMeasure b U).toReal ^ (1 - 2 / p)) := by
  let : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  let : IsFiniteMeasure ((weightedMeasure b).restrict U) :=
    variational_weighted_isFiniteMeasure hU.isOpen.measurableSet hb
  obtain ⟨u, hae, hu⟩ := hlocal.2.2 U hU.isOpen hU.isBoundedDomain.isBounded s hs
    (fun _ => 1) (memLp_const (1 : ℝ))
  have hu' : IsMassiveWeakSolutionOn A b s⁻¹ U u.toH1Function (fun _ => s⁻¹) := by
    simpa only [mul_one] using hu
  have hv := normalizedResolvent_scaled_equation hs u hu'
  have hcap := massiveTorsion_ae_le hU hne hb (inv_nonneg.mpr hs.le) hp hKsob hSob (s • u) hv
  filter_upwards [hae, hcap] with x hx hcx
  rw [discountedUnitOccupation_eq_ofReal_scaled_resolvent law hU.isOpen hs x]
  apply ENNReal.ofReal_le_ofReal
  change s * u.toFun x ≤ _ at hcx
  simpa only [hx] using hcx

/-- Countable monotone convergence gives the actual mean bound almost everywhere. -/
theorem localDiffusion_meanExit_ae_le {d : ℕ}
    {A b : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    (hlocal : LocalDiffusion A b law) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (hb : CoefficientOn U b)
    {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob) :
    ∀ᵐ x ∂(weightedMeasure b).restrict U, meanExit law U x ≤
      ENNReal.ofReal (torsionConstant p * Ksob *
        (weightedMeasure b U).toReal ^ (1 - 2 / p)) := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂(weightedMeasure b).restrict U,
      discountedUnitOccupation law U ((n : ℝ) + 1) x ≤
        ENNReal.ofReal (torsionConstant p * Ksob *
          (weightedMeasure b U).toReal ^ (1 - 2 / p)) := fun n =>
    localDiffusion_discountedUnitOccupation_ae_le hlocal hU hne hb hp hKsob hSob (by positivity)
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact meanExit_le_of_discountedUnitOccupation_le law hU.isOpen x hx

/-- The every-start upper bound needs only lower semicontinuity of countably many
actual discounted occupations, not a zero-mass equality or heat kernel. -/
theorem localDiffusion_meanExit_le {d : ℕ}
    {A b : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    (hlocal : LocalDiffusion A b law) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (hb : CoefficientOn U b)
    {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (hls : UnitDiscountOccupationLSC law U) :
    ∀ x ∈ U, meanExit law U x ≤
      ENNReal.ofReal (torsionConstant p * Ksob *
        (weightedMeasure b U).toReal ^ (1 - 2 / p)) := by
  intro x hx
  apply meanExit_le_of_discountedUnitOccupation_le law hU.isOpen x
  intro n
  exact discountedUnitOccupation_le_of_ae law hU.isOpen hb (hls n)
    (localDiffusion_discountedUnitOccupation_ae_le hlocal hU hne hb hp hKsob hSob (by positivity)) x hx



end SubdiffusiveProcess.Section10
