module

public import SubdiffusiveProcess.Section10.TorsionBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKMassiveHolder

@[expose] public section

/-! A continuous torsion representative, followed by full-support promotion.
The essential bound is already proved before regularity is invoked. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
namespace SubdiffusiveProcess.Section10

/-- Positive local density gives the full-support promotion on the open domain. -/
theorem torsion_continuous_le_of_ae {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {b : Vec d → ℝ} (hb : CoefficientOn U b)
    {v : Vec d → ℝ} (hv : ContinuousOn v U) {L : ℝ}
    (hbound : ∀ᵐ x ∂(weightedMeasure b).restrict U, v x ≤ L) :
    ∀ x ∈ U, v x ≤ L := by
  have hfull := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hb
  exact continuousOn_le_of_ae_restrict volume U hU v hv L (hfull.ae_le hbound)

/-- Native weak torsion has an actual continuous representative bounded at every
point by the same essential constant, without an exit-time identification. -/
theorem weakTorsion_exists_continuous_representative {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hA : ContinuousOn A U) (hApos : ∀ x ∈ U, 0 < A x)
    (hb : CoefficientOn U b) {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (u : H10Function U) (hu : IsWeakTorsion A b U u) :
    ∃ v : Vec d → ℝ, ContinuousOn v U ∧
      (v =ᵐ[(weightedMeasure b).restrict U] u.toFun) ∧
      (v =ᵐ[volume.restrict U] u.toFun) ∧
      ∀ x ∈ U, |v x| ≤
        torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p) := by
  let L := torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p)
  have hbound := weakTorsion_ae_abs_le hU hne hb hp hKsob hSob u hu
  have hfull := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.isOpen.measurableSet hb
  have huabs : ∀ᵐ x ∂volume.restrict U, |u.toFun x| ≤ L := hfull.ae_le hbound
  obtain ⟨lo, hi, hlo, hbnd⟩ := hb.2
  have habs : ∀ᵐ x ∂volume.restrict U, |b x| ≤ hi := by
    filter_upwards [hbnd] with x hx
    rw [abs_of_nonneg (hlo.le.trans hx.1)]
    exact hx.2
  let : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  have hf : MemL2On U (fun _ : Vec d => (1 : ℝ)) := memLp_const 1
  have hfb : ∀ᵐ _x ∂volume.restrict U, |(1 : ℝ)| ≤ 1 := by simp
  obtain ⟨hcont, hae, -⟩ := holder_euclideanBallAverageRepresentative_of_bounded_massiveWeakSolution
    hd hU.isOpen hA hApos hb.1 habs hf hfb huabs hu
  let v := euclideanBallAverageRepresentative u.toFun
  have haeμ : v =ᵐ[(weightedMeasure b).restrict U] u.toFun :=
    (weightedMeasure_restrict_absolutelyContinuous_volume_restrict hU.isOpen.measurableSet).ae_le hae
  have hvabs : ∀ᵐ x ∂(weightedMeasure b).restrict U, |v x| ≤ L := by
    filter_upwards [haeμ, hbound] with x hx hbx
    simpa only [hx] using hbx
  refine ⟨v, hcont, haeμ, hae, ?_⟩
  exact torsion_continuous_le_of_ae hU.isOpen hb hcont.abs hvabs

end SubdiffusiveProcess.Section10
