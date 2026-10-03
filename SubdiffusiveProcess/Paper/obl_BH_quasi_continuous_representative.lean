module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Sobolev.WeakGradient

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def obl_BH_quasi_continuous_representative {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm) : Prop :=
  ∃ rep :
      ∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))),
        v ∈ E.toClosedForm.domain → SpatialCoordinates d → ℝ,
    (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
        (hv : v ∈ E.toClosedForm.domain), Measurable (rep v hv)) ∧
    (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
        (hv : v ∈ E.toClosedForm.domain),
      (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] rep v hv)) ∧
    (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
        (hv : v ∈ E.toClosedForm.domain),
      ∀ K : Set ℝ, IsCompact K → volume K = 0 →
        Gamma.measure v ((rep v hv) ⁻¹' K) = 0) ∧
    (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
        (hv : v ∈ E.toClosedForm.domain),
      ∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
      ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
        (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
        ∀ (w : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
          (_hw : w ∈ E.toClosedForm.domain),
          (⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
            (fun x => T (rep v hv x))) →
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            ((Gamma.measure w B).toReal =
              ∫ x in B, (Tderiv (rep v hv x)) ^ 2 ∂(Gamma.measure v)))

/-- **Non-vacuity of the carrier.**  The zero Dirichlet form with its zero energy measure
satisfies it.  This establishes NON-VACUITY only: inhabitation at the paper's form is the
published input itself, exactly as for `DirichletForm.HasEnergyMeasure`.  Without this
check a consumer that carries the `Prop` could be vacuously true. -/
theorem aux_obl_BH_quasi_continuous_representative_nonvacuous
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) :
    obl_BH_quasi_continuous_representative
      (DirichletForm.zeroDirichletForm
        (volume.restrict (Q : Set (SpatialCoordinates d))))
      (DirichletForm.zeroEnergyMeasure
        (volume.restrict (Q : Set (SpatialCoordinates d)))) := by
  classical
  refine ⟨fun v _ => (Lp.aestronglyMeasurable v).mk ⇑v, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact (Lp.aestronglyMeasurable v).stronglyMeasurable_mk.measurable
  · intro v hv
    exact (Lp.aestronglyMeasurable v).ae_eq_mk
  · intro v hv K hK hKnull
    simp [DirichletForm.zeroEnergyMeasure]
  · intro v hv T hT hT0 Tderiv hTm hTd w hw hwrep B hB
    simp [DirichletForm.zeroEnergyMeasure]

end Paper
