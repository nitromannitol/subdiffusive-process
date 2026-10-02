import SubdiffusiveProcess.Sobolev.ResponsePositivity

/-! The actual volume-source solver as a continuous linear operator, with its quadratic response identity.
No compactness or convergence is asserted in this module. -/

open MeasureTheory TopologicalSpace

noncomputable section
namespace SubdiffusiveProcess

/-- The unique continuous linear operator represented by the volume-source weak solver. -/
def volumeResponseOperator {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) : DomainL2 Ω →L[ℝ] DomainL2 Ω :=
  (existsUnique_volumeResponseOperator S a).choose

/-- Evaluation of the volume-response operator is the actual weak solution. -/
theorem volumeResponseOperator_apply {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f : DomainL2 Ω) :
    volumeResponseOperator S a f =
      (responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 :=
  (existsUnique_volumeResponseOperator S a).choose_spec.1 f

/-- The volume-response operator is symmetric in its source pairings. -/
theorem volumeResponseOperator_symm {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f g : DomainL2 Ω) :
    inner ℝ f (volumeResponseOperator S a g) = inner ℝ g (volumeResponseOperator S a f) := by
  rw [volumeResponseOperator_apply, volumeResponseOperator_apply]
  exact volumeResponse_pairing_symm S a f g

/-- The quadratic pairing of the volume-response operator is its inverse response. -/
theorem volumeResponseOperator_quadratic {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f : DomainL2 Ω) :
    inner ℝ f (volumeResponseOperator S a f) =
      inverseResponse S a ((sobolevVolumeLoad f).comp S.space.subtypeL) := by
  rw [volumeResponseOperator_apply, inverseResponse_eq_load]
  rfl

end SubdiffusiveProcess
