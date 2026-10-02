import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMultiplierDerivative

/-!
# Weak Hodge identities for the one-step projected columns

This file records the divergence-free half of the stationary Helmholtz trace
calculation.  Each forcing column minus its stationary potential projection
is solenoidal, so it has zero pairing with every stationary potential test
field.  Expanding the literal forcing identifies the remaining pairing with
the corresponding scalar coordinate.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Potential and solenoidal stationary vector fields are orthogonal. -/
theorem Stationary.inner_eq_zero_of_mem_potential_of_mem_solenoidal
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [AddAction (Vec d) Omega]
    [MeasurableConstVAdd (Vec d) Omega]
    [VAddInvariantMeasure (Vec d) Omega mu]
    {F R : Stationary.VectorL2 d mu}
    (hF : F ∈ Stationary.stationaryPotentialSubspace
      (mu := mu) (d := d))
    (hR : R ∈ Stationary.stationarySolenoidalSubspace
      (mu := mu) (d := d)) :
    inner ℝ F R = 0 :=
  Submodule.inner_right_of_mem_orthogonal hF hR

/-- Weak divergence identity for one projected coordinate column.  This is
the exact stationary form of `div (X e_j - P(X e_j)) = 0`. -/
theorem inner_coord_multiplier_eq_inner_projectedColumn
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (F : Stationary.VectorL2 d M.P.toMeasure)
    (hF : letI := potentialSequenceVAddInvariant M
      F ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    (j : Fin d) (hh : 0 < h) :
    inner ℝ
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) j F)
        (oneStepMultiplierAtL2 M n h 0 hh) =
      inner ℝ F
        (oneStepPotentialProjection M n h (Pi.single j 1) hh) := by
  letI := potentialSequenceVAddInvariant M
  have horth : inner ℝ F
      (oneStepOriginForcingL2 M n h (Pi.single j 1) hh -
        oneStepPotentialProjection M n h (Pi.single j 1) hh) = 0 :=
    Stationary.inner_eq_zero_of_mem_potential_of_mem_solenoidal hF
      (oneStepOriginForcingL2_sub_projection_mem_stationarySolenoidalSubspace
        M n h (Pi.single j 1) hh)
  rw [inner_sub_right] at horth
  have heq : inner ℝ F
      (oneStepOriginForcingL2 M n h (Pi.single j 1) hh) =
        inner ℝ F
          (oneStepPotentialProjection M n h (Pi.single j 1) hh) := by
    linarith
  rw [inner_vectorL2_oneStepOriginForcing_basis_eq_coord_inner] at heq
  exact heq

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
