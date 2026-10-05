module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerOccupationEllipticity
@[expose] public section

/-!

Continuity upgrades the actual scalar coefficient bounds to pointwise ellipticity on the open domain. The matrix measurability and ellipticity carrier are constructed from those data.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Filter Set SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Construct the pointwise scalar ellipticity carrier from continuity and coefficient data. -/
theorem goodCube_scalar_ellipticity_of_continuous_coefficientOn
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {a : Vec d → ℝ} (ha : ContinuousOn a U) (hCoeff : CoefficientOn U a) :
    ∃ lam Lam : ℝ, 0 < lam ∧ IsEllipticFieldOn lam Lam U (scalarCoeffField a) := by
  classical
  obtain ⟨-, lo, hi, hlo, hbnd⟩ := hCoeff
  have hptw : ∀ x ∈ U, lo ≤ a x ∧ a x ≤ hi :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower.forall_mem_of_ae_of_continuousOn
      hU ha hbnd
  refine ⟨lo, hi, hlo, ?_, ?_⟩
  · have hpiece : Measurable (U.piecewise a fun _ => (0 : ℝ)) :=
      ha.measurable_piecewise continuous_const.continuousOn hU.measurableSet
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    by_cases hij : i = j
    · subst hij
      simpa [Set.piecewise, scalarCoeffField, Homogenization.scalarMatrix] using! hpiece
    · have hzero : (fun x : Vec d => if x ∈ U then scalarCoeffField a x i j else 0)
          = fun _ => (0 : ℝ) := by
        funext x
        simp [scalarCoeffField, Homogenization.scalarMatrix, hij]
      rw [hzero]
      exact measurable_const
  · intro x hx
    have hax : 0 < a x := lt_of_lt_of_le hlo (hptw x hx).1
    exact (Homogenization.isEllipticMatrix_scalarMatrix hax).mono hlo
      (hptw x hx).1 (hptw x hx).2

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
