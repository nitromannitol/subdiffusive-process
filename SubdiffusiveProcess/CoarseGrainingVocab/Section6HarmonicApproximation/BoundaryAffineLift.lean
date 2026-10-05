module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.RoughDirichletMinimality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.AffineHarmonic
public import Homogenization.Book.Ch03.Theorems.EnergyRHS.BoundaryGradient

@[expose] public section

/-!
# Rough harmonic extension of the affine boundary part

This is the first half of the manuscript's boundary-datum split.  The
`aCutoff`-harmonic extension of an affine function with slope `p` costs at
most the raw upper ellipticity constant times `|p|^2`; the affine constant is
absent, as required by the printed estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

noncomputable section

variable {d : ℕ}

theorem volumeAverage_openCubeSet_eq_cubeAverage_local
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  calc
    volumeAverage (openCubeSet Q) f =
        (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume := by
      unfold volumeAverage
      rw [volume_openCubeSet_toReal]
    _ = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂MeasureTheory.volume := by
      rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = cubeAverage Q f := rfl

/-- The scalar rough harmonic extension of an affine datum has the expected
constant-gradient energy price. -/
theorem exists_aCutoffAffineDirichletLift_energy_le
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (x : Vec d) (c : ℝ) (p : Vec d) :
    let ell := affineLiftH1
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain x c p
    ∃ v : DirichletForcedCubeSolution Q (aCutoffFamily M L omega) (fun _ => 0),
      v.boundaryData = ell ∧
        localizedCoeffEnergyValue (openCubeSet Q)
            ((aCutoffFamily M L omega).coeffOn Q) v.toH1 ≤
          ((aCutoffFamily M L omega).coeffOn Q).Lam * vecNormSq p := by
  dsimp only
  let ell : H1Function (openCubeSet Q) :=
    affineLiftH1
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain x c p
  obtain ⟨v, hv, hmin⟩ :=
    exists_aCutoffZeroForceDirichletLift_energy_le M L omega Q ell
  have hgradMem : MemVectorL2 (cubeSet Q) ell.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using
      ell.grad_memVectorL2
  have hupper :=
    cubeAverage_coefficientEnergyDensity_publicCoeffField_le_Lam_mul_cubeAverage_vecNormSq
      (Q := Q) (a := aCutoffFamily M L omega) hgradMem
  have henergy : localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) ell ≤
      ((aCutoffFamily M L omega).coeffOn Q).Lam * vecNormSq p := by
    rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) ell]
    have hfield : (fun y => vecNormSq (ell.grad y)) = fun _ => vecNormSq p := by
      funext y
      rw [show ell.grad y = p by
        exact affineLiftH1_grad
          (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain x c p y]
    rw [volumeAverage_openCubeSet_eq_cubeAverage_local]
    rw [hfield, cubeAverage_const] at hupper
    exact hupper
  exact ⟨v, hv, hmin.trans henergy⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
