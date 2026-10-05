module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.RoughDirichletMinimality
public import Homogenization.Book.Ch03.Theorems.CoarsePoincare
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

@[expose] public section

set_option autoImplicit false

/-!
# Coarse gradient-energy control for arbitrary boundary data

The deterministic full-dual cutoff-product estimate only needs a descendant
cube-average control for the gradient of its scalar factor.  Harmonicity of
that scalar factor is unnecessary: on each descendant we replace it by the
zero-force Dirichlet solution with the same trace.  The mean gradient is
unchanged, Dirichlet minimality lowers the coefficient energy, and the usual
one-cube coarse `sigmaStarInv` estimate applies to the replacement.

This is the nonzero-boundary-datum step absent from CoarseGraining.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem memVectorL2_cubeSet_of_openCubeSet {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    MemVectorL2 (cubeSet Q) F := by
  rw [MemVectorL2, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact hF

private theorem cubeAverageVec_grad_eq_boundaryData
    {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (v : DirichletForcedCubeSolution Q a g) :
    cubeAverageVec Q v.toH1.grad = cubeAverageVec Q v.boundaryData.grad := by
  have hz := cubeAverageVec_grad_eq_zero_of_h10OnCube Q
    v.zeroTraceDifferenceH10CubeSet
  have hae := cubeAverageVec_eq_of_ae_eq_on_cubeSet
    v.zeroTraceDifferenceH10CubeSet_grad_ae_eq
  have hsub := cubeAverageVec_sub Q v.toH1.grad v.boundaryData.grad
    (memVectorL2_cubeSet_of_openCubeSet v.toH1.grad_memVectorL2)
    (memVectorL2_cubeSet_of_openCubeSet v.boundaryData.grad_memVectorL2)
  rw [hae, hsub] at hz
  exact sub_eq_zero.mp hz

omit [NeZero d] in
private theorem publicParent_ae_eq_childCoeffOn
    (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    publicCoeffField Q a =ᵐ[volumeMeasureOn (openCubeSet R)]
      (a.coeffOn R).toCoeffField := by
  have hj : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have hRs : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_of_mem_descendantsAtDepth hR
  have hcompat := Ch02.coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict
    (a := a) hj hRs
  simpa [publicCoeffField, Ch02.pointwiseCoeffOnRestrict,
    Ch02.CoeffOn.AEEq] using hcompat.symm

private noncomputable def zeroForceReplacementAHarmonic
    (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (v : DirichletForcedCubeSolution R a (fun _ ↦ 0)) :
    AHarmonicFunction (publicCoeffField Q a) (openCubeSet R) where
  toH1 := v.toH1
  isHarmonic := by
    refine ⟨v.toH1.isPotentialOn, ?_⟩
    intro phi
    have hweak := v.weakSolution phi
    have hcoeff := publicParent_ae_eq_childCoeffOn Q a hR
    calc
      ∫ x in openCubeSet R,
          vecDot (matVecMul (publicCoeffField Q a x) (v.toH1.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet R,
          vecDot (matVecMul ((a.coeffOn R).toCoeffField x) (v.toH1.grad x))
            (phi.toH1Function.grad x) ∂volume := by
              apply integral_congr_ae
              filter_upwards [hcoeff] with x hx
              simp [hx]
      _ = ∫ x in openCubeSet R,
          vecDot ((fun _ : Vec d ↦ (0 : Vec d)) x)
            (phi.toH1Function.grad x) ∂volume := by
              simpa only [Ch02.cubeDomain_coe] using hweak
      _ = 0 := by simp [vecDot]

omit [NeZero d] in
private theorem cubeAverage_parentEnergy_eq_localizedChildEnergy
    (Q : TriadicCube d) (a : CoeffFamily d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (u : H1Function (openCubeSet R)) :
    cubeAverage R
        (coefficientEnergyDensity (publicCoeffField Q a) u.grad) =
      localizedCoeffEnergyValue (openCubeSet R) (a.coeffOn R) u := by
  have hcoeff := publicParent_ae_eq_childCoeffOn Q a hR
  have henergy :
      coefficientEnergyDensity (publicCoeffField Q a) u.grad
        =ᵐ[volumeMeasureOn (openCubeSet R)]
      coefficientEnergyDensity (a.coeffOn R).toCoeffField u.grad := by
    filter_upwards [hcoeff] with x hx
    simp [coefficientEnergyDensity, hx]
  calc
    cubeAverage R (coefficientEnergyDensity (publicCoeffField Q a) u.grad) =
        volumeAverage (openCubeSet R)
          (coefficientEnergyDensity (publicCoeffField Q a) u.grad) := by
      simp [cubeAverage, volumeAverage, volume_openCubeSet_eq_volume_cubeSet,
        volume_cubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = volumeAverage (openCubeSet R)
          (coefficientEnergyDensity (a.coeffOn R).toCoeffField u.grad) :=
      volumeAverage_eq_of_ae_eq henergy
    _ = localizedCoeffEnergyValue (openCubeSet R) (a.coeffOn R) u := rfl

/-- An arbitrary `H¹` scalar field has the same descendant coarse-gradient
control as its local harmonic replacements, with its own coefficient energy
on the right.  No pointwise ellipticity constant appears. -/
theorem cubeAverageGradientEnergyControl_of_h1Function_of_descendantSymmetry
    (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (openCubeSet Q))
    (hsymm : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j, ∀ᵐ x ∂volume.restrict (openCubeSet R),
      Matrix.IsSymm ((a.coeffOn R).toCoeffField x)) :
    CubeAverageGradientEnergyControl Q (publicCoeffField Q a) u.grad
      (coefficientEnergyDensity (publicCoeffField Q a) u.grad) := by
  intro j R hR
  let uR : H1Function (openCubeSet R) := u.restrictToOpenSubcube hR
  obtain ⟨v, hvBoundary, hvEnergy⟩ :=
    exists_zeroForceDirichletLift_energy_le R a uR (hsymm j R hR)
  let vH : AHarmonicFunction (publicCoeffField Q a) (openCubeSet R) :=
    zeroForceReplacementAHarmonic Q a hR v
  let vCube : AHarmonicFunction (publicCoeffField Q a) (cubeSet R) := vH.toCubeSet
  have hEllR := publicCoeffField_isEllipticFieldOn_descendant_cubeSet Q a hR
  have hDataR :=
    publicCoeffField_openCubeDeterministicCoarseData_descendant Q a hR
  have hcoarse :=
    cubeAverageGradient_le_coarseSigmaStarInvBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
      R (publicCoeffField Q a) hEllR hDataR vCube
  have havg : cubeAverageVec R v.toH1.grad = cubeAverageVec R u.grad := by
    rw [cubeAverageVec_grad_eq_boundaryData v, hvBoundary]
    rfl
  have henergyV :
      cubeAverage R
          (coefficientEnergyDensity (publicCoeffField Q a) v.toH1.grad) ≤
        cubeAverage R
          (coefficientEnergyDensity (publicCoeffField Q a) u.grad) := by
    rw [cubeAverage_parentEnergy_eq_localizedChildEnergy Q a hR v.toH1]
    have huR := cubeAverage_parentEnergy_eq_localizedChildEnergy Q a hR uR
    rw [show uR.grad = u.grad by rfl] at huR
    rw [huR]
    exact hvEnergy
  have hnorm : 0 ≤ coarseSigmaStarInvBlockNorm R (publicCoeffField Q a) :=
    coarseSigmaStarInvBlockNorm_nonneg R (publicCoeffField Q a)
  calc
    vecNormSq (cubeAverageVec R u.grad) =
        vecNormSq (cubeAverageVec R vCube.toH1.grad) := by
      rw [AHarmonicFunction.grad_toCubeSet]
      exact congrArg vecNormSq havg.symm
    _ ≤ coarseSigmaStarInvBlockNorm R (publicCoeffField Q a) *
          cubeAverage R (scalarVariationEnergyIntegrand
            (publicCoeffField Q a) vCube) := hcoarse
    _ = coarseSigmaStarInvBlockNorm R (publicCoeffField Q a) *
          cubeAverage R
            (coefficientEnergyDensity (publicCoeffField Q a) v.toH1.grad) := by
      congr 1
      apply cubeAverage_eq_of_eq_on_cubeSet
      intro x hx
      have hgrad : vCube.toH1.grad = v.toH1.grad := by
        rw [AHarmonicFunction.grad_toCubeSet]
        rfl
      simp only [scalarVariationEnergyIntegrand,
        coefficientEnergyDensity_eq_unsymmetrized]
      rw [hgrad]
      exact vecDot_matVecMul_symmPart _ _
    _ ≤ coarseSigmaStarInvBlockNorm R (publicCoeffField Q a) *
          cubeAverage R
            (coefficientEnergyDensity (publicCoeffField Q a) u.grad) :=
      mul_le_mul_of_nonneg_left henergyV hnorm


/-- Parent scalarity supplies every descendant symmetry used by replacement. -/
theorem cubeAverageGradientEnergyControl_of_h1Function_of_scalarParent
    (Q : TriadicCube d) (a : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (a.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H1Function (openCubeSet Q)) :
    CubeAverageGradientEnergyControl Q (publicCoeffField Q a) u.grad
      (coefficientEnergyDensity (publicCoeffField Q a) u.grad) := by
  apply cubeAverageGradientEnergyControl_of_h1Function_of_descendantSymmetry
  intro j R hR
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hscalar := ae_restrict_of_ae_restrict_of_subset hsub hb
  have hrestrict := a.restrictsTo_of_subset hsub
  filter_upwards [hscalar, hrestrict] with x hx hx2
  rw [hx2, hx]
  exact scalarMatrix_isSymm (b x)

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy

