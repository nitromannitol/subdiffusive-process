module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCommonAverage
public import Homogenization.PDE.DirichletRHS

@[expose] public section

/-!
# Removing the constant mode of the boundary forcing

The manuscript centers the forcing before the boundary Caccioppoli argument:
constants have zero divergence, while the fractional seminorm is unchanged.
This module records that reduction in the Chapter-3 carriers.

PROVENANCE: this is the constant-force reduction immediately before the
boundary estimate in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryOuterCaccioppoli.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}



private noncomputable def boundaryWspFieldOfFull
    {Q : TriadicCube d} {s : FractionalOrder} {g : Vec d → Vec d}
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two g) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := g
  euclideanMemLp := hg.1
  euclideanMemWsp := hg.2

@[simp] private theorem boundaryWspFieldOfFull_toField
    {Q : TriadicCube d} {s : FractionalOrder} {g : Vec d → Vec d}
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two g) :
    (boundaryWspFieldOfFull hg).toField = g := rfl

/-- The v5 inhomogeneous fractional carrier supplies positive-Besov
regularity at every lower exponent. -/
theorem forceBesovRegularity_of_memCubeEuclideanFullWsp_of_exponent_le
    [NeZero d] {Q : TriadicCube d} {s : FractionalOrder} {t : ℝ}
    {g : Vec d → Vec d}
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two g) (hts : t ≤ s.1) :
    ForceBesovRegularity Q t g := by
  have hsob := cubeEuclideanWspField_forceSobolevRegularity s
    (boundaryWspFieldOfFull hg)
  have hreg : ForceBesovRegularity Q s.1 g := by
    simpa using hsob.toForceBesovRegularity s.2.1 s.2.2.le
  exact hreg.of_exponent_le hts

/-- Subtracting the parent cube average preserves the public positive-Besov
regularity package. -/
theorem forceBesovRegularity_cubeFluctuationVec
    {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g) :
    ForceBesovRegularity Q s (cubeFluctuationVec Q g) where
  memLp := memLp_cubeFluctuationVec Q g hg.memLp
  partialSeminorms_bddAbove := by
    rcases hg.partialSeminorms_bddAbove with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro _ ⟨N, rfl⟩
    have hmem :
        ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
          MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
      intro j _ R hR
      exact memLp_on_descendant_of_memLp_generic hR hg.memLp
    change cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x ↦ g x - cubeAverageVec Q g) ≤ B
    rw [cubeBesovPositiveVectorPartialSeminormTwo_sub_const
        Q s N g (cubeAverageVec Q g) hmem]
    exact hB ⟨N, rfl⟩

/-- The normalized positive seminorm is exactly invariant under removal of
the parent constant mode. -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_cubeFluctuationVec
    {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s (cubeFluctuationVec Q g) =
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
  unfold scaleNormalizedPositiveBesovVectorSeminormTwo
  rw [show cubeFluctuationVec Q g =
      (fun x ↦ g x - cubeAverageVec Q g) by rfl,
    cubeBesovPositiveVectorSeminormTwo_sub_const Q s g
      (cubeAverageVec Q g) (fun j R hR ↦
        memLp_on_descendant_of_memLp_generic hR hg.memLp)]

/-- After centering, the Euclidean `L²` term in the inhomogeneous weak-flux
estimate is controlled by the same positive fractional seminorm. -/
theorem boundaryNormalizedEuclideanL2_cubeFluctuationVec_le
    {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g) :
    boundaryNormalizedEuclideanL2 Q (cubeFluctuationVec Q g) ≤
      Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
  let gc := cubeFluctuationVec Q g
  have hgc : ForceBesovRegularity Q s gc :=
    forceBesovRegularity_cubeFluctuationVec hg
  have hgcAvg : cubeAverageVec Q gc = 0 := by
    change cubeAverageVec Q (fun x ↦ g x - cubeAverageVec Q g) = 0
    rw [cubeAverageVec_sub_const Q g (cubeAverageVec Q g) hg.memLp]
    exact sub_self _
  have hsq : boundaryNormalizedEuclideanL2 Q gc ^ (2 : ℕ) =
      cubeAverage Q (fun x ↦ vecNormSq (gc x)) := by
    have hF := memVectorL2_cubeSet_of_forceBesovRegularity hgc
    have hHilbert : MemLp (fun x ↦ HilbertVec.ofVec (gc x)) 2
        (volumeMeasureOn (cubeSet Q)) := memHilbertVectorL2_hilbertifyVecField hF
    have hmem : MemLp (fun x ↦ HilbertVec.ofVec (gc x)) 2
        (normalizedCubeMeasure Q) := by
      simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure] using
        hHilbert.smul_measure ENNReal.ofReal_ne_top
    have hbase := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
      (Q := Q) (p := (2 : ℝ≥0∞)) (f := fun x ↦ HilbertVec.ofVec (gc x))
      (by norm_num) (by norm_num) hmem
    rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num] at hbase
    simp only [Real.rpow_natCast] at hbase
    rw [boundaryNormalizedEuclideanL2, hbase]
    apply congrArg (cubeAverage Q)
    funext x
    rw [HilbertVec.norm_sq_ofVec]
    rfl
  have hnorm : scaleNormalizedPositiveBesovVectorNormTwo Q s gc =
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    rw [hgcAvg]
    have hz : vecNormSq (0 : Vec d) = 0 := by
      simp [vecNormSq, vecDot]
    rw [hz, Real.sqrt_zero, zero_add,
      scaleNormalizedPositiveBesovVectorSeminormTwo_cubeFluctuationVec hg]
  calc
    boundaryNormalizedEuclideanL2 Q gc =
        Real.sqrt (cubeAverage Q (fun x ↦ vecNormSq (gc x))) := by
      rw [← hsq, Real.sqrt_sq (boundaryNormalizedEuclideanL2_nonneg Q gc)]
    _ ≤ Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s gc :=
      sqrt_cubeAverage_vecNormSq_le_sqrt_card_mul_scaleNormalizedPositiveBesovVectorNormTwo
        hgc
    _ = Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by rw [hnorm]

private theorem memVectorL2_openCubeSet_of_forceBesovRegularity
    {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g) : MemVectorL2 (openCubeSet Q) g := by
  have h := memVectorL2_cubeSet_of_forceBesovRegularity hg
  rw [MemVectorL2, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at h
  exact h

/-- The Chapter-3 forced equation is unchanged when the parent average of
the vector forcing is removed. -/
theorem isForcedEquation_cubeFluctuationVec
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
    {u : H1Function (openCubeSet Q)}
    (hg : ForceBesovRegularity Q s g) (hu : IsForcedEquation Q a u g) :
    IsForcedEquation Q a u (cubeFluctuationVec Q g) := by
  intro phi
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (g x) (phi.toH1Function.grad x) ∂volume := hu phi
    _ = ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (cubeFluctuationVec Q g x) (phi.toH1Function.grad x) ∂volume := by
      rw [show cubeFluctuationVec Q g =
          (fun x ↦ g x - cubeAverageVec Q g) by rfl]
      symm
      simpa only [Ch02.cubeDomain_coe] using
        integral_vecDot_sub_const_zeroTraceGrad_eq
          (U := openCubeSet Q)
          (memVectorL2_openCubeSet_of_forceBesovRegularity hg) phi
          (cubeAverageVec Q g)

/-- Repackage a forced solution with its divergence-equivalent centered
forcing. The represented `H¹` function and gradient are definitionally
unchanged. -/
noncomputable def centeredForcedCubeSolution
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) (hg : ForceBesovRegularity Q s g) :
    ForcedCubeSolution Q a (cubeFluctuationVec Q g) where
  toH1 := u.toH1
  weakSolution := isForcedEquation_cubeFluctuationVec hg u.weakSolution

@[simp] theorem centeredForcedCubeSolution_toH1
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) (hg : ForceBesovRegularity Q s g) :
    (centeredForcedCubeSolution u hg).toH1 = u.toH1 :=
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
