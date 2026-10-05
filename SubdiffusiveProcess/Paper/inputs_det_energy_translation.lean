module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellCover
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

theorem inputs_det_energy_translation (d : ℕ) [NeZero d]
    (a : Vec d → ℝ) (y : Vec d)
    (data : ScalarTriadicCoeffData (fun q => a (q + y))) (k : ℤ)
    (u0 : H1Function (openCubeSet (originCube d k)))
    (G : Vec d → Vec d) (hG : ∀ q, u0.grad q = G (q + y)) :
    (cubeAverage (originCube d k)
      (coefficientEnergyDensity
        (data.toTriadicCoeffFamily.coeffOn (originCube d k)).toCoeffField u0.grad) =
      normalizedSetAverage (translatedCube d k y) (fun q => a q * vecNormSq (G q))) := by
  have hfun : coefficientEnergyDensity
      (data.toTriadicCoeffFamily.coeffOn (originCube d k)).toCoeffField u0.grad =
      fun x => a (x + y) * vecNormSq (G (x + y)) := by
    funext x
    change vecDot (u0.grad x)
      (matVecMul (symmPart (scalarMatrix (d := d) (a (x + y)))) (u0.grad x)) = _
    rw [Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix, vecDot_smul_right, hG]
    rfl
  rw [hfun, SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.cubeAverage_comp_addRight_eq_volumeAverage_translateSet
    (originCube d k) y (fun q => a q * vecNormSq (G q))]
  have hset : translateSet y (openCubeSet (originCube d k)) = translatedCube d k y := by
    rw [translatedCube, cube, SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet]
  rw [hset]

end SubdiffusiveProcess.Paper
