module

public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import Homogenization.Internal.Ch02.Representatives
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import Homogenization.PDE.EnergyIdentities
public import Homogenization.CoarseGraining.OriginCubeOpenBridge

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
noncomputable section
namespace SubdiffusiveProcess.ScalarEnergyTransport

/-- Scalar coefficient energy is the scalar coefficient times squared Euclidean length. -/
theorem energy_density_eq {d : ℕ} (Q : TriadicCube d) {a : Vec d → ℝ}
    (data : ScalarCoeffOnData (Ch02.cubeDomain Q) a) (G : Vec d → Vec d) :
    coefficientEnergyDensity data.toCoeffOn.toCoeffField G =
      fun x => a x * vecNormSq (G x) := by
  funext x
  change vecDot (G x) (matVecMul (symmPart (scalarMatrix (a x))) (G x)) = _
  rw [Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix, vecDot_smul_right]
  rfl

/-- The public almost-everywhere coefficient carrier gives integrable H1 energy. -/
theorem integrable_energy {d : ℕ} (Q : TriadicCube d) {a : Vec d → ℝ}
    (data : ScalarCoeffOnData (Ch02.cubeDomain Q) a)
    (u : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => a x * vecNormSq (u.grad x)) (cubeSet Q) volume := by
  let A := data.toCoeffOn
  let b := Internal.Ch02.BookCh02.pointwiseCoeffOn (Ch02.cubeDomain Q) A
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn (Ch02.cubeDomain Q) A
  have hb : IntegrableOn (coefficientEnergyDensity b.toCoeffField u.grad) (openCubeSet Q) volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hba : b.toCoeffField =ᵐ[volume.restrict (openCubeSet Q)] A.toCoeffField := by
    simpa only [b, Ch02.CoeffOn.AEEq, Ch02.cubeDomain_coe, volumeMeasureOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Ch02.cubeDomain Q) A
  have ha : IntegrableOn (coefficientEnergyDensity A.toCoeffField u.grad) (openCubeSet Q) volume := by
    apply hb.congr
    filter_upwards [hba] with x hx
    simp only [coefficientEnergyDensity, hx]
  have ha' := (integrableOn_cubeSet_iff_integrableOn_openCubeSet (Q := Q)).2 ha
  simpa only [A, energy_density_eq Q data u.grad] using ha'

end SubdiffusiveProcess.ScalarEnergyTransport

