module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveIntegrability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoEnergyCover

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The pointwise identity behind the weighted energy readout. -/
theorem euclideanNorm_sqrt_smul_sq (a : Vec d → ℝ) (v : Vec d → Vec d)
    (ha : ∀ x, 0 ≤ a x) (x : Vec d) :
    Homogenization.euclideanNorm (Real.sqrt (a x) • v x) ^ 2 =
      a x * vecNormSq (v x) := by
  rw [euclideanNorm_smul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    euclideanNorm_sq, Real.sq_sqrt (ha x)]

/-- **The energy cover's integrability hypothesis, discharged.**  Holds for every
window centre `y` and every scale `j`, with no hypothesis at all. -/
theorem integrableOn_weightedGrad_sq
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m : ℤ)
    (u : H1Function (openCubeSet (originCube d m))) (j : ℤ) (y : Vec d) :
    IntegrableOn
      (fun p ↦ Homogenization.euclideanNorm
        (Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) • u.grad p) ^ 2)
      (truncatedCube d m j y) volume := by
  have hbase :
      IntegrableOn (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
        vecNormSq (u.grad x)) (truncatedCube d m j y) volume :=
    (integrableOn_aCutoff_energy M L omega (originCube d m) u).mono_set
      (Section6ExcessDecay.truncatedCube_subset_cube d m j y)
  refine hbase.congr_fun ?_ (Section6ExcessDecay.measurableSet_truncatedCube d m j y)
  intro x _
  exact (euclideanNorm_sqrt_smul_sq
    (fun p ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega p) u.grad
    (fun p ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega p).le) x).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
