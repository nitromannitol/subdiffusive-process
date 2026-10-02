import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius.TriadicFaceSlab
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryTraceMeasure

/-!
# Translated zero-extension carrier for face slabs

The physical Dirichlet difference is an `H¹₀` function on the ambient
domain.  Its zero extension, pulled back by the projected-cell translation,
is an `H¹` function on every comparison tile.  This supplies the common
function and gradient required by the one-tile slab rows.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-- Pull the global zero extension back to a frame translated by `c`. -/
noncomputable def translatedZeroExtendH1 {V : Set (Vec d)}
    (hV : MeasurableSet V) (rho : H10Function V) (c : Vec d)
    (A : Set (Vec d)) : H1Function A :=
  H1Function.untranslate c (zeroExtendH1 hV rho (translateSet c A))

@[simp] theorem translatedZeroExtendH1_toFun {V : Set (Vec d)}
    (hV : MeasurableSet V) (rho : H10Function V) (c : Vec d)
    (A : Set (Vec d)) (x : Vec d) :
    (translatedZeroExtendH1 hV rho c A).toFun x =
      zeroExtend V rho.toH1Function.toFun (x + c) := rfl

@[simp] theorem translatedZeroExtendH1_grad {V : Set (Vec d)}
    (hV : MeasurableSet V) (rho : H10Function V) (c : Vec d)
    (A : Set (Vec d)) (x : Vec d) :
    (translatedZeroExtendH1 hV rho c A).grad x =
      zeroExtendGrad V rho.toH1Function.grad (x + c) := rfl

/-- Lower-face slab row for a translated global zero extension. -/
theorem sq_averageOn_translatedZeroExtend_lowerFace_le
    {V : Set (Vec d)} (hV : MeasurableSet V) (rho : H10Function V)
    (c : Vec d) (Q : TriadicCube d) (i : Fin d)
    (houtside : ∀ x : Vec d, x i < triadicLowerCorner Q i → x + c ∉ V) :
    averageOn (openCubeSet Q)
        (fun x ↦ zeroExtend V rho.toH1Function.toFun (x + c)) ^ 2 ≤
      2 * ((tilePoincareConst d (cubeScaleFactor Q) ^ 2 * d) *
          (2 : ℝ) ^ d) *
        volumeAverage
          (faceDoubledSlab i (triadicLowerCorner Q i) (triadicLowerCorner Q)
            (cubeScaleFactor Q) 1)
          (fun x ↦ vecNormSq
            (zeroExtendGrad V rho.toH1Function.grad (x + c))) +
      2 * (2 : ℝ) ^ d * normalizedL2On (openCubeSet Q)
        (fun x ↦ zeroExtend V rho.toH1Function.toFun (x + c) -
          averageOn (openCubeSet Q)
            (fun y ↦ zeroExtend V rho.toH1Function.toFun (y + c))) ^ 2 := by
  let f : Vec d → ℝ := fun x ↦ zeroExtend V rho.toH1Function.toFun (x + c)
  let G : Vec d → Vec d := fun x ↦ zeroExtendGrad V rho.toH1Function.grad (x + c)
  let uP := translatedZeroExtendH1 hV rho c (openCubeSet Q)
  letI : IsFiniteMeasure (volume.restrict (openCubeSet Q)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top Q
  have hf : IntegrableOn f (openCubeSet Q) := by
    exact uP.memL2.integrable (by norm_num)
  have hf2 : IntegrableOn (fun x ↦ f x ^ 2) (openCubeSet Q) := by
    simpa only [IntegrableOn] using uP.memL2.integrable_sq
  have hH1 : ∀ k : FaceIndex d i 1,
      ∃ v : H1Function
          (axisCube (faceTileCorner i (triadicLowerCorner Q i)
            (triadicLowerCorner Q) (cubeScaleFactor Q) k)
            (cubeScaleFactor Q)),
        v.toFun = f ∧ v.grad = G := by
    intro k
    let A := axisCube (faceTileCorner i (triadicLowerCorner Q i)
      (triadicLowerCorner Q) (cubeScaleFactor Q) k) (cubeScaleFactor Q)
    refine ⟨translatedZeroExtendH1 hV rho c A, ?_, ?_⟩
    · exact funext fun x ↦ rfl
    · exact funext fun x ↦ rfl
  have hfzero : ∀ x : Vec d, x i < triadicLowerCorner Q i → f x = 0 := by
    intro x hx
    exact zeroExtend_of_notMem _ (houtside x hx)
  let W := faceDoubledSlab i (triadicLowerCorner Q i) (triadicLowerCorner Q)
    (cubeScaleFactor Q) 1
  let uW := translatedZeroExtendH1 hV rho c W
  have hgW : IntegrableOn (fun x ↦ vecNormSq (G x)) W := by
    have hcomp : ∀ j, IntegrableOn (fun x ↦ uW.grad x j ^ 2) W :=
      fun j ↦ (uW.gradMemL2 j).integrable_sq
    have hsum : IntegrableOn (fun x ↦ ∑ j, uW.grad x j ^ 2) W :=
      integrable_finset_sum Finset.univ (fun j _ ↦ hcomp j)
    simpa only [G, uW, vecNormSq, vecDot, pow_two,
      translatedZeroExtendH1_grad] using hsum
  simpa only [f, G, W] using
    sq_averageOn_openCubeSet_lowerFace_le Q i hf hf2 hH1 hfzero hgW

/-- Upper-face slab row for a translated global zero extension. -/
theorem sq_averageOn_translatedZeroExtend_upperFace_le
    {V : Set (Vec d)} (hV : MeasurableSet V) (rho : H10Function V)
    (c : Vec d) (Q : TriadicCube d) (i : Fin d)
    (houtside : ∀ x : Vec d,
      triadicLowerCorner Q i + cubeScaleFactor Q < x i → x + c ∉ V) :
    averageOn (openCubeSet Q)
        (fun x ↦ zeroExtend V rho.toH1Function.toFun (x + c)) ^ 2 ≤
      2 * ((tilePoincareConst d (cubeScaleFactor Q) ^ 2 * d) *
          (2 : ℝ) ^ d) *
        volumeAverage
          (faceDoubledSlab i
            (triadicLowerCorner Q i + cubeScaleFactor Q) (triadicLowerCorner Q)
              (cubeScaleFactor Q) 1)
          (fun x ↦ vecNormSq
            (zeroExtendGrad V rho.toH1Function.grad (x + c))) +
      2 * (2 : ℝ) ^ d * normalizedL2On (openCubeSet Q)
        (fun x ↦ zeroExtend V rho.toH1Function.toFun (x + c) -
          averageOn (openCubeSet Q)
            (fun y ↦ zeroExtend V rho.toH1Function.toFun (y + c))) ^ 2 := by
  let f : Vec d → ℝ := fun x ↦ zeroExtend V rho.toH1Function.toFun (x + c)
  let G : Vec d → Vec d := fun x ↦ zeroExtendGrad V rho.toH1Function.grad (x + c)
  let uP := translatedZeroExtendH1 hV rho c (openCubeSet Q)
  letI : IsFiniteMeasure (volume.restrict (openCubeSet Q)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top Q
  have hf : IntegrableOn f (openCubeSet Q) := uP.memL2.integrable (by norm_num)
  have hf2 : IntegrableOn (fun x ↦ f x ^ 2) (openCubeSet Q) := by
    simpa only [IntegrableOn] using uP.memL2.integrable_sq
  have hH1 : ∀ k : FaceIndex d i 1,
      ∃ v : H1Function
          (axisCube (faceTileCorner i
            (triadicLowerCorner Q i + cubeScaleFactor Q)
            (triadicLowerCorner Q) (cubeScaleFactor Q) k)
            (cubeScaleFactor Q)),
        v.toFun = f ∧ v.grad = G := by
    intro k
    let A := axisCube (faceTileCorner i
      (triadicLowerCorner Q i + cubeScaleFactor Q)
      (triadicLowerCorner Q) (cubeScaleFactor Q) k) (cubeScaleFactor Q)
    exact ⟨translatedZeroExtendH1 hV rho c A, funext fun x ↦ rfl,
      funext fun x ↦ rfl⟩
  have hfzero : ∀ x : Vec d,
      triadicLowerCorner Q i + cubeScaleFactor Q < x i → f x = 0 := by
    intro x hx
    exact zeroExtend_of_notMem _ (houtside x hx)
  let W := faceDoubledSlab i
    (triadicLowerCorner Q i + cubeScaleFactor Q) (triadicLowerCorner Q)
      (cubeScaleFactor Q) 1
  let uW := translatedZeroExtendH1 hV rho c W
  have hgW : IntegrableOn (fun x ↦ vecNormSq (G x)) W := by
    have hcomp : ∀ j, IntegrableOn (fun x ↦ uW.grad x j ^ 2) W :=
      fun j ↦ (uW.gradMemL2 j).integrable_sq
    have hsum : IntegrableOn (fun x ↦ ∑ j, uW.grad x j ^ 2) W :=
      integrable_finset_sum Finset.univ (fun j _ ↦ hcomp j)
    simpa only [G, uW, vecNormSq, vecDot, pow_two,
      translatedZeroExtendH1_grad] using hsum
  simpa only [f, G, W] using
    sq_averageOn_openCubeSet_upperFace_le Q i hf hf2 hH1 hfzero hgW

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius
