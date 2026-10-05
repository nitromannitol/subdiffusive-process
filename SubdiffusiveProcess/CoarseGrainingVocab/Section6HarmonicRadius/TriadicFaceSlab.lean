module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius.UniformFaceSlab

@[expose] public section

/-!
# One-tile slabs on triadic boundary parents

This file identifies the geometric `P` in the radius-uniform mean row with an
open triadic cube.  The lower and upper constructions use the corresponding
half of a doubled tile centred on one face of the cube.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-- Lower corner of the axis-cube realization of a triadic cube. -/
noncomputable def triadicLowerCorner (Q : TriadicCube d) : Vec d :=
  fun i ↦ ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q

theorem openCubeSet_eq_axisCube_lowerCorner (Q : TriadicCube d) :
    openCubeSet Q = axisCube (triadicLowerCorner Q) (cubeScaleFactor Q) := by
  simpa only [triadicLowerCorner] using! openCubeSet_eq_axisCube Q

/-- The inner half of the doubled tile at a lower face lies in the triadic
parent. -/
theorem lowerFaceInnerSlab_subset_openCubeSet
    (Q : TriadicCube d) (i : Fin d) :
    faceInnerSlab i (triadicLowerCorner Q i) (triadicLowerCorner Q)
        (cubeScaleFactor Q) 1 ⊆ openCubeSet Q := by
  intro x hx
  rw [openCubeSet_eq_axisCube_lowerCorner]
  simp only [faceInnerSlab, faceDoubledSlab, Set.mem_inter_iff,
    Set.mem_iUnion, Set.mem_ofPred_eq] at hx
  obtain ⟨⟨k, hk⟩, hxi⟩ := hx
  simp only [axisCube, Set.mem_univ_pi, Set.mem_Ioo] at hk ⊢
  intro j
  by_cases hji : j = i
  · subst j
    have hki := hk i
    rw [faceTileCorner_normal] at hki
    exact ⟨hxi, by linarith [hki.2]⟩
  · have hcorner := faceTileCorner_tangential
      i (triadicLowerCorner Q i) (triadicLowerCorner Q)
        (cubeScaleFactor Q) k ⟨j, hji⟩
    have hkzero : (k ⟨j, hji⟩ : ℕ) = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (k ⟨j, hji⟩).isLt)
    have hc : faceTileCorner i (triadicLowerCorner Q i)
        (triadicLowerCorner Q) (cubeScaleFactor Q) k j = triadicLowerCorner Q j := by
      simpa only [hkzero, Nat.cast_zero, mul_zero, add_zero] using hcorner
    have hkj := hk j
    rw [hc] at hkj
    exact hkj

/-- The inner half of the doubled tile at an upper face lies in the triadic
parent. -/
theorem upperFaceInnerSlab_subset_openCubeSet
    (Q : TriadicCube d) (i : Fin d) :
    upperFaceInnerSlab i
        (triadicLowerCorner Q i + cubeScaleFactor Q)
        (triadicLowerCorner Q) (cubeScaleFactor Q) 1 ⊆ openCubeSet Q := by
  intro x hx
  rw [openCubeSet_eq_axisCube_lowerCorner]
  simp only [upperFaceInnerSlab, faceDoubledSlab, Set.mem_inter_iff,
    Set.mem_iUnion, Set.mem_ofPred_eq] at hx
  obtain ⟨⟨k, hk⟩, hxi⟩ := hx
  simp only [axisCube, Set.mem_univ_pi, Set.mem_Ioo] at hk ⊢
  intro j
  by_cases hji : j = i
  · subst j
    have hki := hk i
    rw [faceTileCorner_normal] at hki
    constructor
    · have hscale := cubeScaleFactor_pos Q
      linarith [hki.1]
    · exact hxi
  · have hcorner := faceTileCorner_tangential i
      (triadicLowerCorner Q i + cubeScaleFactor Q) (triadicLowerCorner Q)
        (cubeScaleFactor Q) k ⟨j, hji⟩
    have hkzero : (k ⟨j, hji⟩ : ℕ) = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (k ⟨j, hji⟩).isLt)
    have hc : faceTileCorner i
        (triadicLowerCorner Q i + cubeScaleFactor Q) (triadicLowerCorner Q)
        (cubeScaleFactor Q) k j = triadicLowerCorner Q j := by
      simpa only [hkzero, Nat.cast_zero, mul_zero, add_zero] using hcorner
    have hkj := hk j
    rw [hc] at hkj
    exact hkj

/-- Lower-face radius-uniform residual-mean row on a triadic parent. -/
theorem sq_averageOn_openCubeSet_lowerFace_le
    (Q : TriadicCube d) (i : Fin d)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : IntegrableOn f (openCubeSet Q))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (openCubeSet Q))
    (hH1 : ∀ k : FaceIndex d i 1,
      ∃ v : H1Function
          (axisCube (faceTileCorner i (triadicLowerCorner Q i)
            (triadicLowerCorner Q) (cubeScaleFactor Q) k)
            (cubeScaleFactor Q)),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, x i < triadicLowerCorner Q i → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab i (triadicLowerCorner Q i) (triadicLowerCorner Q)
        (cubeScaleFactor Q) 1)) :
    averageOn (openCubeSet Q) f ^ 2 ≤
      2 * ((tilePoincareConst d (cubeScaleFactor Q) ^ 2 * d) *
          (2 : ℝ) ^ d) *
        volumeAverage
          (faceDoubledSlab i (triadicLowerCorner Q i) (triadicLowerCorner Q)
            (cubeScaleFactor Q) 1) (fun x => vecNormSq (G x)) +
      2 * (2 : ℝ) ^ d * normalizedL2On (openCubeSet Q)
        (fun x ↦ f x - averageOn (openCubeSet Q) f) ^ 2 := by
  rw [openCubeSet_eq_axisCube_lowerCorner] at hf hf2 ⊢
  have hsub : faceInnerSlab i (triadicLowerCorner Q i) (triadicLowerCorner Q)
      (cubeScaleFactor Q) 1 ⊆ axisCube (triadicLowerCorner Q) (cubeScaleFactor Q) := by
    simpa only [openCubeSet_eq_axisCube_lowerCorner] using
      lowerFaceInnerSlab_subset_openCubeSet Q i
  exact sq_averageOn_axisCube_oneTile_lowerFace_le i
    (triadicLowerCorner Q i) (triadicLowerCorner Q) (triadicLowerCorner Q)
    (cubeScaleFactor_pos Q)
    hsub hf hf2 hH1 hfzero hgW

/-- Upper-face radius-uniform residual-mean row on a triadic parent. -/
theorem sq_averageOn_openCubeSet_upperFace_le
    (Q : TriadicCube d) (i : Fin d)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : IntegrableOn f (openCubeSet Q))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (openCubeSet Q))
    (hH1 : ∀ k : FaceIndex d i 1,
      ∃ v : H1Function
          (axisCube (faceTileCorner i
            (triadicLowerCorner Q i + cubeScaleFactor Q)
            (triadicLowerCorner Q) (cubeScaleFactor Q) k)
            (cubeScaleFactor Q)),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d,
      triadicLowerCorner Q i + cubeScaleFactor Q < x i → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab i
        (triadicLowerCorner Q i + cubeScaleFactor Q) (triadicLowerCorner Q)
          (cubeScaleFactor Q) 1)) :
    averageOn (openCubeSet Q) f ^ 2 ≤
      2 * ((tilePoincareConst d (cubeScaleFactor Q) ^ 2 * d) *
          (2 : ℝ) ^ d) *
        volumeAverage
          (faceDoubledSlab i
            (triadicLowerCorner Q i + cubeScaleFactor Q) (triadicLowerCorner Q)
              (cubeScaleFactor Q) 1) (fun x => vecNormSq (G x)) +
      2 * (2 : ℝ) ^ d * normalizedL2On (openCubeSet Q)
        (fun x ↦ f x - averageOn (openCubeSet Q) f) ^ 2 := by
  rw [openCubeSet_eq_axisCube_lowerCorner] at hf hf2 ⊢
  have hsub : upperFaceInnerSlab i
      (triadicLowerCorner Q i + cubeScaleFactor Q) (triadicLowerCorner Q)
      (cubeScaleFactor Q) 1 ⊆ axisCube (triadicLowerCorner Q) (cubeScaleFactor Q) := by
    simpa only [openCubeSet_eq_axisCube_lowerCorner] using
      upperFaceInnerSlab_subset_openCubeSet Q i
  exact sq_averageOn_axisCube_oneTile_upperFace_le i
    (triadicLowerCorner Q i + cubeScaleFactor Q)
      (triadicLowerCorner Q) (triadicLowerCorner Q) (cubeScaleFactor_pos Q)
    hsub hf hf2 hH1 hfzero hgW

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius
