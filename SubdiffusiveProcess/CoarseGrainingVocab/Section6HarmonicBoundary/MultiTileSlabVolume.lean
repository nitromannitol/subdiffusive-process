module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SignedSlabPoincare

@[expose] public section

/-!
# Volumes of the multi-tile face slabs

`Section6HarmonicRadius/UniformFaceSlab.lean` computes the slab volume ratio
only for a **single** tile (`M = 1`).  A single tile cannot deliver the free
Young parameter of the route: with one tile of side `L`, the doubled
slab has volume `L^d`, so `volume P / volume W` grows like `(r/L)^d` and the
gradient coefficient `L^2 * (|P|/|W|)` grows like `r^2 (r/L)^{d-2}` as
`L → 0`.  The tile family must **cover the face**, i.e. `M * L` must equal the
tangential side of the patch; then `volume W = L * (M L)^{d-1}` and the
gradient coefficient is `L * r`, linear in the free parameter.

This file supplies the two volume facts for arbitrary `M` that the covering
family needs, in both signs of the face, together with the uniform ratio
`volume (doubled slab) / volume (inner slab) ≤ 2 ^ d`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The tiled doubled slab is the disjoint union of `card (FaceIndex d j0 M)`
axis cubes of side `L`. -/
theorem volume_faceDoubledSlab (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ}
    (hL : 0 < L) (M : ℕ) :
    volume (faceDoubledSlab j0 a b L M) =
      (Fintype.card (FaceIndex d j0 M) : ℝ≥0∞) * ENNReal.ofReal L ^ d := by
  classical
  rw [faceDoubledSlab, measure_iUnion (faceTiles_disjoint j0 a b hL)
    (fun k => (isOpen_axisCube _ _).measurableSet)]
  rw [tsum_fintype]
  simp [volume_axisCube, Finset.sum_const, nsmul_eq_mul]

/-- Each upper half tile sits inside the inner slab. -/
theorem axisCube_upperHalfTileCorner_subset_faceInnerSlab
    (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ) {M : ℕ}
    (k : FaceIndex d j0 M) :
    axisCube (upperHalfTileCorner j0 a b L k) (L / 2) ⊆
      faceInnerSlab j0 a b L M := by
  intro x hx
  refine ⟨?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨k, axisCube_upperHalf_subset_faceTile j0 a b k hx⟩
  · exact faceTile_upperHalf_outer j0 a b k x hx

/-- The inner slab has at least the volume of the disjoint half tiles. -/
theorem volume_faceInnerSlab_lower (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ}
    (hL : 0 < L) (M : ℕ) :
    (Fintype.card (FaceIndex d j0 M) : ℝ≥0∞) * ENNReal.ofReal (L / 2) ^ d ≤
      volume (faceInnerSlab j0 a b L M) := by
  classical
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun k : FaceIndex d j0 M =>
        axisCube (upperHalfTileCorner j0 a b L k) (L / 2))) := by
    intro k1 k2 hne
    exact ((faceTiles_disjoint j0 a b hL hne).mono
      (axisCube_upperHalf_subset_faceTile j0 a b k1)
      (axisCube_upperHalf_subset_faceTile j0 a b k2))
  have hunion : (⋃ k : FaceIndex d j0 M,
      axisCube (upperHalfTileCorner j0 a b L k) (L / 2)) ⊆
      faceInnerSlab j0 a b L M := by
    refine Set.iUnion_subset fun k => ?_
    exact axisCube_upperHalfTileCorner_subset_faceInnerSlab j0 a b L k
  have hmeas := measure_iUnion (μ := volume) hdisj
    (fun k => (isOpen_axisCube _ _).measurableSet)
  have hsum : volume (⋃ k : FaceIndex d j0 M,
      axisCube (upperHalfTileCorner j0 a b L k) (L / 2)) =
      (Fintype.card (FaceIndex d j0 M) : ℝ≥0∞) * ENNReal.ofReal (L / 2) ^ d := by
    rw [hmeas, tsum_fintype]
    simp [volume_axisCube, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact measure_mono hunion

/-- Uniform slab volume ratio, for **every** tile count. -/
theorem faceSlab_volumeRatio_le (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ}
    (hL : 0 < L) {M : ℕ} (hcard : 0 < Fintype.card (FaceIndex d j0 M)) :
    0 < (volume (faceInnerSlab j0 a b L M)).toReal ∧
      0 < (volume (faceDoubledSlab j0 a b L M)).toReal ∧
        (volume (faceDoubledSlab j0 a b L M)).toReal /
            (volume (faceInnerSlab j0 a b L M)).toReal ≤ (2 : ℝ) ^ d := by
  classical
  set N : ℝ := (Fintype.card (FaceIndex d j0 M) : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]; exact_mod_cast hcard
  have hWvol := volume_faceDoubledSlab j0 a b hL M
  have hWtop : volume (faceDoubledSlab j0 a b L M) ≠ ⊤ := by
    rw [hWvol]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hStop : volume (faceInnerSlab j0 a b L M) ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)
  have hWreal : (volume (faceDoubledSlab j0 a b L M)).toReal = N * L ^ d := by
    rw [hWvol]
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← ENNReal.ofReal_pow hL.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hSlower : N * (L / 2) ^ d ≤ (volume (faceInnerSlab j0 a b L M)).toReal := by
    have h := volume_faceInnerSlab_lower j0 a b hL M
    have := ENNReal.toReal_mono hStop h
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ L / 2),
      ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  have hSpos : 0 < (volume (faceInnerSlab j0 a b L M)).toReal := by
    have : 0 < N * (L / 2) ^ d := by positivity
    linarith
  have hWpos : 0 < (volume (faceDoubledSlab j0 a b L M)).toReal := by
    rw [hWreal]; positivity
  refine ⟨hSpos, hWpos, ?_⟩
  rw [div_le_iff₀ hSpos, hWreal]
  have hpow : N * L ^ d = (2 : ℝ) ^ d * (N * (L / 2) ^ d) := by
    rw [div_pow]
    field_simp
  have hmul : (2 : ℝ) ^ d * (N * (L / 2) ^ d) ≤
      (2 : ℝ) ^ d * (volume (faceInnerSlab j0 a b L M)).toReal :=
    mul_le_mul_of_nonneg_left hSlower (by positivity)
  linarith [hpow, hmul]

/-- Each lower half tile sits inside the upper-face inner slab. -/
theorem axisCube_faceTileCorner_subset_upperFaceInnerSlab
    (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ) {M : ℕ}
    (k : FaceIndex d j0 M) :
    axisCube (faceTileCorner j0 a b L k) (L / 2) ⊆
      upperFaceInnerSlab j0 a b L M := by
  intro x hx
  refine ⟨?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨k, axisCube_half_subset _ _ hx⟩
  · exact faceTile_half_outer j0 a b k x hx

/-- Lower bound for the upper-face inner slab. -/
theorem volume_upperFaceInnerSlab_lower (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ}
    (hL : 0 < L) (M : ℕ) :
    (Fintype.card (FaceIndex d j0 M) : ℝ≥0∞) * ENNReal.ofReal (L / 2) ^ d ≤
      volume (upperFaceInnerSlab j0 a b L M) := by
  classical
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun k : FaceIndex d j0 M =>
        axisCube (faceTileCorner j0 a b L k) (L / 2))) := by
    intro k1 k2 hne
    exact ((faceTiles_disjoint j0 a b hL hne).mono
      (axisCube_half_subset _ _) (axisCube_half_subset _ _))
  have hunion : (⋃ k : FaceIndex d j0 M,
      axisCube (faceTileCorner j0 a b L k) (L / 2)) ⊆
      upperFaceInnerSlab j0 a b L M := by
    refine Set.iUnion_subset fun k => ?_
    exact axisCube_faceTileCorner_subset_upperFaceInnerSlab j0 a b L k
  have hmeas := measure_iUnion (μ := volume) hdisj
    (fun k => (isOpen_axisCube _ _).measurableSet)
  have hsum : volume (⋃ k : FaceIndex d j0 M,
      axisCube (faceTileCorner j0 a b L k) (L / 2)) =
      (Fintype.card (FaceIndex d j0 M) : ℝ≥0∞) * ENNReal.ofReal (L / 2) ^ d := by
    rw [hmeas, tsum_fintype]
    simp [volume_axisCube, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact measure_mono hunion

/-- Uniform upper-face slab volume ratio, for every tile count. -/
theorem upperFaceSlab_volumeRatio_le (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ}
    (hL : 0 < L) {M : ℕ} (hcard : 0 < Fintype.card (FaceIndex d j0 M)) :
    0 < (volume (upperFaceInnerSlab j0 a b L M)).toReal ∧
      0 < (volume (faceDoubledSlab j0 a b L M)).toReal ∧
        (volume (faceDoubledSlab j0 a b L M)).toReal /
            (volume (upperFaceInnerSlab j0 a b L M)).toReal ≤ (2 : ℝ) ^ d := by
  classical
  set N : ℝ := (Fintype.card (FaceIndex d j0 M) : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]; exact_mod_cast hcard
  have hWvol := volume_faceDoubledSlab j0 a b hL M
  have hWtop : volume (faceDoubledSlab j0 a b L M) ≠ ⊤ := by
    rw [hWvol]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hStop : volume (upperFaceInnerSlab j0 a b L M) ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)
  have hWreal : (volume (faceDoubledSlab j0 a b L M)).toReal = N * L ^ d := by
    rw [hWvol]
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← ENNReal.ofReal_pow hL.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hSlower : N * (L / 2) ^ d ≤
      (volume (upperFaceInnerSlab j0 a b L M)).toReal := by
    have h := volume_upperFaceInnerSlab_lower j0 a b hL M
    have := ENNReal.toReal_mono hStop h
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ L / 2),
      ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  have hSpos : 0 < (volume (upperFaceInnerSlab j0 a b L M)).toReal := by
    have : 0 < N * (L / 2) ^ d := by positivity
    linarith
  have hWpos : 0 < (volume (faceDoubledSlab j0 a b L M)).toReal := by
    rw [hWreal]; positivity
  refine ⟨hSpos, hWpos, ?_⟩
  rw [div_le_iff₀ hSpos, hWreal]
  have hpow : N * L ^ d = (2 : ℝ) ^ d * (N * (L / 2) ^ d) := by
    rw [div_pow]
    field_simp
  have hmul : (2 : ℝ) ^ d * (N * (L / 2) ^ d) ≤
      (2 : ℝ) ^ d * (volume (upperFaceInnerSlab j0 a b L M)).toReal :=
    mul_le_mul_of_nonneg_left hSlower (by positivity)
  linarith [hpow, hmul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
