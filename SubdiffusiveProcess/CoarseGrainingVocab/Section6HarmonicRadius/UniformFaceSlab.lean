import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SignedSlabPoincare

/-!
# Radius-uniform one-tile face slabs

For the physical radius recurrence the face slab is chosen at the adaptive
cell scale.  Thus its parent is one doubled tile, not the fixed macroscopic
projected cube.  The inner slab contains a half-side axis cube, so both volume
ratios in the residual-mean row are bounded by `2 ^ d`, independently of the
tile side.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

private noncomputable def oneFaceIndex (j0 : Fin d) : FaceIndex d j0 1 :=
  fun _ => 0

private theorem faceDoubledSlab_one_eq_axisCube
    (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ) :
    faceDoubledSlab j0 a b L 1 =
      axisCube (faceTileCorner j0 a b L (oneFaceIndex j0)) L := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [faceDoubledSlab, Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    simpa only [Subsingleton.elim k (oneFaceIndex j0)] using hk
  · intro x hx
    simp only [faceDoubledSlab, Set.mem_iUnion]
    exact ⟨oneFaceIndex j0, hx⟩

private theorem upperHalfTile_subset_faceInnerSlab_one
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} :
    axisCube (upperHalfTileCorner j0 a b L (oneFaceIndex j0)) (L / 2) ⊆
      faceInnerSlab j0 a b L 1 := by
  intro x hx
  refine ⟨?_, faceTile_upperHalf_outer j0 a b (oneFaceIndex j0) x hx⟩
  rw [faceDoubledSlab_one_eq_axisCube]
  exact axisCube_upperHalf_subset_faceTile j0 a b (oneFaceIndex j0) hx

/-- A one-tile lower-face slab has positive inner and doubled volume, and the
doubled-to-inner volume ratio is bounded by the dimension-only factor
`2 ^ d`. -/
theorem oneTile_lowerFaceSlab_volumeRatio_le
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) :
    0 < (volume (faceInnerSlab j0 a b L 1)).toReal ∧
      0 < (volume (faceDoubledSlab j0 a b L 1)).toReal ∧
      (volume (faceDoubledSlab j0 a b L 1)).toReal /
          (volume (faceInnerSlab j0 a b L 1)).toReal ≤ (2 : ℝ) ^ d := by
  let k : FaceIndex d j0 1 := oneFaceIndex j0
  let H := axisCube (upperHalfTileCorner j0 a b L k) (L / 2)
  let W := faceDoubledSlab j0 a b L 1
  let S := faceInnerSlab j0 a b L 1
  have hHsub : H ⊆ S := by
    simpa only [H, S, k] using
      upperHalfTile_subset_faceInnerSlab_one (j0 := j0) (a := a) (b := b) (L := L)
  have hHpos : 0 < (volume H).toReal := by
    dsimp only [H]
    exact volume_axisCube_toReal_pos _ (by positivity)
  have hWtop : volume W ≠ ⊤ := by
    rw [show W = axisCube (faceTileCorner j0 a b L k) L by
      simpa only [W, k] using faceDoubledSlab_one_eq_axisCube j0 a b L]
    exact volume_axisCube_ne_top _ L
  have hStop : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)
  have hSpos : 0 < (volume S).toReal := by
    exact lt_of_lt_of_le hHpos
      (ENNReal.toReal_mono hStop (measure_mono hHsub))
  have hWpos : 0 < (volume W).toReal := by
    rw [show W = axisCube (faceTileCorner j0 a b L k) L by
      simpa only [W, k] using faceDoubledSlab_one_eq_axisCube j0 a b L]
    exact volume_axisCube_toReal_pos _ hL
  have hWleH : (volume W).toReal ≤ (2 : ℝ) ^ d * (volume H).toReal := by
    rw [show W = axisCube (faceTileCorner j0 a b L k) L by
      simpa only [W, k] using faceDoubledSlab_one_eq_axisCube j0 a b L]
    dsimp only [H]
    rw [volume_axisCube_toReal _ hL.le,
      volume_axisCube_toReal _ (by positivity : 0 ≤ L / 2)]
    rw [← mul_pow]
    rw [show (2 : ℝ) * (L / 2) = L by ring]
  have hHleS : (volume H).toReal ≤ (volume S).toReal :=
    ENNReal.toReal_mono hStop (measure_mono hHsub)
  refine ⟨hSpos, hWpos, ?_⟩
  rw [div_le_iff₀ hSpos]
  exact hWleH.trans (mul_le_mul_of_nonneg_left hHleS (by positivity))

/-- Radius-uniform lower-face residual-mean row on one adaptive tile.  The
oscillation coefficient is dimension-only; in particular it has no inverse
power of the tile side. -/
theorem sq_averageOn_oneTile_lowerFace_le
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : IntegrableOn f (faceDoubledSlab j0 a b L 1))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (faceDoubledSlab j0 a b L 1))
    (hH1 : ∀ k : FaceIndex d j0 1,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, x j0 < a → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L 1)) :
    averageOn (faceDoubledSlab j0 a b L 1) f ^ 2 ≤
      2 * ((tilePoincareConst d L ^ 2 * d) * (2 : ℝ) ^ d) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) +
        2 * (2 : ℝ) ^ d *
          normalizedL2On (faceDoubledSlab j0 a b L 1)
            (fun x ↦ f x - averageOn (faceDoubledSlab j0 a b L 1) f) ^ 2 := by
  obtain ⟨hSpos, hWpos, hratio⟩ :=
    oneTile_lowerFaceSlab_volumeRatio_le j0 a b hL
  have hraw := sq_averageOn_le_slabPoincare j0 a b hL
    (P := faceDoubledSlab j0 a b L 1) (M := 1)
    Set.inter_subset_left
    (by
      rw [faceDoubledSlab_one_eq_axisCube]
      exact volume_axisCube_ne_top _ L)
    hWpos hSpos hWpos hf hf2 hH1 hfzero hgW
  have hgrad : 0 ≤ volumeAverage (faceDoubledSlab j0 a b L 1)
      (fun x => vecNormSq (G x)) :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ vecNormSq_nonneg _)
  have hosc : 0 ≤ normalizedL2On (faceDoubledSlab j0 a b L 1)
      (fun x ↦ f x - averageOn (faceDoubledSlab j0 a b L 1) f) ^ 2 :=
    sq_nonneg _
  have hfirst :
      2 * ((tilePoincareConst d L ^ 2 * d) *
          ((volume (faceDoubledSlab j0 a b L 1)).toReal /
            (volume (faceInnerSlab j0 a b L 1)).toReal)) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) ≤
        2 * ((tilePoincareConst d L ^ 2 * d) * (2 : ℝ) ^ d) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) := by
    gcongr
  have hsecond :
      2 * ((volume (faceDoubledSlab j0 a b L 1)).toReal /
          (volume (faceInnerSlab j0 a b L 1)).toReal) *
          normalizedL2On (faceDoubledSlab j0 a b L 1)
            (fun x ↦ f x - averageOn (faceDoubledSlab j0 a b L 1) f) ^ 2 ≤
        2 * (2 : ℝ) ^ d *
          normalizedL2On (faceDoubledSlab j0 a b L 1)
            (fun x ↦ f x - averageOn (faceDoubledSlab j0 a b L 1) f) ^ 2 := by
    gcongr
  exact hraw.trans (add_le_add hfirst hsecond)

private theorem lowerHalfTile_subset_upperFaceInnerSlab_one
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} :
    axisCube (faceTileCorner j0 a b L (oneFaceIndex j0)) (L / 2) ⊆
      upperFaceInnerSlab j0 a b L 1 := by
  intro x hx
  refine ⟨?_, faceTile_half_outer j0 a b (oneFaceIndex j0) x hx⟩
  rw [faceDoubledSlab_one_eq_axisCube]
  exact axisCube_half_subset _ _ hx

/-- Upper-face counterpart of `oneTile_lowerFaceSlab_volumeRatio_le`. -/
theorem oneTile_upperFaceSlab_volumeRatio_le
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) :
    0 < (volume (upperFaceInnerSlab j0 a b L 1)).toReal ∧
      0 < (volume (faceDoubledSlab j0 a b L 1)).toReal ∧
      (volume (faceDoubledSlab j0 a b L 1)).toReal /
          (volume (upperFaceInnerSlab j0 a b L 1)).toReal ≤ (2 : ℝ) ^ d := by
  let k : FaceIndex d j0 1 := oneFaceIndex j0
  let H := axisCube (faceTileCorner j0 a b L k) (L / 2)
  let W := faceDoubledSlab j0 a b L 1
  let S := upperFaceInnerSlab j0 a b L 1
  have hHsub : H ⊆ S := by
    simpa only [H, S, k] using
      lowerHalfTile_subset_upperFaceInnerSlab_one
        (j0 := j0) (a := a) (b := b) (L := L)
  have hHpos : 0 < (volume H).toReal := by
    dsimp only [H]
    exact volume_axisCube_toReal_pos _ (by positivity)
  have hWtop : volume W ≠ ⊤ := by
    rw [show W = axisCube (faceTileCorner j0 a b L k) L by
      simpa only [W, k] using faceDoubledSlab_one_eq_axisCube j0 a b L]
    exact volume_axisCube_ne_top _ L
  have hStop : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)
  have hSpos : 0 < (volume S).toReal :=
    lt_of_lt_of_le hHpos (ENNReal.toReal_mono hStop (measure_mono hHsub))
  have hWpos : 0 < (volume W).toReal := by
    rw [show W = axisCube (faceTileCorner j0 a b L k) L by
      simpa only [W, k] using faceDoubledSlab_one_eq_axisCube j0 a b L]
    exact volume_axisCube_toReal_pos _ hL
  have hWleH : (volume W).toReal ≤ (2 : ℝ) ^ d * (volume H).toReal := by
    rw [show W = axisCube (faceTileCorner j0 a b L k) L by
      simpa only [W, k] using faceDoubledSlab_one_eq_axisCube j0 a b L]
    dsimp only [H]
    rw [volume_axisCube_toReal _ hL.le,
      volume_axisCube_toReal _ (by positivity : 0 ≤ L / 2)]
    rw [← mul_pow]
    rw [show (2 : ℝ) * (L / 2) = L by ring]
  have hHleS : (volume H).toReal ≤ (volume S).toReal :=
    ENNReal.toReal_mono hStop (measure_mono hHsub)
  refine ⟨hSpos, hWpos, ?_⟩
  rw [div_le_iff₀ hSpos]
  exact hWleH.trans (mul_le_mul_of_nonneg_left hHleS (by positivity))

/-- Radius-uniform upper-face residual-mean row on one adaptive tile. -/
theorem sq_averageOn_oneTile_upperFace_le
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : IntegrableOn f (faceDoubledSlab j0 a b L 1))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (faceDoubledSlab j0 a b L 1))
    (hH1 : ∀ k : FaceIndex d j0 1,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, a < x j0 → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L 1)) :
    averageOn (faceDoubledSlab j0 a b L 1) f ^ 2 ≤
      2 * ((tilePoincareConst d L ^ 2 * d) * (2 : ℝ) ^ d) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) +
        2 * (2 : ℝ) ^ d *
          normalizedL2On (faceDoubledSlab j0 a b L 1)
            (fun x ↦ f x - averageOn (faceDoubledSlab j0 a b L 1) f) ^ 2 := by
  obtain ⟨hSpos, hWpos, hratio⟩ :=
    oneTile_upperFaceSlab_volumeRatio_le j0 a b hL
  have hraw := sq_averageOn_le_upperSlabPoincare j0 a b hL
    (P := faceDoubledSlab j0 a b L 1) (M := 1)
    Set.inter_subset_left
    (by
      rw [faceDoubledSlab_one_eq_axisCube]
      exact volume_axisCube_ne_top _ L)
    hWpos hSpos hWpos hf hf2 hH1 hfzero hgW
  have hgrad : 0 ≤ volumeAverage (faceDoubledSlab j0 a b L 1)
      (fun x => vecNormSq (G x)) :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ vecNormSq_nonneg _)
  have hosc : 0 ≤ normalizedL2On (faceDoubledSlab j0 a b L 1)
      (fun x ↦ f x - averageOn (faceDoubledSlab j0 a b L 1) f) ^ 2 :=
    sq_nonneg _
  have hfirst :
      2 * ((tilePoincareConst d L ^ 2 * d) *
          ((volume (faceDoubledSlab j0 a b L 1)).toReal /
            (volume (upperFaceInnerSlab j0 a b L 1)).toReal)) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) ≤
        2 * ((tilePoincareConst d L ^ 2 * d) * (2 : ℝ) ^ d) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) := by
    gcongr
  have hsecond :
      2 * ((volume (faceDoubledSlab j0 a b L 1)).toReal /
          (volume (upperFaceInnerSlab j0 a b L 1)).toReal) *
          normalizedL2On (faceDoubledSlab j0 a b L 1)
            (fun x ↦ f x - averageOn (faceDoubledSlab j0 a b L 1) f) ^ 2 ≤
        2 * (2 : ℝ) ^ d *
          normalizedL2On (faceDoubledSlab j0 a b L 1)
            (fun x ↦ f x - averageOn (faceDoubledSlab j0 a b L 1) f) ^ 2 := by
    gcongr
  exact hraw.trans (add_le_add hfirst hsecond)

/-- The same lower-face ratio bound for any axis-cube parent with the same
side as the doubled tile.  This is the physical configuration: the parent is
inside the domain while the doubled tile straddles its boundary face. -/
theorem axisCube_to_oneTile_lowerFaceInner_volumeRatio_le
    (j0 : Fin d) (a : ℝ) (b p : Vec d) {L : ℝ} (hL : 0 < L) :
    (volume (axisCube p L)).toReal /
        (volume (faceInnerSlab j0 a b L 1)).toReal ≤ (2 : ℝ) ^ d := by
  obtain ⟨hSpos, _hWpos, hratio⟩ :=
    oneTile_lowerFaceSlab_volumeRatio_le j0 a b hL
  have hvolume : (volume (axisCube p L)).toReal =
      (volume (faceDoubledSlab j0 a b L 1)).toReal := by
    rw [faceDoubledSlab_one_eq_axisCube,
      volume_axisCube_toReal _ hL.le, volume_axisCube_toReal _ hL.le]
  rw [hvolume]
  exact hratio

/-- The same upper-face ratio bound for any axis-cube parent with the same
side as the doubled tile. -/
theorem axisCube_to_oneTile_upperFaceInner_volumeRatio_le
    (j0 : Fin d) (a : ℝ) (b p : Vec d) {L : ℝ} (hL : 0 < L) :
    (volume (axisCube p L)).toReal /
        (volume (upperFaceInnerSlab j0 a b L 1)).toReal ≤ (2 : ℝ) ^ d := by
  obtain ⟨hSpos, _hWpos, hratio⟩ :=
    oneTile_upperFaceSlab_volumeRatio_le j0 a b hL
  have hvolume : (volume (axisCube p L)).toReal =
      (volume (faceDoubledSlab j0 a b L 1)).toReal := by
    rw [faceDoubledSlab_one_eq_axisCube,
      volume_axisCube_toReal _ hL.le, volume_axisCube_toReal _ hL.le]
  rw [hvolume]
  exact hratio

/-- Lower-face mean row for an interior axis parent of the same side as the
single doubled tile. -/
theorem sq_averageOn_axisCube_oneTile_lowerFace_le
    (j0 : Fin d) (a : ℝ) (b p : Vec d) {L : ℝ} (hL : 0 < L)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hsub : faceInnerSlab j0 a b L 1 ⊆ axisCube p L)
    (hf : IntegrableOn f (axisCube p L))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (axisCube p L))
    (hH1 : ∀ k : FaceIndex d j0 1,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, x j0 < a → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L 1)) :
    averageOn (axisCube p L) f ^ 2 ≤
      2 * ((tilePoincareConst d L ^ 2 * d) * (2 : ℝ) ^ d) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) +
        2 * (2 : ℝ) ^ d * normalizedL2On (axisCube p L)
          (fun x ↦ f x - averageOn (axisCube p L) f) ^ 2 := by
  obtain ⟨hSpos, hWpos, hWratio⟩ :=
    oneTile_lowerFaceSlab_volumeRatio_le j0 a b hL
  have hPratio := axisCube_to_oneTile_lowerFaceInner_volumeRatio_le
    j0 a b p hL
  have hraw := sq_averageOn_le_slabPoincare j0 a b hL
    (P := axisCube p L) (M := 1) hsub (volume_axisCube_ne_top _ L)
    (volume_axisCube_toReal_pos _ hL) hSpos hWpos hf hf2 hH1 hfzero hgW
  have hgrad : 0 ≤ volumeAverage (faceDoubledSlab j0 a b L 1)
      (fun x => vecNormSq (G x)) :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ vecNormSq_nonneg _)
  have hosc : 0 ≤ normalizedL2On (axisCube p L)
      (fun x ↦ f x - averageOn (axisCube p L) f) ^ 2 := sq_nonneg _
  have hfirst :
      2 * ((tilePoincareConst d L ^ 2 * d) *
          ((volume (faceDoubledSlab j0 a b L 1)).toReal /
            (volume (faceInnerSlab j0 a b L 1)).toReal)) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) ≤
        2 * ((tilePoincareConst d L ^ 2 * d) * (2 : ℝ) ^ d) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) := by
    gcongr
  have hsecond :
      2 * ((volume (axisCube p L)).toReal /
          (volume (faceInnerSlab j0 a b L 1)).toReal) *
          normalizedL2On (axisCube p L)
            (fun x ↦ f x - averageOn (axisCube p L) f) ^ 2 ≤
        2 * (2 : ℝ) ^ d * normalizedL2On (axisCube p L)
          (fun x ↦ f x - averageOn (axisCube p L) f) ^ 2 := by
    gcongr
  exact hraw.trans (add_le_add hfirst hsecond)

/-- Upper-face mean row for an interior axis parent of the same side as the
single doubled tile. -/
theorem sq_averageOn_axisCube_oneTile_upperFace_le
    (j0 : Fin d) (a : ℝ) (b p : Vec d) {L : ℝ} (hL : 0 < L)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hsub : upperFaceInnerSlab j0 a b L 1 ⊆ axisCube p L)
    (hf : IntegrableOn f (axisCube p L))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (axisCube p L))
    (hH1 : ∀ k : FaceIndex d j0 1,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, a < x j0 → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L 1)) :
    averageOn (axisCube p L) f ^ 2 ≤
      2 * ((tilePoincareConst d L ^ 2 * d) * (2 : ℝ) ^ d) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) +
        2 * (2 : ℝ) ^ d * normalizedL2On (axisCube p L)
          (fun x ↦ f x - averageOn (axisCube p L) f) ^ 2 := by
  obtain ⟨hSpos, hWpos, hWratio⟩ :=
    oneTile_upperFaceSlab_volumeRatio_le j0 a b hL
  have hPratio := axisCube_to_oneTile_upperFaceInner_volumeRatio_le
    j0 a b p hL
  have hraw := sq_averageOn_le_upperSlabPoincare j0 a b hL
    (P := axisCube p L) (M := 1) hsub (volume_axisCube_ne_top _ L)
    (volume_axisCube_toReal_pos _ hL) hSpos hWpos hf hf2 hH1 hfzero hgW
  have hgrad : 0 ≤ volumeAverage (faceDoubledSlab j0 a b L 1)
      (fun x => vecNormSq (G x)) :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ vecNormSq_nonneg _)
  have hosc : 0 ≤ normalizedL2On (axisCube p L)
      (fun x ↦ f x - averageOn (axisCube p L) f) ^ 2 := sq_nonneg _
  have hfirst :
      2 * ((tilePoincareConst d L ^ 2 * d) *
          ((volume (faceDoubledSlab j0 a b L 1)).toReal /
            (volume (upperFaceInnerSlab j0 a b L 1)).toReal)) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) ≤
        2 * ((tilePoincareConst d L ^ 2 * d) * (2 : ℝ) ^ d) *
          volumeAverage (faceDoubledSlab j0 a b L 1)
            (fun x => vecNormSq (G x)) := by
    gcongr
  have hsecond :
      2 * ((volume (axisCube p L)).toReal /
          (volume (upperFaceInnerSlab j0 a b L 1)).toReal) *
          normalizedL2On (axisCube p L)
            (fun x ↦ f x - averageOn (axisCube p L) f) ^ 2 ≤
        2 * (2 : ℝ) ^ d * normalizedL2On (axisCube p L)
          (fun x ↦ f x - averageOn (axisCube p L) f) ^ 2 := by
    gcongr
  exact hraw.trans (add_le_add hfirst hsecond)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius
