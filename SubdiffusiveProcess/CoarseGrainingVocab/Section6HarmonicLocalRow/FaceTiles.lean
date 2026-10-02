import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.TilePoincare
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

/-!
# The concrete tile family on a boundary face

Tiles for the doubled slab across the face `{x j0 = a}`: one tile per point of
the `(d-1)`-dimensional tangential integer grid, each an `axisCube` of side `L`
whose corner sits at `a - L/2` in the normal direction, so that

* the tile straddles the face, and
* its corner sub-cube of side `L/2` lies strictly on the **outer** side
  `{x j0 < a}`, where the zero extension of `u - h` vanishes.

The interior slab produced has thickness `L/2`, so `delta = L/2`.

Taking the slab to be `(⋃ tiles) ∩ {a < x j0}` rather than an independently
described box makes the covering hypothesis an inclusion by construction, which
is what lets `ae_cover_of_subset` discharge it: recall from
`TilingPoincare.lean` that a strict inclusion into a union of *open* tiles is
otherwise unavailable, since the grid faces between adjacent tiles are omitted.
Those faces are a null set, and they are exactly the difference between this
slab and the full box.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ}

/-- Tangential grid index for the tiles on a face with normal direction `j0`. -/
abbrev FaceIndex (d : ℕ) (j0 : Fin d) (M : ℕ) := {j : Fin d // j ≠ j0} → Fin M

/-- Corner of the tile at tangential grid position `k`. -/
def faceTileCorner (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ) {M : ℕ}
    (k : FaceIndex d j0 M) : Vec d :=
  fun j => if h : j = j0 then a - L / 2 else b j + L * (k ⟨j, h⟩ : ℕ)

@[simp] theorem faceTileCorner_normal (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ)
    {M : ℕ} (k : FaceIndex d j0 M) :
    faceTileCorner j0 a b L k j0 = a - L / 2 := by
  simp [faceTileCorner]

theorem faceTileCorner_tangential (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ)
    {M : ℕ} (k : FaceIndex d j0 M) (j : {j : Fin d // j ≠ j0}) :
    faceTileCorner j0 a b L k j.val = b j.val + L * (k j : ℕ) := by
  simp [faceTileCorner, j.property]

/-- Distinct tangential grid positions give disjoint tiles. -/
theorem faceTiles_disjoint (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L)
    {M : ℕ} :
    Pairwise (Function.onFun Disjoint
      (fun k : FaceIndex d j0 M =>
        axisCube (faceTileCorner j0 a b L k) L)) := by
  intro k k' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ioo] at hx hx'
  obtain ⟨h1, h2⟩ := hx j.val
  obtain ⟨h1', h2'⟩ := hx' j.val
  rw [faceTileCorner_tangential] at h1 h2 h1' h2'
  have hkk : ((k j : ℕ)) ≠ ((k' j : ℕ)) := fun h => hj (Fin.ext h)
  rcases lt_or_gt_of_ne hkk with hlt | hlt
  · have hstep : (((k j : ℕ) : ℝ)) + 1 ≤ (((k' j : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hprod : 0 ≤ L * ((((k' j : ℕ) : ℝ)) - ((((k j : ℕ) : ℝ)) + 1)) :=
      mul_nonneg hL.le (by linarith)
    nlinarith [hprod, h1', h2]
  · have hstep : (((k' j : ℕ) : ℝ)) + 1 ≤ (((k j : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hprod : 0 ≤ L * ((((k j : ℕ) : ℝ)) - ((((k' j : ℕ) : ℝ)) + 1)) :=
      mul_nonneg hL.le (by linarith)
    nlinarith [hprod, h1, h2']

/-- The corner sub-cube of every tile lies strictly outside the face. -/
theorem faceTile_half_outer (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ}
    {M : ℕ} (k : FaceIndex d j0 M) :
    ∀ y ∈ axisCube (faceTileCorner j0 a b L k) (L / 2), y j0 < a := by
  intro y hy
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ioo] at hy
  obtain ⟨_, h2⟩ := hy j0
  rw [faceTileCorner_normal] at h2
  linarith

/-- The tiled doubled slab across the face. -/
def faceDoubledSlab (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ) (M : ℕ) :
    Set (Vec d) :=
  ⋃ k : FaceIndex d j0 M, axisCube (faceTileCorner j0 a b L k) L

/-- The interior slab: the inner side of the tiled doubled slab.  Its normal
thickness is `L / 2`. -/
def faceInnerSlab (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ) (M : ℕ) :
    Set (Vec d) :=
  faceDoubledSlab j0 a b L M ∩ {x | a < x j0}

/-- **Slab Poincare on a boundary face.**  For any `f` vanishing on the outer
side of the face and `H¹` on each tile with gradient `G`, the `L²` size of `f`
on the interior slab is controlled by `G` on the doubled slab, with constant
proportional to `L²` — hence to `delta²`, since `delta = L / 2`. -/
theorem slabPoincare_face
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {M : ℕ}
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hH1 : ∀ k : FaceIndex d j0 M,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, x j0 < a → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L M)) :
    ∫ x in faceInnerSlab j0 a b L M, f x ^ 2 ≤
      (tilePoincareConst d L ^ 2 * d) *
        ∫ x in faceDoubledSlab j0 a b L M, vecNormSq (G x) := by
  refine slabPoincare_of_tileFamily (faceTileCorner j0 a b L) hL hH1 ?_
    (faceTiles_disjoint j0 a b hL)
    (ae_cover_of_subset Set.inter_subset_left) (subset_refl _) hgW
  intro k y hy
  exact hfzero y (faceTile_half_outer j0 a b k y hy)

/-- Normalized (volume-averaged) form of the face slab Poincare. -/
theorem volumeAverage_sq_faceInnerSlab_le
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {M : ℕ}
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hH1 : ∀ k : FaceIndex d j0 M,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, x j0 < a → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L M))
    (hSpos : 0 < (volume (faceInnerSlab j0 a b L M)).toReal)
    (hWpos : 0 < (volume (faceDoubledSlab j0 a b L M)).toReal) :
    volumeAverage (faceInnerSlab j0 a b L M) (fun x => f x ^ 2) ≤
      ((tilePoincareConst d L ^ 2 * d) *
          ((volume (faceDoubledSlab j0 a b L M)).toReal /
            (volume (faceInnerSlab j0 a b L M)).toReal)) *
        volumeAverage (faceDoubledSlab j0 a b L M)
          (fun x => vecNormSq (G x)) := by
  have hmain := slabPoincare_face j0 a b hL hH1 hfzero hgW
  unfold volumeAverage
  set S := (volume (faceInnerSlab j0 a b L M)).toReal with hS
  set W := (volume (faceDoubledSlab j0 a b L M)).toReal with hW
  have hSne : S ≠ 0 := hSpos.ne'
  have hinv : 0 ≤ S⁻¹ := inv_nonneg.mpr hSpos.le
  calc S⁻¹ * ∫ x in faceInnerSlab j0 a b L M, f x ^ 2
      ≤ S⁻¹ * ((tilePoincareConst d L ^ 2 * d) *
          ∫ x in faceDoubledSlab j0 a b L M, vecNormSq (G x)) :=
        mul_le_mul_of_nonneg_left hmain hinv
    _ = ((tilePoincareConst d L ^ 2 * d) * (W / S)) *
          (W⁻¹ * ∫ x in faceDoubledSlab j0 a b L M, vecNormSq (G x)) := by
        have hWne : W ≠ 0 := hWpos.ne'
        field_simp



theorem normalizedL2On_faceInnerSlab_le
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {M : ℕ}
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hH1 : ∀ k : FaceIndex d j0 M,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, x j0 < a → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L M))
    (hSpos : 0 < (volume (faceInnerSlab j0 a b L M)).toReal)
    (hWpos : 0 < (volume (faceDoubledSlab j0 a b L M)).toReal) :
    normalizedL2On (faceInnerSlab j0 a b L M) f ≤
      Real.sqrt ((tilePoincareConst d L ^ 2 * d) *
          ((volume (faceDoubledSlab j0 a b L M)).toReal /
            (volume (faceInnerSlab j0 a b L M)).toReal)) *
        vectorNormalizedL2On (faceDoubledSlab j0 a b L M) G := by
  have havg := volumeAverage_sq_faceInnerSlab_le j0 a b hL hH1 hfzero hgW hSpos hWpos
  have hcnn : 0 ≤ (tilePoincareConst d L ^ 2 * d) *
      ((volume (faceDoubledSlab j0 a b L M)).toReal /
        (volume (faceInnerSlab j0 a b L M)).toReal) := by positivity
  have hgrad : vectorNormalizedL2On (faceDoubledSlab j0 a b L M) G
      = Real.sqrt (volumeAverage (faceDoubledSlab j0 a b L M)
          (fun x => vecNormSq (G x))) := by
    unfold vectorNormalizedL2On normalizedL2On
    congr 1
    refine congrArg _ (funext fun x => ?_)
    exact Real.sq_sqrt (vecNormSq_nonneg (G x))
  unfold normalizedL2On
  rw [hgrad, ← Real.sqrt_mul hcnn]
  exact Real.sqrt_le_sqrt havg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
