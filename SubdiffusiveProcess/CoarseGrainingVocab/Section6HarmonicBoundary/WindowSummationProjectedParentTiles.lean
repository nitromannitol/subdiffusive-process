module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowSummationLowerFace
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowSummationProjectedParents
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryResidualWindowCore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison

@[expose] public section

/-!
# Face tiles attached to a projected boundary parent

This file constructs the signed face-tile family used by the boundary-window
summation.  A depth `j` divides every tangential side of the projected parent
into `3^j` pieces.  The doubled tiles straddle the flush face, while their
inner halves lie in the projected parent.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Tile scale obtained by descending `j` triadic generations from a parent. -/
def windowSummationTileScale (kp : ℤ) (j : ℕ) : ℤ := kp - (j : ℤ)

/-- Number of tiles in each tangential direction at depth `j`. -/
def windowSummationTileCount (j : ℕ) : ℕ := 3 ^ j

/-- Lower corner of a projected parent cube. -/
def windowSummationParentLowerCorner (c : Vec d) (kp : ℤ) : Vec d :=
  fun i ↦ c i - (3 : ℝ) ^ kp / 2

theorem windowSummationTileSide_mul_count (kp : ℤ) (j : ℕ) :
    (3 : ℝ) ^ windowSummationTileScale kp j * windowSummationTileCount j =
      (3 : ℝ) ^ kp := by
  rw [windowSummationTileScale, windowSummationTileCount]
  push_cast
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  field_simp

theorem windowSummationTileSide_pos (kp : ℤ) (j : ℕ) :
    0 < (3 : ℝ) ^ windowSummationTileScale kp j :=
  zpow_pos (by norm_num) _

theorem windowSummationTileCount_pos (j : ℕ) :
    0 < windowSummationTileCount j := by
  simp [windowSummationTileCount]

theorem windowSummation_faceIndex_card_pos [NeZero d]
    (j0 : Fin d) (j : ℕ) :
    0 < Fintype.card (FaceIndex d j0 (windowSummationTileCount j)) := by
  rw [Fintype.card_pos_iff]
  exact ⟨fun _ ↦ ⟨0, windowSummationTileCount_pos j⟩⟩

theorem windowSummation_faceIndex_card (j0 : Fin d) (j : ℕ) :
    Fintype.card (FaceIndex d j0 (windowSummationTileCount j)) =
      windowSummationTileCount j ^ (d - 1) := by
  classical
  change Fintype.card ({i : Fin d // i ≠ j0} → Fin (3 ^ j)) = (3 ^ j) ^ (d - 1)
  erw [Fintype.card_fun]
  simp

/-- The inner slab on the upper face of a parent is contained in the parent. -/
theorem windowSummation_upperFaceInnerSlab_subset_projectedParent
    (c : Vec d) (kp : ℤ) (j : ℕ) (j0 : Fin d) :
    upperFaceInnerSlab j0 (c j0 + (3 : ℝ) ^ kp / 2)
        (windowSummationParentLowerCorner c kp)
        ((3 : ℝ) ^ windowSummationTileScale kp j)
        (windowSummationTileCount j) ⊆
      translatedCube d kp c := by
  intro p hp
  rcases Set.mem_iUnion.mp hp.1 with ⟨idx, hidx⟩
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ioo] at hidx
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    mem_openCubeSet_originCube_iff]
  intro i
  simp only [Pi.sub_apply]
  set ell : ℝ := (3 : ℝ) ^ windowSummationTileScale kp j with hell
  set side : ℝ := (3 : ℝ) ^ kp with hside
  have hellpos : 0 < ell := by rw [hell]; exact windowSummationTileSide_pos kp j
  have hMtpos : 0 < windowSummationTileCount j := windowSummationTileCount_pos j
  have hprod : ell * (windowSummationTileCount j : ℝ) = side := by
    rw [hell, hside]
    exact windowSummationTileSide_mul_count kp j
  have hsidepos : 0 < side := by rw [hside]; exact zpow_pos (by norm_num) _
  by_cases hi : i = j0
  · subst i
    have htile := hidx j0
    rw [faceTileCorner_normal] at htile
    have hinside := hp.2
    constructor
    · have hellside : ell ≤ side := by
        have hMone : (1 : ℝ) ≤ windowSummationTileCount j := by
          exact_mod_cast hMtpos
        nlinarith [mul_le_mul_of_nonneg_left hMone hellpos.le]
      linarith
    · change p j0 < c j0 + (3 : ℝ) ^ kp / 2 at hinside
      rw [← hside] at hinside
      linarith
  · let ii : {i : Fin d // i ≠ j0} := ⟨i, hi⟩
    have htile := hidx i
    rw [faceTileCorner_tangential j0 (c j0 + side / 2)
      (windowSummationParentLowerCorner c kp) ell idx ii] at htile
    have hk : (((idx ii : ℕ) : ℝ)) + 1 ≤ windowSummationTileCount j := by
      exact_mod_cast (idx ii).isLt
    have hk0 : (0 : ℝ) ≤ ((idx ii : ℕ) : ℝ) := by positivity
    simp only [windowSummationParentLowerCorner] at htile
    rw [← hside] at htile
    change c i - side / 2 + ell * (((idx ii : ℕ) : ℝ)) < p i ∧
      p i < c i - side / 2 + ell * (((idx ii : ℕ) : ℝ)) + ell at htile
    constructor
    · have hnonneg : 0 ≤ ell * ((idx ii : ℕ) : ℝ) :=
        mul_nonneg hellpos.le hk0
      linarith [htile.1]
    · have hmul : ell * ((((idx ii : ℕ) : ℝ)) + 1) ≤
          ell * windowSummationTileCount j :=
        mul_le_mul_of_nonneg_left hk hellpos.le
      linarith [htile.2, hprod]

/-- The inner slab on the lower face of a parent is contained in the parent. -/
theorem windowSummation_lowerFaceInnerSlab_subset_projectedParent
    (c : Vec d) (kp : ℤ) (j : ℕ) (j0 : Fin d) :
    faceInnerSlab j0 (c j0 - (3 : ℝ) ^ kp / 2)
        (windowSummationParentLowerCorner c kp)
        ((3 : ℝ) ^ windowSummationTileScale kp j)
        (windowSummationTileCount j) ⊆
      translatedCube d kp c := by
  intro p hp
  rcases Set.mem_iUnion.mp hp.1 with ⟨idx, hidx⟩
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ioo] at hidx
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    mem_openCubeSet_originCube_iff]
  intro i
  simp only [Pi.sub_apply]
  set ell : ℝ := (3 : ℝ) ^ windowSummationTileScale kp j with hell
  set side : ℝ := (3 : ℝ) ^ kp with hside
  have hellpos : 0 < ell := by rw [hell]; exact windowSummationTileSide_pos kp j
  have hMtpos : 0 < windowSummationTileCount j := windowSummationTileCount_pos j
  have hprod : ell * (windowSummationTileCount j : ℝ) = side := by
    rw [hell, hside]
    exact windowSummationTileSide_mul_count kp j
  have hsidepos : 0 < side := by rw [hside]; exact zpow_pos (by norm_num) _
  by_cases hi : i = j0
  · subst i
    have htile := hidx j0
    rw [faceTileCorner_normal] at htile
    have hinside := hp.2
    constructor
    · change c j0 - (3 : ℝ) ^ kp / 2 < p j0 at hinside
      rw [← hside] at hinside
      linarith
    · have hellside : ell ≤ side := by
        have hMone : (1 : ℝ) ≤ windowSummationTileCount j := by
          exact_mod_cast hMtpos
        nlinarith [mul_le_mul_of_nonneg_left hMone hellpos.le]
      linarith
  · let ii : {i : Fin d // i ≠ j0} := ⟨i, hi⟩
    have htile := hidx i
    rw [faceTileCorner_tangential j0 (c j0 - side / 2)
      (windowSummationParentLowerCorner c kp) ell idx ii] at htile
    have hk : (((idx ii : ℕ) : ℝ)) + 1 ≤ windowSummationTileCount j := by
      exact_mod_cast (idx ii).isLt
    have hk0 : (0 : ℝ) ≤ ((idx ii : ℕ) : ℝ) := by positivity
    simp only [windowSummationParentLowerCorner] at htile
    rw [← hside] at htile
    change c i - side / 2 + ell * (((idx ii : ℕ) : ℝ)) < p i ∧
      p i < c i - side / 2 + ell * (((idx ii : ℕ) : ℝ)) + ell at htile
    constructor
    · have hnonneg : 0 ≤ ell * ((idx ii : ℕ) : ℝ) :=
        mul_nonneg hellpos.le hk0
      linarith [htile.1]
    · have hmul : ell * ((((idx ii : ℕ) : ℝ)) + 1) ≤
          ell * windowSummationTileCount j :=
        mul_le_mul_of_nonneg_left hk hellpos.le
      linarith [htile.2, hprod]

/-- The projected parent has `3^j` times the volume of its depth-`j`
doubled face slab. -/
theorem windowSummation_projectedParent_volume_div_faceDoubledSlab
    [NeZero d] (c : Vec d) (kp : ℤ) (j : ℕ) (j0 : Fin d) (a : ℝ) :
    (volume (translatedCube d kp c)).toReal /
        (volume (faceDoubledSlab j0 a
          (windowSummationParentLowerCorner c kp)
          ((3 : ℝ) ^ windowSummationTileScale kp j)
          (windowSummationTileCount j))).toReal =
      windowSummationTileCount j := by
  classical
  set ell : ℝ := (3 : ℝ) ^ windowSummationTileScale kp j with hell
  set Mt : ℕ := windowSummationTileCount j with hMt
  have hellpos : 0 < ell := by rw [hell]; exact windowSummationTileSide_pos kp j
  have hMtpos : 0 < Mt := by rw [hMt]; exact windowSummationTileCount_pos j
  have hprod : ell * (Mt : ℝ) = (3 : ℝ) ^ kp := by
    rw [hell, hMt]
    exact windowSummationTileSide_mul_count kp j
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hcard : Fintype.card (FaceIndex d j0 Mt) = Mt ^ (d - 1) := by
    rw [hMt]
    exact windowSummation_faceIndex_card j0 j
  have hcardR : (Fintype.card (FaceIndex d j0 Mt) : ℝ) =
      (Mt : ℝ) ^ (d - 1) := by exact_mod_cast hcard
  rw [volume_translatedCube_toReal,
    volume_faceDoubledSlab j0 a (windowSummationParentLowerCorner c kp) hellpos Mt,
    ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hellpos.le, hcardR]
  have hpow : ((3 : ℝ) ^ kp) ^ d = (Mt : ℝ) ^ d * ell ^ d := by
    rw [← hprod, mul_pow]
    ring
  have hMpow : (Mt : ℝ) ^ d = (Mt : ℝ) ^ (d - 1) * Mt := by
    conv_lhs => rw [show d = d - 1 + 1 by omega, pow_succ]
  rw [hpow, hMpow]
  field_simp [ne_of_gt hellpos, ne_of_gt (by exact_mod_cast hMtpos : (0 : ℝ) < Mt)]

/-- Volume comparison for the upper-face inner slab. -/
theorem windowSummation_projectedParent_volume_div_upperFaceInnerSlab_le
    [NeZero d] (c : Vec d) (kp : ℤ) (j : ℕ) (j0 : Fin d) :
    (volume (translatedCube d kp c)).toReal /
        (volume (upperFaceInnerSlab j0 (c j0 + (3 : ℝ) ^ kp / 2)
          (windowSummationParentLowerCorner c kp)
          ((3 : ℝ) ^ windowSummationTileScale kp j)
          (windowSummationTileCount j))).toReal ≤
      (2 : ℝ) ^ d * windowSummationTileCount j := by
  set ell : ℝ := (3 : ℝ) ^ windowSummationTileScale kp j with hell
  set a : ℝ := c j0 + (3 : ℝ) ^ kp / 2 with ha
  set W := faceDoubledSlab j0 a (windowSummationParentLowerCorner c kp) ell
    (windowSummationTileCount j) with hW
  set S := upperFaceInnerSlab j0 a (windowSummationParentLowerCorner c kp) ell
    (windowSummationTileCount j) with hS
  have hellpos : 0 < ell := by rw [hell]; exact windowSummationTileSide_pos kp j
  have hcard := windowSummation_faceIndex_card_pos j0 j
  obtain ⟨hSpos, hWpos, hWS⟩ :=
    upperFaceSlab_volumeRatio_le j0 a (windowSummationParentLowerCorner c kp)
      hellpos hcard
  have hPW : (volume (translatedCube d kp c)).toReal /
      (volume W).toReal = windowSummationTileCount j := by
    rw [hW, hell, ha]
    exact windowSummation_projectedParent_volume_div_faceDoubledSlab c kp j j0 _
  have hfactor : (volume (translatedCube d kp c)).toReal / (volume S).toReal =
      ((volume (translatedCube d kp c)).toReal / (volume W).toReal) *
        ((volume W).toReal / (volume S).toReal) := by
    exact (div_mul_div_cancel₀
      (ne_of_gt (by simpa only [W] using hWpos))).symm
  change (volume (translatedCube d kp c)).toReal / (volume S).toReal ≤ _
  rw [hfactor, hPW]
  have hWS' : (volume W).toReal / (volume S).toReal ≤ (2 : ℝ) ^ d := by
    simpa only [W, S] using hWS
  nlinarith [mul_le_mul_of_nonneg_left hWS'
    (show (0 : ℝ) ≤ windowSummationTileCount j by positivity)]

/-- Volume comparison for the lower-face inner slab. -/
theorem windowSummation_projectedParent_volume_div_lowerFaceInnerSlab_le
    [NeZero d] (c : Vec d) (kp : ℤ) (j : ℕ) (j0 : Fin d) :
    (volume (translatedCube d kp c)).toReal /
        (volume (faceInnerSlab j0 (c j0 - (3 : ℝ) ^ kp / 2)
          (windowSummationParentLowerCorner c kp)
          ((3 : ℝ) ^ windowSummationTileScale kp j)
          (windowSummationTileCount j))).toReal ≤
      (2 : ℝ) ^ d * windowSummationTileCount j := by
  set ell : ℝ := (3 : ℝ) ^ windowSummationTileScale kp j with hell
  set a : ℝ := c j0 - (3 : ℝ) ^ kp / 2 with ha
  set W := faceDoubledSlab j0 a (windowSummationParentLowerCorner c kp) ell
    (windowSummationTileCount j) with hW
  set S := faceInnerSlab j0 a (windowSummationParentLowerCorner c kp) ell
    (windowSummationTileCount j) with hS
  have hellpos : 0 < ell := by rw [hell]; exact windowSummationTileSide_pos kp j
  have hcard := windowSummation_faceIndex_card_pos j0 j
  obtain ⟨hSpos, hWpos, hWS⟩ :=
    faceSlab_volumeRatio_le j0 a (windowSummationParentLowerCorner c kp)
      hellpos hcard
  have hPW : (volume (translatedCube d kp c)).toReal /
      (volume W).toReal = windowSummationTileCount j := by
    rw [hW, hell, ha]
    exact windowSummation_projectedParent_volume_div_faceDoubledSlab c kp j j0 _
  have hfactor : (volume (translatedCube d kp c)).toReal / (volume S).toReal =
      ((volume (translatedCube d kp c)).toReal / (volume W).toReal) *
        ((volume W).toReal / (volume S).toReal) := by
    exact (div_mul_div_cancel₀
      (ne_of_gt (by simpa only [W] using hWpos))).symm
  change (volume (translatedCube d kp c)).toReal / (volume S).toReal ≤ _
  rw [hfactor, hPW]
  have hWS' : (volume W).toReal / (volume S).toReal ≤ (2 : ℝ) ^ d := by
    simpa only [W, S] using hWS
  nlinarith [mul_le_mul_of_nonneg_left hWS'
    (show (0 : ℝ) ≤ windowSummationTileCount j by positivity)]

/-- Every tile centre lies within half a parent side of the parent centre. -/
theorem windowSummation_faceTileCenter_sub_parentCenter_abs_le
    (c : Vec d) (kp : ℤ) (j : ℕ) (j0 : Fin d) (a : ℝ)
    (ha : |a - c j0| ≤ (3 : ℝ) ^ kp / 2)
    (idx : FaceIndex d j0 (windowSummationTileCount j)) (i : Fin d) :
    |(axisCubeCenter
        (faceTileCorner j0 a (windowSummationParentLowerCorner c kp)
          ((3 : ℝ) ^ windowSummationTileScale kp j) idx)
        ((3 : ℝ) ^ windowSummationTileScale kp j) - c) i| ≤
      (3 : ℝ) ^ kp / 2 := by
  set ell : ℝ := (3 : ℝ) ^ windowSummationTileScale kp j with hell
  set side : ℝ := (3 : ℝ) ^ kp with hside
  have hellpos : 0 < ell := by rw [hell]; exact windowSummationTileSide_pos kp j
  have hprod : ell * (windowSummationTileCount j : ℝ) = side := by
    rw [hell, hside]
    exact windowSummationTileSide_mul_count kp j
  simp only [Pi.sub_apply, axisCubeCenter_apply]
  by_cases hi : i = j0
  · subst i
    rw [faceTileCorner_normal]
    have heq : a - ell / 2 + ell / 2 - c j0 = a - c j0 := by ring
    rw [heq]
    exact ha
  · let ii : {i : Fin d // i ≠ j0} := ⟨i, hi⟩
    rw [faceTileCorner_tangential j0 a
      (windowSummationParentLowerCorner c kp) ell idx ii]
    simp only [windowSummationParentLowerCorner]
    rw [← hside]
    have hk0 : (0 : ℝ) ≤ ((idx ii : ℕ) : ℝ) := by positivity
    have hk : (((idx ii : ℕ) : ℝ)) + 1 ≤ windowSummationTileCount j := by
      exact_mod_cast (idx ii).isLt
    have hlo : -side / 2 ≤
        -side / 2 + ell * ((idx ii : ℕ) + 1 / 2 : ℝ) := by
      have : 0 ≤ ell * ((idx ii : ℕ) + 1 / 2 : ℝ) := by positivity
      linarith
    have hhi : -side / 2 + ell * ((idx ii : ℕ) + 1 / 2 : ℝ) ≤
        side / 2 := by
      have hmul : ell * ((((idx ii : ℕ) : ℝ)) + 1) ≤
          ell * windowSummationTileCount j :=
        mul_le_mul_of_nonneg_left hk hellpos.le
      linarith [hprod]
    rw [abs_le]
    constructor <;> linarith

/-- A closed tile whose centre is within one scale-`n` side of `z` fits in
the scale-`n+2` anchor. -/
theorem windowSummation_translateSet_cubeSet_subset_anchor
    {n kappa : ℤ} {y z : Vec d} (hkappa : kappa ≤ n - 2)
    (hyz : ∀ i, |(y - z) i| ≤ (3 : ℝ) ^ n) :
    translateSet (y - z) (cubeSet (originCube d kappa)) ⊆
      cubeSet (originCube d (n + 2)) := by
  intro w hw
  have hw0 : w - (y - z) ∈ cubeSet (originCube d kappa) :=
    mem_translateSet_iff_sub_mem.mp hw
  rw [mem_cubeSet_originCube_iff] at hw0 ⊢
  intro i
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have hn : (3 : ℝ) ^ n = 9 * (3 : ℝ) ^ (n - 2) := by
    rw [show n = n - 2 + 2 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hanchor : (3 : ℝ) ^ (n + 2) = 81 * (3 : ℝ) ^ (n - 2) := by
    rw [show n + 2 = n - 2 + 4 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hpow : (3 : ℝ) ^ kappa ≤ (3 : ℝ) ^ (n - 2) :=
    zpow_le_zpow_right₀ (by norm_num) hkappa
  have hyzi := abs_le.mp (hyz i)
  have hid : w i = (w - (y - z)) i + (y - z) i := by
    simp only [Pi.sub_apply]
    ring
  rw [hn] at hyzi
  rw [hid, hanchor]
  constructor <;>
    linarith only [(hw0 i).1, (hw0 i).2, hyzi.1, hyzi.2, hpow, hbase]

/-- All depth-`j` face tiles of a projected parent lie in the common
good-event anchor used by the window step. -/
theorem windowSummation_projectedParent_tileAnchorContainment
    {m kp : ℤ} {n : ℕ} {q x z : Vec d} {rho : ℝ}
    (hkp_m : kp ≤ m) (hkp_n : kp ≤ (n : ℤ) - 2)
    (hx : x ∈ truncatedCube d m ((n : ℤ) - 3) z)
    (hq : q ∈ boundaryWindow d m x rho)
    (hrho : rho ≤ 4 * (3 : ℝ) ^ n / 9)
    (j : ℕ) (j0 : Fin d) (a : ℝ)
    (ha : |a - Section6ExcessDecay.wellPlacedCentre q m kp j0| ≤
      (3 : ℝ) ^ kp / 2) :
    ∀ idx : FaceIndex d j0 (windowSummationTileCount j),
      translateSet
          (axisCubeCenter
              (faceTileCorner j0 a
                (windowSummationParentLowerCorner
                  (Section6ExcessDecay.wellPlacedCentre q m kp) kp)
                ((3 : ℝ) ^ windowSummationTileScale kp j) idx)
              ((3 : ℝ) ^ windowSummationTileScale kp j) - z)
          (cubeSet (originCube d (windowSummationTileScale kp j))) ⊆
        cubeSet (originCube d ((n : ℤ) + 2)) := by
  intro idx
  apply windowSummation_translateSet_cubeSet_subset_anchor
      (n := (n : ℤ)) (kappa := windowSummationTileScale kp j)
  · unfold windowSummationTileScale
    omega
  · intro i
    set c : Vec d := Section6ExcessDecay.wellPlacedCentre q m kp with hc
    set y : Vec d := axisCubeCenter
      (faceTileCorner j0 a (windowSummationParentLowerCorner c kp)
        ((3 : ℝ) ^ windowSummationTileScale kp j) idx)
      ((3 : ℝ) ^ windowSummationTileScale kp j) with hy
    have hyc : |(y - c) i| ≤ (3 : ℝ) ^ kp / 2 := by
      rw [hy]
      exact windowSummation_faceTileCenter_sub_parentCenter_abs_le
        c kp j j0 a (by simpa only [hc] using ha) idx i
    have hcq : |(c - q) i| < (3 : ℝ) ^ kp / 2 := by
      have h := MeanControlGeometry.abs_wellPlacedCentre_sub_lt hkp_m hq.2 i
      simp only [c, Pi.sub_apply]
      convert h using 1
      all_goals ring
    have hqx : |(q - x) i| ≤ rho := by
      simpa only [Pi.sub_apply] using hq.1 i
    have hxzCube : x - z ∈ cube d ((n : ℤ) - 3) :=
      Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hx
    rw [cube, mem_openCubeSet_originCube_iff] at hxzCube
    have hxz : |(x - z) i| < (3 : ℝ) ^ ((n : ℤ) - 3) / 2 := by
      rw [abs_lt]
      have hi := hxzCube i
      constructor <;> linarith [hi.1, hi.2]
    have hkpPow : (3 : ℝ) ^ kp ≤ (3 : ℝ) ^ ((n : ℤ) - 2) :=
      zpow_le_zpow_right₀ (by norm_num) hkp_n
    have hn3 : (3 : ℝ) ^ ((n : ℤ) - 3) = (3 : ℝ) ^ n / 27 := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
      norm_num
    have hn2 : (3 : ℝ) ^ ((n : ℤ) - 2) = (3 : ℝ) ^ n / 9 := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
      norm_num
    have hNpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    have htri : |(y - z) i| ≤
        |(y - c) i| + |(c - q) i| + |(q - x) i| + |(x - z) i| := by
      have hid : (y - z) i =
          (y - c) i + (c - q) i + (q - x) i + (x - z) i := by
        simp only [Pi.sub_apply]
        ring
      rw [hid]
      calc
        |(y - c) i + (c - q) i + (q - x) i + (x - z) i| ≤
            |(y - c) i + (c - q) i + (q - x) i| + |(x - z) i| :=
          abs_add_le _ _
        _ ≤ (|(y - c) i + (c - q) i| + |(q - x) i|) + |(x - z) i| :=
          by linarith [abs_add_le ((y - c) i + (c - q) i) ((q - x) i)]
        _ ≤ |(y - c) i| + |(c - q) i| + |(q - x) i| + |(x - z) i| := by
          linarith [abs_add_le ((y - c) i) ((c - q) i)]
    rw [hn2] at hkpPow
    rw [hn3] at hxz
    calc
      |(y - z) i| ≤
          |(y - c) i| + |(c - q) i| + |(q - x) i| + |(x - z) i| := htri
      _ ≤ (3 : ℝ) ^ n := by
        linarith [hyc, hcq, hqx, hxz, hkpPow, hrho]

/-- **Signed projected-parent tile constructor.**  The flush-face dichotomy,
together with a chosen depth `j`, supplies all geometric arguments of the
appropriate physical tile-family theorem. -/
theorem exists_windowSummation_projectedBoundaryParentTileFamily
    [NeZero d] {m kp : ℤ} {n : ℕ} {q x z : Vec d} {rho : ℝ}
    (hkp_m : kp ≤ m) (hkp_n : kp ≤ (n : ℤ) - 2)
    (hx : x ∈ truncatedCube d m ((n : ℤ) - 3) z)
    (hq : q ∈ boundaryWindow d m x rho)
    (hrho : rho ≤ 4 * (3 : ℝ) ^ n / 9)
    (hnot : ¬ translatedCube d (kp - 1) q ⊆ cube d m) (j : ℕ) :
    ∃ (j0 : Fin d) (sigma : ℝ), (sigma = 1 ∨ sigma = -1) ∧
      (∀ idx : FaceIndex d j0 (windowSummationTileCount j),
        translateSet
            (axisCubeCenter
                (faceTileCorner j0
                  (if sigma = 1 then
                    Section6ExcessDecay.wellPlacedCentre q m kp j0 + (3 : ℝ) ^ kp / 2
                  else
                    Section6ExcessDecay.wellPlacedCentre q m kp j0 - (3 : ℝ) ^ kp / 2)
                  (windowSummationParentLowerCorner
                    (Section6ExcessDecay.wellPlacedCentre q m kp) kp)
                  ((3 : ℝ) ^ windowSummationTileScale kp j) idx)
                ((3 : ℝ) ^ windowSummationTileScale kp j) - z)
            (cubeSet (originCube d (windowSummationTileScale kp j))) ⊆
          cubeSet (originCube d ((n : ℤ) + 2))) ∧
      ((sigma = 1 ∧
          Section6ExcessDecay.wellPlacedCentre q m kp j0 + (3 : ℝ) ^ kp / 2 =
            (3 : ℝ) ^ m / 2 ∧
          (∀ p : Vec d,
            Section6ExcessDecay.wellPlacedCentre q m kp j0 + (3 : ℝ) ^ kp / 2 <
              p j0 → p ∉ cube d m) ∧
          upperFaceInnerSlab j0
              (Section6ExcessDecay.wellPlacedCentre q m kp j0 + (3 : ℝ) ^ kp / 2)
              (windowSummationParentLowerCorner
                (Section6ExcessDecay.wellPlacedCentre q m kp) kp)
              ((3 : ℝ) ^ windowSummationTileScale kp j)
              (windowSummationTileCount j) ⊆
            translatedCube d kp (Section6ExcessDecay.wellPlacedCentre q m kp) ∧
          (volume (translatedCube d kp
              (Section6ExcessDecay.wellPlacedCentre q m kp))).toReal /
              (volume (upperFaceInnerSlab j0
                (Section6ExcessDecay.wellPlacedCentre q m kp j0 + (3 : ℝ) ^ kp / 2)
                (windowSummationParentLowerCorner
                  (Section6ExcessDecay.wellPlacedCentre q m kp) kp)
                ((3 : ℝ) ^ windowSummationTileScale kp j)
                (windowSummationTileCount j))).toReal ≤
            (2 : ℝ) ^ d * windowSummationTileCount j) ∨
        (sigma = -1 ∧
          Section6ExcessDecay.wellPlacedCentre q m kp j0 - (3 : ℝ) ^ kp / 2 =
            -(3 : ℝ) ^ m / 2 ∧
          (∀ p : Vec d,
            p j0 < Section6ExcessDecay.wellPlacedCentre q m kp j0 -
              (3 : ℝ) ^ kp / 2 → p ∉ cube d m) ∧
          faceInnerSlab j0
              (Section6ExcessDecay.wellPlacedCentre q m kp j0 - (3 : ℝ) ^ kp / 2)
              (windowSummationParentLowerCorner
                (Section6ExcessDecay.wellPlacedCentre q m kp) kp)
              ((3 : ℝ) ^ windowSummationTileScale kp j)
              (windowSummationTileCount j) ⊆
            translatedCube d kp (Section6ExcessDecay.wellPlacedCentre q m kp) ∧
          (volume (translatedCube d kp
              (Section6ExcessDecay.wellPlacedCentre q m kp))).toReal /
              (volume (faceInnerSlab j0
                (Section6ExcessDecay.wellPlacedCentre q m kp j0 - (3 : ℝ) ^ kp / 2)
                (windowSummationParentLowerCorner
                  (Section6ExcessDecay.wellPlacedCentre q m kp) kp)
                ((3 : ℝ) ^ windowSummationTileScale kp j)
                (windowSummationTileCount j))).toReal ≤
            (2 : ℝ) ^ d * windowSummationTileCount j)) := by
  obtain ⟨j0, sigma, hsigma, hflush⟩ :=
    Section6HarmonicApproximation.exists_projectedBoundaryCell_flushFace
      hkp_m hnot
  refine ⟨j0, sigma, hsigma, ?_, ?_⟩
  · rcases hsigma with hsig | hsig
    · subst sigma
      apply windowSummation_projectedParent_tileAnchorContainment
        hkp_m hkp_n hx hq hrho j j0
      simp only [ite_true]
      rw [abs_le]
      have hp : 0 < (3 : ℝ) ^ kp := zpow_pos (by norm_num) _
      constructor <;> linarith
    · subst sigma
      simp only [ite_eq_right (by norm_num : (-1 : ℝ) ≠ 1)]
      apply windowSummation_projectedParent_tileAnchorContainment
        hkp_m hkp_n hx hq hrho j j0
      rw [abs_le]
      have hp : 0 < (3 : ℝ) ^ kp := zpow_pos (by norm_num) _
      constructor <;> linarith
  · rcases hsigma with hsig | hsig
    · subst sigma
      left
      refine ⟨rfl, ?_, ?_,
        windowSummation_upperFaceInnerSlab_subset_projectedParent _ _ _ _,
        windowSummation_projectedParent_volume_div_upperFaceInnerSlab_le _ _ _ _⟩
      · convert hflush using 1 <;> ring
      · intro p hpout hpCube
        rw [cube, mem_openCubeSet_originCube_iff] at hpCube
        have hi := hpCube j0
        rw [show Section6ExcessDecay.wellPlacedCentre q m kp j0 +
            (3 : ℝ) ^ kp / 2 = (3 : ℝ) ^ m / 2 by
          convert hflush using 1 <;> ring] at hpout
        linarith [hi.2]
    · subst sigma
      right
      refine ⟨rfl, ?_, ?_,
        windowSummation_lowerFaceInnerSlab_subset_projectedParent _ _ _ _,
        windowSummation_projectedParent_volume_div_lowerFaceInnerSlab_le _ _ _ _⟩
      · simp only [neg_mul] at hflush
        linarith
      · intro p hpout hpCube
        rw [cube, mem_openCubeSet_originCube_iff] at hpCube
        have hi := hpCube j0
        have hface : Section6ExcessDecay.wellPlacedCentre q m kp j0 -
            (3 : ℝ) ^ kp / 2 = -(3 : ℝ) ^ m / 2 := by
          simp only [neg_mul] at hflush
          linarith
        rw [hface] at hpout
        linarith [hi.1]

/-- Zero-extension energy on a doubled depth-`j` face slab is at most
`3^j` times its parent average, provided the part of the slab in the domain
lies in the parent. -/
theorem windowSummation_faceDoubledSlab_zeroExtendEnergy_le_parent
    [NeZero d] (c : Vec d) (kp : ℤ) (j : ℕ) (j0 : Fin d) (a : ℝ)
    {V : Set (Vec d)} (hV : MeasurableSet V) {A : Vec d → ℝ}
    {G : Vec d → Vec d}
    (hA0 : ∀ p, 0 ≤ A p)
    (hinside : faceDoubledSlab j0 a (windowSummationParentLowerCorner c kp)
        ((3 : ℝ) ^ windowSummationTileScale kp j) (windowSummationTileCount j) ∩ V ⊆
      translatedCube d kp c)
    (hint : IntegrableOn (fun p ↦ A p * vecNormSq (G p))
      (translatedCube d kp c)) :
    let W := faceDoubledSlab j0 a (windowSummationParentLowerCorner c kp)
      ((3 : ℝ) ^ windowSummationTileScale kp j) (windowSummationTileCount j)
    let energy0 := fun p ↦ A p * vecNormSq (zeroExtendGrad V G p)
    IntegrableOn energy0 W ∧
      averageOn W energy0 ≤ windowSummationTileCount j *
        averageOn (translatedCube d kp c) (fun p ↦ A p * vecNormSq (G p)) := by
  dsimp only
  set W := faceDoubledSlab j0 a (windowSummationParentLowerCorner c kp)
    ((3 : ℝ) ^ windowSummationTileScale kp j) (windowSummationTileCount j) with hW
  set e : Vec d → ℝ := fun p ↦ A p * vecNormSq (G p) with he
  set e0 : Vec d → ℝ := fun p ↦ A p * vecNormSq (zeroExtendGrad V G p) with he0
  have hWmeas : MeasurableSet W := by
    rw [hW]
    exact MeasurableSet.iUnion fun idx ↦ measurableSet_axisCube _ _
  have hWVmeas : MeasurableSet (W ∩ V) := hWmeas.inter hV
  have hintWV : IntegrableOn e (W ∩ V) := by
    exact hint.mono_set hinside
  have hindicator : W.indicator e0 = (W ∩ V).indicator e := by
    funext p
    by_cases hpW : p ∈ W
    · rw [Set.indicator_of_mem hpW]
      by_cases hpV : p ∈ V
      · have hpWV : p ∈ W ∩ V := ⟨hpW, hpV⟩
        rw [Set.indicator_of_mem hpWV]
        simp only [e0, e, zeroExtendGrad_of_mem G hpV]
      · rw [Set.indicator_of_notMem (fun hp ↦ hpV hp.2)]
        simp only [e0, zeroExtendGrad_of_notMem G hpV]
        simp [vecNormSq, vecDot]
    · rw [Set.indicator_of_notMem hpW,
        Set.indicator_of_notMem (fun hp ↦ hpW hp.1)]
  have he0int : IntegrableOn e0 W := by
    apply (integrable_indicator_iff hWmeas).1
    rw [hindicator]
    exact hintWV.integrable_indicator hWVmeas
  refine ⟨by simpa only [W, e0], ?_⟩
  have hintle : ∫ p in W, e0 p ≤ ∫ p in translatedCube d kp c, e p := by
    have heq : ∫ p in W, e0 p = ∫ p in W ∩ V, e p := by
      rw [← integral_indicator hWmeas, hindicator, integral_indicator hWVmeas]
    rw [heq]
    exact setIntegral_mono_set (by simpa only [e] using hint)
      (Filter.Eventually.of_forall fun p ↦
        mul_nonneg (hA0 p) (vecNormSq_nonneg _))
      (LE.le.eventuallySubset (by simpa only [W] using hinside))
  have hWpos : 0 < (volume W).toReal := by
    rw [hW]
    exact (faceSlab_volumeRatio_le j0 a (windowSummationParentLowerCorner c kp)
      (windowSummationTileSide_pos kp j)
      (windowSummation_faceIndex_card_pos j0 j)).2.1
  have hPpos : 0 < (volume (translatedCube d kp c)).toReal :=
    volume_translatedCube_toReal_pos kp c
  have hratio : (volume (translatedCube d kp c)).toReal / (volume W).toReal =
      windowSummationTileCount j := by
    rw [hW]
    exact windowSummation_projectedParent_volume_div_faceDoubledSlab c kp j j0 a
  have hinv : ((volume W).toReal)⁻¹ = windowSummationTileCount j *
      ((volume (translatedCube d kp c)).toReal)⁻¹ := by
    field_simp [hWpos.ne', hPpos.ne'] at hratio ⊢
    nlinarith [hratio]
  unfold averageOn volumeAverage
  have hInvNonneg : 0 ≤ ((volume W).toReal)⁻¹ := by positivity
  calc
    ((volume W).toReal)⁻¹ * ∫ p in W, e0 p ≤
        ((volume W).toReal)⁻¹ * ∫ p in translatedCube d kp c, e p :=
      mul_le_mul_of_nonneg_left hintle hInvNonneg
    _ = windowSummationTileCount j *
        ((volume (translatedCube d kp c)).toReal)⁻¹ *
          ∫ p in translatedCube d kp c, e p := by rw [hinv]
    _ = windowSummationTileCount j *
        (((volume (translatedCube d kp c)).toReal)⁻¹ *
          ∫ p in translatedCube d kp c, e p) := by ring

theorem windowSummation_upperFaceDoubledSlab_inter_cube_subset_parent
    (c : Vec d) (m kp : ℤ) (j : ℕ) (j0 : Fin d)
    (hface : c j0 + (3 : ℝ) ^ kp / 2 = (3 : ℝ) ^ m / 2) :
    faceDoubledSlab j0 (c j0 + (3 : ℝ) ^ kp / 2)
        (windowSummationParentLowerCorner c kp)
        ((3 : ℝ) ^ windowSummationTileScale kp j)
        (windowSummationTileCount j) ∩ cube d m ⊆
      translatedCube d kp c := by
  intro p hp
  apply windowSummation_upperFaceInnerSlab_subset_projectedParent c kp j j0
  refine ⟨hp.1, ?_⟩
  have hpcube := hp.2
  rw [cube, mem_openCubeSet_originCube_iff] at hpcube
  have hi := hpcube j0
  change p j0 < c j0 + (3 : ℝ) ^ kp / 2
  rw [hface]
  linarith [hi.2]

theorem windowSummation_lowerFaceDoubledSlab_inter_cube_subset_parent
    (c : Vec d) (m kp : ℤ) (j : ℕ) (j0 : Fin d)
    (hface : c j0 - (3 : ℝ) ^ kp / 2 = -(3 : ℝ) ^ m / 2) :
    faceDoubledSlab j0 (c j0 - (3 : ℝ) ^ kp / 2)
        (windowSummationParentLowerCorner c kp)
        ((3 : ℝ) ^ windowSummationTileScale kp j)
        (windowSummationTileCount j) ∩ cube d m ⊆
      translatedCube d kp c := by
  intro p hp
  apply windowSummation_lowerFaceInnerSlab_subset_projectedParent c kp j j0
  refine ⟨hp.1, ?_⟩
  have hpcube := hp.2
  rw [cube, mem_openCubeSet_originCube_iff] at hpcube
  have hi := hpcube j0
  change c j0 - (3 : ℝ) ^ kp / 2 < p j0
  rw [hface]
  linarith [hi.1]

/-- The scalar zero extension of a cube `H¹₀` datum and its square are
integrable on every measurable subset of the ambient space. -/
theorem windowSummation_zeroExtend_integrableOn
    (m : ℤ) (rho : H10Function (openCubeSet (originCube d m)))
    {W : Set (Vec d)} (_hW : MeasurableSet W) :
    IntegrableOn (zeroExtend (openCubeSet (originCube d m))
      rho.toH1Function.toFun) W ∧
    IntegrableOn (fun p ↦ zeroExtend (openCubeSet (originCube d m))
      rho.toH1Function.toFun p ^ 2) W := by
  let V := openCubeSet (originCube d m)
  have hV : MeasurableSet V := measurableSet_openCubeSet _
  let : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top _
  have hfV : IntegrableOn rho.toH1Function.toFun V :=
    rho.toH1Function.memL2.integrable (by norm_num)
  have hf2V : IntegrableOn (fun p ↦ rho.toH1Function.toFun p ^ 2) V := by
    simpa only [IntegrableOn] using rho.toH1Function.memL2.integrable_sq
  have hfun : zeroExtend V rho.toH1Function.toFun =
      V.indicator rho.toH1Function.toFun := by
    funext p
    by_cases hp : p ∈ V
    · rw [zeroExtend_of_mem _ hp, Set.indicator_of_mem hp]
    · rw [zeroExtend_of_notMem _ hp, Set.indicator_of_notMem hp]
  have hfun2 : (fun p ↦ zeroExtend V rho.toH1Function.toFun p ^ 2) =
      V.indicator (fun p ↦ rho.toH1Function.toFun p ^ 2) := by
    funext p
    by_cases hp : p ∈ V
    · rw [zeroExtend_of_mem _ hp, Set.indicator_of_mem hp]
    · rw [zeroExtend_of_notMem _ hp, Set.indicator_of_notMem hp]
      norm_num
  constructor
  · have hglobal : Integrable (zeroExtend V rho.toH1Function.toFun) := by
      rw [hfun]
      exact hfV.integrable_indicator hV
    simpa only [V] using hglobal.integrableOn
  · have hglobal : Integrable
        (fun p ↦ zeroExtend V rho.toH1Function.toFun p ^ 2) := by
      rw [hfun2]
      exact hf2V.integrable_indicator hV
    simpa only [V] using hglobal.integrableOn

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
