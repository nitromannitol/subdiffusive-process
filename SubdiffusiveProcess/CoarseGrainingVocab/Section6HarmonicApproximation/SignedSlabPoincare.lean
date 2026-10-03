module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.ResidualMeanRow

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-- Corner of the upper half-cube of a face tile. -/
def upperHalfTileCorner (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ)
    {M : ℕ} (k : FaceIndex d j0 M) : Vec d :=
  faceTileCorner j0 a b L k + (L / 2) • basisVec j0

@[simp] theorem upperHalfTileCorner_normal (j0 : Fin d) (a : ℝ)
    (b : Vec d) (L : ℝ) {M : ℕ} (k : FaceIndex d j0 M) :
    upperHalfTileCorner j0 a b L k j0 = a := by
  simp [upperHalfTileCorner, basisVec, faceTileCorner_normal]

theorem axisCube_upperHalf_subset_faceTile (j0 : Fin d) (a : ℝ)
    (b : Vec d) {L : ℝ} {M : ℕ}
    (k : FaceIndex d j0 M) :
    axisCube (upperHalfTileCorner j0 a b L k) (L / 2) ⊆
      axisCube (faceTileCorner j0 a b L k) L := by
  intro x hx
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ioo] at hx ⊢
  intro j
  obtain ⟨hx1, hx2⟩ := hx j
  by_cases hj : j = j0
  · subst j
    rw [upperHalfTileCorner_normal] at hx1 hx2
    rw [faceTileCorner_normal]
    constructor <;> linarith
  · have hc : upperHalfTileCorner j0 a b L k j =
        faceTileCorner j0 a b L k j := by
      simp [upperHalfTileCorner, basisVec_apply, hj]
    rw [hc] at hx1 hx2
    exact ⟨hx1, lt_of_lt_of_le hx2 (by linarith)⟩

theorem faceTile_upperHalf_outer (j0 : Fin d) (a : ℝ) (b : Vec d)
    {L : ℝ} {M : ℕ} (k : FaceIndex d j0 M) :
    ∀ y ∈ axisCube (upperHalfTileCorner j0 a b L k) (L / 2), a < y j0 := by
  intro y hy
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ioo] at hy
  simpa [upperHalfTileCorner_normal] using (hy j0).1

/-- The inner half of the same tile family when the physical domain lies on
the lower side of the face. -/
def upperFaceInnerSlab (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ) (M : ℕ) :
    Set (Vec d) :=
  faceDoubledSlab j0 a b L M ∩ {x | x j0 < a}

theorem measurableSet_upperFaceInnerSlab (j0 : Fin d) (a : ℝ)
    (b : Vec d) (L : ℝ) (M : ℕ) :
    MeasurableSet (upperFaceInnerSlab j0 a b L M) := by
  refine (measurableSet_faceDoubledSlab j0 a b L M).inter ?_
  exact measurableSet_lt (measurable_pi_apply j0) measurable_const

private theorem tile_upperZeroSetPoincare_integral
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L)
    {M : ℕ} (k : FaceIndex d j0 M)
    (u : H1Function (axisCube (faceTileCorner j0 a b L k) L))
    (hzero : ∀ y ∈ axisCube (upperHalfTileCorner j0 a b L k) (L / 2),
      u.toFun y = 0) :
    ∫ x in axisCube (faceTileCorner j0 a b L k) L, u.toFun x ^ 2 ≤
      (tilePoincareConst d L ^ 2 * d) *
        ∫ x in axisCube (faceTileCorner j0 a b L k) L, vecNormSq (u.grad x) := by
  classical
  let E := axisCube (upperHalfTileCorner j0 a b L k) (L / 2)
  have hEmeas : MeasurableSet E := (isOpen_axisCube _ _).measurableSet
  have hEsub : E ⊆ axisCube (faceTileCorner j0 a b L k) L :=
    axisCube_upperHalf_subset_faceTile j0 a b k
  have hvol : volume (axisCube (faceTileCorner j0 a b L k) L) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d) * volume E := by
    dsimp [E]
    rw [volume_axisCube, volume_axisCube]
    rw [← ENNReal.ofReal_pow hL.le,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ L / 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d)]
    apply le_of_eq
    congr 1
    rw [← mul_pow]
    ring_nf
  have hnorm := eLpNorm_le_of_zeroSet_of_volume_le
    (faceTileCorner j0 a b L k) hL (by positivity)
    u hEsub hEmeas hzero hvol
  set N : ℝ := (eLpNorm u.toFun 2
    (volumeMeasureOn (axisCube (faceTileCorner j0 a b L k) L))).toReal
  set G : Fin d → ℝ := fun i =>
    (eLpNorm (fun x => u.grad x i) 2
      (volumeMeasureOn (axisCube (faceTileCorner j0 a b L k) L))).toReal
  have hmain : N ≤ tilePoincareConst d L * ∑ i, G i := by
    simpa [N, G, tilePoincareConst] using hnorm
  have hNnn : 0 ≤ N := ENNReal.toReal_nonneg
  have hGnn : ∀ i, 0 ≤ G i := fun _ => ENNReal.toReal_nonneg
  have hKnn : 0 ≤ tilePoincareConst d L := tilePoincareConst_nonneg d hL.le
  have hSnn : 0 ≤ ∑ i, G i := Finset.sum_nonneg fun i _ => hGnn i
  have hsq : N ^ 2 ≤ tilePoincareConst d L ^ 2 * (∑ i, G i) ^ 2 := by
    nlinarith [hmain]
  have hcs := sq_sum_le_card_smul G
  have hstep : N ^ 2 ≤ tilePoincareConst d L ^ 2 *
      ((d : ℝ) * ∑ i, G i ^ 2) :=
    hsq.trans (mul_le_mul_of_nonneg_left hcs (sq_nonneg _))
  have hNsq : N ^ 2 = ∫ x in axisCube (faceTileCorner j0 a b L k) L,
      u.toFun x ^ 2 :=
    Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq u.memL2
  have hGsq : ∀ i, G i ^ 2 =
      ∫ x in axisCube (faceTileCorner j0 a b L k) L, u.grad x i ^ 2 :=
    fun i => Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (u.gradMemL2 i)
  have hsum : ∑ i, ∫ x in axisCube (faceTileCorner j0 a b L k) L,
      u.grad x i ^ 2 =
      ∫ x in axisCube (faceTileCorner j0 a b L k) L, vecNormSq (u.grad x) := by
    rw [← integral_finset_sum _ (fun i _ => (u.gradMemL2 i).integrable_sq)]
    refine setIntegral_congr_fun (isOpen_axisCube _ _).measurableSet ?_
    intro x _
    simp only [vecNormSq, vecDot]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hNsq] at hstep
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hGsq i), ← hsum]
  ring

/-- Upper-face counterpart of P-118's integral slab Poincare. -/
theorem slabPoincare_upperFace
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {M : ℕ}
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hH1 : ∀ k : FaceIndex d j0 M,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, a < x j0 → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L M)) :
    ∫ x in upperFaceInnerSlab j0 a b L M, f x ^ 2 ≤
      (tilePoincareConst d L ^ 2 * d) *
        ∫ x in faceDoubledSlab j0 a b L M, vecNormSq (G x) := by
  classical
  set g : Vec d → ℝ := fun x ↦ Real.sqrt (vecNormSq (G x)) with hgdef
  have hgsq : ∀ x, g x ^ 2 = vecNormSq (G x) := fun x ↦
    Real.sq_sqrt (vecNormSq_nonneg (G x))
  have hgfun : (fun x ↦ g x ^ 2) = fun x ↦ vecNormSq (G x) := funext hgsq
  rw [← hgfun]
  refine setIntegral_sq_le_of_tiling_ambient
    (S := upperFaceInnerSlab j0 a b L M)
    (W := faceDoubledSlab j0 a b L M) (f := f) (g := g)
    (fun k : FaceIndex d j0 M ↦ axisCube (faceTileCorner j0 a b L k) L)
    (fun k ↦ (isOpen_axisCube _ _).measurableSet)
    (faceTiles_disjoint j0 a b hL)
    (ae_cover_of_subset Set.inter_subset_left) (subset_refl _) ?_ ?_ ?_
    (c := tilePoincareConst d L ^ 2 * d) (by positivity) ?_
  · intro k
    obtain ⟨v, hv, _⟩ := hH1 k
    simpa [hv] using! v.memL2.integrable_sq
  · intro k
    obtain ⟨v, _, hvg⟩ := hH1 k
    rw [hgfun, ← hvg]
    have hcomp : ∀ j, IntegrableOn (fun x => v.grad x j ^ 2)
        (axisCube (faceTileCorner j0 a b L k) L) :=
      fun j => (v.gradMemL2 j).integrable_sq
    have hs : IntegrableOn (fun x ↦ ∑ j, v.grad x j ^ 2)
        (axisCube (faceTileCorner j0 a b L k) L) :=
      integrable_finset_sum _ (fun j _ ↦ hcomp j)
    refine hs.congr_fun ?_ (isOpen_axisCube _ _).measurableSet
    intro x _
    simp only [vecNormSq, vecDot]
    exact (Finset.sum_congr rfl fun j _ ↦ by ring).symm
  · rwa [hgfun]
  · intro k
    obtain ⟨v, hv, hvg⟩ := hH1 k
    have hz : ∀ y ∈ axisCube (upperHalfTileCorner j0 a b L k) (L / 2),
        v.toFun y = 0 := by
      intro y hy
      rw [hv]
      exact hfzero y (faceTile_upperHalf_outer j0 a b k y hy)
    have ht := tile_upperZeroSetPoincare_integral j0 a b hL k v hz
    rw [hv, hvg] at ht
    rwa [hgfun]

/-- Upper-face counterpart of P-118's normalized residual-mean endpoint. -/
theorem sq_averageOn_le_upperSlabPoincare
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {M : ℕ}
    {P : Set (Vec d)} {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hsub : upperFaceInnerSlab j0 a b L M ⊆ P)
    (hPtop : volume P ≠ ⊤) (hPpos : 0 < (volume P).toReal)
    (hSpos : 0 < (volume (upperFaceInnerSlab j0 a b L M)).toReal)
    (hWpos : 0 < (volume (faceDoubledSlab j0 a b L M)).toReal)
    (hf : IntegrableOn f P) (hf2 : IntegrableOn (fun x ↦ f x ^ 2) P)
    (hH1 : ∀ k : FaceIndex d j0 M,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, a < x j0 → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L M)) :
    averageOn P f ^ 2 ≤
      2 * ((tilePoincareConst d L ^ 2 * d) *
            ((volume (faceDoubledSlab j0 a b L M)).toReal /
              (volume (upperFaceInnerSlab j0 a b L M)).toReal)) *
          volumeAverage (faceDoubledSlab j0 a b L M)
            (fun x => vecNormSq (G x)) +
        2 * ((volume P).toReal /
              (volume (upperFaceInnerSlab j0 a b L M)).toReal) *
          normalizedL2On P (fun x ↦ f x - averageOn P f) ^ 2 := by
  have hsplit := sq_averageOn_le_slab_add_oscillation
    (P := P) (S := upperFaceInnerSlab j0 a b L M) (f := f)
    (measurableSet_upperFaceInnerSlab j0 a b L M) hsub hPtop hPpos hSpos hf hf2
  have hraw := slabPoincare_upperFace j0 a b hL hH1 hfzero hgW
  have hslab : volumeAverage (upperFaceInnerSlab j0 a b L M)
        (fun x => f x ^ 2) ≤
      ((tilePoincareConst d L ^ 2 * d) *
          ((volume (faceDoubledSlab j0 a b L M)).toReal /
            (volume (upperFaceInnerSlab j0 a b L M)).toReal)) *
        volumeAverage (faceDoubledSlab j0 a b L M)
          (fun x => vecNormSq (G x)) := by
    unfold volumeAverage
    set S := (volume (upperFaceInnerSlab j0 a b L M)).toReal
    set W := (volume (faceDoubledSlab j0 a b L M)).toReal
    have hSne : S ≠ 0 := hSpos.ne'
    have hWne : W ≠ 0 := hWpos.ne'
    have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hSpos.le)
    calc
      S⁻¹ * ∫ x in upperFaceInnerSlab j0 a b L M, f x ^ 2
          ≤ S⁻¹ * ((tilePoincareConst d L ^ 2 * d) *
              ∫ x in faceDoubledSlab j0 a b L M, vecNormSq (G x)) := hscaled
      _ = ((tilePoincareConst d L ^ 2 * d) * (W / S)) *
          (W⁻¹ * ∫ x in faceDoubledSlab j0 a b L M, vecNormSq (G x)) := by
            field_simp
  have hsq : normalizedL2On (upperFaceInnerSlab j0 a b L M) f ^ 2 =
      volumeAverage (upperFaceInnerSlab j0 a b L M) (fun x => f x ^ 2) := by
    unfold normalizedL2On
    exact Real.sq_sqrt (volumeAverage_sq_nonneg _ _)
  rw [hsq] at hsplit
  linarith only [hsplit, hslab]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
