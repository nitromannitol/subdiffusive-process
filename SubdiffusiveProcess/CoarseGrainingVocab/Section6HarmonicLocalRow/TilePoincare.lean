module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.TilingPoincare

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ}

/-- The volume of an axis cube of side `L`. -/
theorem volume_axisCube (z : Vec d) (L : ℝ) :
    volume (axisCube z L) = ENNReal.ofReal L ^ d := by
  rw [axisCube, volume_pi_pi]
  have hcoord : ∀ j : Fin d,
      volume (Set.Ioo (z j) (z j + L)) = ENNReal.ofReal L := by
    intro j
    rw [Real.volume_Ioo]
    ring_nf
  simp [hcoord]

/-- The corner sub-cube of half the side sits inside the tile. -/
theorem axisCube_half_subset (z : Vec d) (L : ℝ) :
    axisCube z (L / 2) ⊆ axisCube z L := by
  intro x hx
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ioo] at hx ⊢
  intro j
  obtain ⟨h1, h2⟩ := hx j
  rcases le_or_gt 0 L with hL | hL
  · exact ⟨h1, lt_of_lt_of_le h2 (by linarith)⟩
  · exact absurd (h1.trans h2) (by simp; linarith)

/-- The tile is `2 ^ d` times its corner sub-cube. -/
theorem volume_axisCube_le_half (z : Vec d) {L : ℝ} (hL : 0 < L) :
    volume (axisCube z L) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d) * volume (axisCube z (L / 2)) := by
  rw [volume_axisCube z L, volume_axisCube z (L / 2)]
  rw [← ENNReal.ofReal_pow hL.le,
    ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ L / 2),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2:ℝ) ^ d)]
  apply le_of_eq
  congr 1
  rw [← mul_pow]
  ring_nf

/-- **Per-tile zero-set Poincare.**  On a tile whose corner sub-cube is a null
set for `u`, the `L²` norm is controlled by the gradient with a constant
proportional to the tile side. -/
theorem tile_zeroSetPoincare (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u : H1Function (axisCube z L))
    (hzero : ∀ y ∈ axisCube z (L / 2), u.toFun y = 0) :
    (eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))).toReal ≤
      (1 + Real.sqrt ((2 : ℝ) ^ d)) * (unitMeanZeroPoincareConst d * L) *
        ∑ i : Fin d,
          (eLpNorm (fun x => u.grad x i) 2
            (volumeMeasureOn (axisCube z L))).toReal := by
  refine eLpNorm_le_of_zeroSet_of_volume_le z hL (by positivity) u
    (axisCube_half_subset z L) ?_ hzero (volume_axisCube_le_half z hL)
  exact (isOpen_axisCube z (L / 2)).measurableSet

/-- The per-tile constant: `(1 + sqrt (2^d)) * (C(d) * L)`, proportional to the
tile side `L`. -/
noncomputable def tilePoincareConst (d : ℕ) (L : ℝ) : ℝ :=
  (1 + Real.sqrt ((2 : ℝ) ^ d)) * (unitMeanZeroPoincareConst d * L)

theorem tilePoincareConst_nonneg (d : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ tilePoincareConst d L := by
  unfold tilePoincareConst
  have h1 : (0:ℝ) ≤ 1 + Real.sqrt ((2 : ℝ) ^ d) := by positivity
  have h2 : (0:ℝ) ≤ unitMeanZeroPoincareConst d * L :=
    mul_nonneg (unitMeanZeroPoincareConst_nonneg d) hL
  exact mul_nonneg h1 h2

/-- **Per-tile zero-set Poincare, integral form.**  This is the shape consumed
by `setIntegral_sq_le_of_tiling`: the constant is `d * (C(d) * L)^2`, i.e.
proportional to `L^2`. -/
theorem tile_zeroSetPoincare_integral (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u : H1Function (axisCube z L))
    (hzero : ∀ y ∈ axisCube z (L / 2), u.toFun y = 0) :
    ∫ x in axisCube z L, u.toFun x ^ 2 ≤
      (tilePoincareConst d L ^ 2 * d) *
        ∫ x in axisCube z L, vecNormSq (u.grad x) := by
  classical
  set N : ℝ := (eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))).toReal with hN
  set G : Fin d → ℝ := fun i =>
    (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal with hG
  have hmain : N ≤ tilePoincareConst d L * ∑ i, G i :=
    tile_zeroSetPoincare z hL u hzero
  have hNnn : 0 ≤ N := ENNReal.toReal_nonneg
  have hGnn : ∀ i, 0 ≤ G i := fun _ => ENNReal.toReal_nonneg
  have hKnn : 0 ≤ tilePoincareConst d L := tilePoincareConst_nonneg d hL.le
  have hSnn : 0 ≤ ∑ i, G i := Finset.sum_nonneg fun i _ => hGnn i
  have hsq : N ^ 2 ≤ tilePoincareConst d L ^ 2 * (∑ i, G i) ^ 2 := by
    nlinarith [hmain, hNnn, hKnn, hSnn]
  have hcs : (∑ i, G i) ^ 2 ≤ (d : ℝ) * ∑ i, G i ^ 2 := sq_sum_le_card_smul G
  have hstep : N ^ 2 ≤ tilePoincareConst d L ^ 2 * ((d : ℝ) * ∑ i, G i ^ 2) :=
    hsq.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
  have hNsq : N ^ 2 = ∫ x in axisCube z L, u.toFun x ^ 2 :=
    Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq u.memL2
  have hGsq : ∀ i, G i ^ 2 = ∫ x in axisCube z L, u.grad x i ^ 2 := fun i =>
    Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (u.gradMemL2 i)
  have hgradInt : ∀ i, IntegrableOn (fun x => u.grad x i ^ 2) (axisCube z L) :=
    fun i => (u.gradMemL2 i).integrable_sq
  have hsum : ∑ i, ∫ x in axisCube z L, u.grad x i ^ 2
      = ∫ x in axisCube z L, vecNormSq (u.grad x) := by
    rw [← integral_finsetSum _ (fun i _ => hgradInt i)]
    refine setIntegral_congr_fun (isOpen_axisCube z L).measurableSet ?_
    intro x _
    simp only [vecNormSq, vecDot]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hNsq] at hstep
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hGsq i), ← hsum]
  ring

/-- **Slab Poincare from a tile family.**  If a function vanishes on the corner
sub-cube of every tile of a disjoint family covering `S`, and is `H¹` on each
tile with gradient `G`, then its `L²` size on `S` is controlled by `G` with a
constant proportional to `L²`.

This is the slab Poincare of `provider-37` §13: taking `L` comparable to the
slab thickness `delta` gives the factor `delta²`, which is the free smallness
the budgeted radius recurrence needs.  The `H¹`-on-each-tile hypothesis is
supplied by `zeroExtendH1`, which produces an `H1Function` on an *arbitrary*
set with `toFun = zeroExtend V _` and `grad = zeroExtendGrad V _`. -/
theorem slabPoincare_of_tileFamily
    {S W : Set (Vec d)} {f : Vec d → ℝ} {G : Vec d → Vec d}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (zt : ι → Vec d) {L : ℝ} (hL : 0 < L)
    (hH1 : ∀ i, ∃ v : H1Function (axisCube (zt i) L), v.toFun = f ∧ v.grad = G)
    (hzero : ∀ i, ∀ y ∈ axisCube (zt i) (L / 2), f y = 0)
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => axisCube (zt i) L)))
    (hcover : volume (S \ ⋃ i, axisCube (zt i) L) = 0)
    (hinside : (⋃ i, axisCube (zt i) L) ⊆ W)
    (hgW : IntegrableOn (fun x => vecNormSq (G x)) W) :
    ∫ x in S, f x ^ 2 ≤
      (tilePoincareConst d L ^ 2 * d) * ∫ x in W, vecNormSq (G x) := by
  classical
  set g : Vec d → ℝ := fun x => Real.sqrt (vecNormSq (G x)) with hgdef
  have hgsq : ∀ x, g x ^ 2 = vecNormSq (G x) := fun x =>
    Real.sq_sqrt (vecNormSq_nonneg (G x))
  have hgfun : (fun x => g x ^ 2) = fun x => vecNormSq (G x) := funext hgsq
  have hfint : ∀ i, IntegrableOn (fun x => f x ^ 2) (axisCube (zt i) L) := by
    intro i
    obtain ⟨v, hv, _⟩ := hH1 i
    have := v.memL2.integrable_sq
    rwa [hv] at this
  have hgint : ∀ i, IntegrableOn (fun x => g x ^ 2) (axisCube (zt i) L) := by
    intro i
    obtain ⟨v, _, hvg⟩ := hH1 i
    rw [hgfun, ← hvg]
    have hcomp : ∀ j, IntegrableOn (fun x => v.grad x j ^ 2) (axisCube (zt i) L) :=
      fun j => (v.gradMemL2 j).integrable_sq
    have : IntegrableOn (fun x => ∑ j, v.grad x j ^ 2) (axisCube (zt i) L) :=
      integrable_finsetSum _ (fun j _ => hcomp j)
    refine this.congr_fun ?_ ((isOpen_axisCube (zt i) L).measurableSet)
    intro x _
    simp only [vecNormSq, vecDot]
    exact (Finset.sum_congr rfl fun j _ => by ring).symm
  have htile : ∀ i, ∫ x in axisCube (zt i) L, f x ^ 2 ≤
      (tilePoincareConst d L ^ 2 * d) * ∫ x in axisCube (zt i) L, g x ^ 2 := by
    intro i
    obtain ⟨v, hv, hvg⟩ := hH1 i
    have hz : ∀ y ∈ axisCube (zt i) (L / 2), v.toFun y = 0 := by
      intro y hy
      rw [hv]
      exact hzero i y hy
    have := tile_zeroSetPoincare_integral (zt i) hL v hz
    rw [hv, hvg] at this
    rwa [hgfun]
  have hgWsq : IntegrableOn (fun x => g x ^ 2) W := by rwa [hgfun]
  have hres := setIntegral_sq_le_of_tiling_ambient
    (fun i => axisCube (zt i) L)
    (fun i => (isOpen_axisCube (zt i) L).measurableSet)
    hdisj hcover hinside hfint hgint hgWsq
    (by positivity : (0:ℝ) ≤ tilePoincareConst d L ^ 2 * d) htile
  rwa [hgfun] at hres

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
