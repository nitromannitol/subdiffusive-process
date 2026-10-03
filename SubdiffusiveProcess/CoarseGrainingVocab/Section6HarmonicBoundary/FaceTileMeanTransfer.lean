module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.MultiTileSlabVolume
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.SlabMeanSplit

@[expose] public section

/-!
# The parent-mean transfer through a covering family of face tiles

`ledger/reports/provider-48-harmonic-boundary.md` §13.6 item 3.

The boundary tile price `exists_boundaryTileResidualMeanCap_half` prices the
*mean* of the residual on one tile straddling `∂𝔠_m` by the `a`-weighted
energy on that tile.  This module transfers such a family of tile-mean caps to
the mean on the projected parent `P`, without ever leaving the `a`-weighted
world (no pointwise `aCutoff / σ` ratio occurs).

The mechanism has two halves.

* **Cancellation-free summation.**  Because the datum vanishes on the outer
  side of the face, the integral over the inner slab equals the integral over
  the whole doubled slab `W = ⋃_k T_k`, hence the sum of the tile integrals —
  the outer halves contribute nothing, and the face itself is a null set.
  Each tile integral is `L^d` times the tile mean, so Cauchy-Schwarz over the
  `N` tiles turns the `N` tile-mean caps into a single cap on the slab mean,
  with the dimension-only loss `4^d` coming from the slab volume lower bounds
  of `MultiTileSlabVolume.lean`.
* **The slab mean split.**  `SlabMeanSplit.abs_averageOn_le_slab_add_oscillation`
  trades `(f)_P` for the slab mean at the price of the parent oscillation
  amplified by `√(|P| / |S|)`; here the mean form is used rather than the `L²`
  form, since the tile caps control means and not local `L²` norms.

Both signs of the face are covered: `faceInnerSlab` when the physical domain
lies above the face, `upperFaceInnerSlab` when it lies below — the latter is
the orientation of a met face `∂𝔠_m` which is the *upper* face of the
projected parent, i.e. the orientation of `CubeHalfVolume.cubeUpperHalf`.

The output carries the free tile parameter exactly as §13.6 predicts: the
energy leg is multiplied by the tile cap `Kt` (which contains the tile scale
factor `L²`, i.e. `3^{-2j}` relative to the parent) while the oscillation leg
is multiplied by `|P| / |S| ≍ 3^{j}`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## A coordinate hyperplane is null -/

/-- A coordinate hyperplane in `Vec d` has Lebesgue measure zero. -/
theorem volume_coordHyperplane_eq_zero (j0 : Fin d) (a : ℝ) :
    volume {x : Vec d | x j0 = a} = 0 := by
  classical
  have hset : {x : Vec d | x j0 = a} =
      Set.pi Set.univ (fun i : Fin d => if i = j0 then ({a} : Set ℝ) else Set.univ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx i
      by_cases h : i = j0
      · subst h; simpa using hx
      · simp [h]
    · intro hx
      simpa using hx j0
  rw [hset, volume_pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
  simp

/-- Almost every point misses a coordinate hyperplane. -/
theorem ae_ne_coordHyperplane (j0 : Fin d) (a : ℝ) :
    ∀ᵐ x : Vec d ∂volume, x j0 ≠ a := by
  rw [MeasureTheory.ae_iff]
  simpa using volume_coordHyperplane_eq_zero j0 a

/-! ## Cancellation-free summation over the tile family -/

/-- The integral over the doubled slab is the sum of the tile integrals. -/
theorem setIntegral_faceDoubledSlab_eq_sum_faceTiles
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {Mt : ℕ}
    {f : Vec d → ℝ} (hfW : IntegrableOn f (faceDoubledSlab j0 a b L Mt)) :
    ∫ x in faceDoubledSlab j0 a b L Mt, f x =
      ∑ k : FaceIndex d j0 Mt,
        ∫ x in axisCube (faceTileCorner j0 a b L k) L, f x := by
  classical
  rw [faceDoubledSlab] at hfW ⊢
  rw [integral_iUnion (fun k => measurableSet_axisCube _ _)
    (faceTiles_disjoint j0 a b hL) hfW, tsum_fintype]

/-- **The inner-slab integral is the sum of the tile integrals** (domain above
the face).  The datum vanishes on the outer side `{x_{j0} < a}`, and the face
itself is null, so the outer halves of the tiles contribute nothing. -/
theorem setIntegral_faceInnerSlab_eq_sum_faceTiles
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {Mt : ℕ}
    {f : Vec d → ℝ}
    (hfzero : ∀ x : Vec d, x j0 < a → f x = 0)
    (hfW : IntegrableOn f (faceDoubledSlab j0 a b L Mt)) :
    ∫ x in faceInnerSlab j0 a b L Mt, f x =
      ∑ k : FaceIndex d j0 Mt,
        ∫ x in axisCube (faceTileCorner j0 a b L k) L, f x := by
  classical
  have hWmeas : MeasurableSet (faceDoubledSlab j0 a b L Mt) :=
    MeasurableSet.iUnion fun k => measurableSet_axisCube _ _
  have hsub : faceInnerSlab j0 a b L Mt ⊆ faceDoubledSlab j0 a b L Mt :=
    Set.inter_subset_left
  have hdiff : ∀ᵐ x : Vec d ∂volume,
      x ∈ faceDoubledSlab j0 a b L Mt \ faceInnerSlab j0 a b L Mt → f x = 0 := by
    filter_upwards [ae_ne_coordHyperplane j0 a] with x hx hmem
    have hnot : ¬ (a < x j0) := fun hlt => hmem.2 ⟨hmem.1, hlt⟩
    exact hfzero x (lt_of_le_of_ne (not_lt.mp hnot) hx)
  have hEq : ∫ x in faceDoubledSlab j0 a b L Mt, f x =
      ∫ x in faceInnerSlab j0 a b L Mt, f x :=
    setIntegral_eq_of_subset_of_ae_diff_eq_zero hWmeas.nullMeasurableSet hsub hdiff
  rw [← hEq]
  exact setIntegral_faceDoubledSlab_eq_sum_faceTiles j0 a b hL hfW

/-- **The inner-slab integral is the sum of the tile integrals** (domain below
the face — the orientation of a met face `∂𝔠_m` which is the upper face of the
projected parent). -/
theorem setIntegral_upperFaceInnerSlab_eq_sum_faceTiles
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {Mt : ℕ}
    {f : Vec d → ℝ}
    (hfzero : ∀ x : Vec d, a < x j0 → f x = 0)
    (hfW : IntegrableOn f (faceDoubledSlab j0 a b L Mt)) :
    ∫ x in upperFaceInnerSlab j0 a b L Mt, f x =
      ∑ k : FaceIndex d j0 Mt,
        ∫ x in axisCube (faceTileCorner j0 a b L k) L, f x := by
  classical
  have hWmeas : MeasurableSet (faceDoubledSlab j0 a b L Mt) :=
    MeasurableSet.iUnion fun k => measurableSet_axisCube _ _
  have hsub : upperFaceInnerSlab j0 a b L Mt ⊆ faceDoubledSlab j0 a b L Mt :=
    Set.inter_subset_left
  have hdiff : ∀ᵐ x : Vec d ∂volume,
      x ∈ faceDoubledSlab j0 a b L Mt \ upperFaceInnerSlab j0 a b L Mt →
        f x = 0 := by
    filter_upwards [ae_ne_coordHyperplane j0 a] with x hx hmem
    have hnot : ¬ (x j0 < a) := fun hlt => hmem.2 ⟨hmem.1, hlt⟩
    exact hfzero x (lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm hx))
  have hEq : ∫ x in faceDoubledSlab j0 a b L Mt, f x =
      ∫ x in upperFaceInnerSlab j0 a b L Mt, f x :=
    setIntegral_eq_of_subset_of_ae_diff_eq_zero hWmeas.nullMeasurableSet hsub hdiff
  rw [← hEq]
  exact setIntegral_faceDoubledSlab_eq_sum_faceTiles j0 a b hL hfW

/-! ## The tile-family mean cap -/

/-- **The slab mean from the tile means.**  If every tile mean is capped by the
tile average of a nonnegative density `e`, with a common constant `Kt`, then
any slab `S` whose integral of `f` is the sum of the tile integrals and whose
volume is at least the total volume of the half tiles obeys the same cap with
the dimension-only loss `4^d`, the density being averaged over the doubled
slab. -/
theorem sq_averageOn_slab_le_of_tileMeanCap
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {Mt : ℕ}
    (hcard : 0 < Fintype.card (FaceIndex d j0 Mt))
    {S : Set (Vec d)} {f e : Vec d → ℝ} {Kt : ℝ} (hKt : 0 ≤ Kt)
    (hSpos : 0 < (volume S).toReal)
    (hSlower : (Fintype.card (FaceIndex d j0 Mt) : ℝ) * (L / 2) ^ d ≤
      (volume S).toReal)
    (hint : ∫ x in S, f x =
      ∑ k : FaceIndex d j0 Mt,
        ∫ x in axisCube (faceTileCorner j0 a b L k) L, f x)
    (heW : IntegrableOn e (faceDoubledSlab j0 a b L Mt))
    (henonneg : ∀ x, 0 ≤ e x)
    (hcap : ∀ k : FaceIndex d j0 Mt,
      averageOn (axisCube (faceTileCorner j0 a b L k) L) f ^ 2 ≤
        Kt * averageOn (axisCube (faceTileCorner j0 a b L k) L) e) :
    averageOn S f ^ 2 ≤
      (4 : ℝ) ^ d * (Kt * averageOn (faceDoubledSlab j0 a b L Mt) e) := by
  classical
  have hWmeas : MeasurableSet (faceDoubledSlab j0 a b L Mt) :=
    MeasurableSet.iUnion fun k => measurableSet_axisCube _ _
  set W := faceDoubledSlab j0 a b L Mt with hW
  set N : ℝ := (Fintype.card (FaceIndex d j0 Mt) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hcard
  have hWreal : (volume W).toReal = N * L ^ d := by
    rw [hW, volume_faceDoubledSlab j0 a b hL Mt, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ← ENNReal.ofReal_pow hL.le,
      ENNReal.toReal_ofReal (by positivity)]
  set c : FaceIndex d j0 Mt → ℝ :=
    fun k => averageOn (axisCube (faceTileCorner j0 a b L k) L) f with hc
  set E : ℝ := averageOn W e with hE
  have hEnonneg : 0 ≤ E := by
    rw [hE, averageOn, volumeAverage]
    exact mul_nonneg (by positivity)
      (setIntegral_nonneg (hW ▸ hWmeas) fun x _ => henonneg x)
  have hsumE : ∑ k : FaceIndex d j0 Mt,
      averageOn (axisCube (faceTileCorner j0 a b L k) L) e = N * E := by
    have hvol : ∀ k : FaceIndex d j0 Mt,
        (volume (axisCube (faceTileCorner j0 a b L k) L)).toReal = L ^ d :=
      fun k => volume_axisCube_toReal _ hL.le
    have hsplit : ∫ x in W, e x =
        ∑ k : FaceIndex d j0 Mt,
          ∫ x in axisCube (faceTileCorner j0 a b L k) L, e x :=
      setIntegral_faceDoubledSlab_eq_sum_faceTiles j0 a b hL heW
    have hLd : (0 : ℝ) < L ^ d := by positivity
    calc ∑ k : FaceIndex d j0 Mt,
          averageOn (axisCube (faceTileCorner j0 a b L k) L) e
        = ∑ k : FaceIndex d j0 Mt,
            (L ^ d)⁻¹ * ∫ x in axisCube (faceTileCorner j0 a b L k) L, e x := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [averageOn, volumeAverage, hvol k]
      _ = (L ^ d)⁻¹ * ∫ x in W, e x := by rw [← Finset.mul_sum, hsplit]
      _ = N * E := by
          rw [hE, averageOn, volumeAverage, hWreal]
          field_simp
  have habs : (∑ k : FaceIndex d j0 Mt, |c k|) ^ 2 ≤ N * (Kt * (N * E)) := by
    have hcs : (∑ k : FaceIndex d j0 Mt, |c k|) ^ 2 ≤
        (Fintype.card (FaceIndex d j0 Mt) : ℝ) *
          ∑ k : FaceIndex d j0 Mt, |c k| ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (FaceIndex d j0 Mt))) (f := fun k => |c k|)
      simpa using this
    have hsq : ∑ k : FaceIndex d j0 Mt, |c k| ^ 2 ≤ Kt * (N * E) := by
      have hle : ∑ k : FaceIndex d j0 Mt, |c k| ^ 2 ≤
          ∑ k : FaceIndex d j0 Mt,
            Kt * averageOn (axisCube (faceTileCorner j0 a b L k) L) e := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [sq_abs]
        exact hcap k
      rw [← Finset.mul_sum, hsumE] at hle
      exact hle
    calc (∑ k : FaceIndex d j0 Mt, |c k|) ^ 2
        ≤ N * ∑ k : FaceIndex d j0 Mt, |c k| ^ 2 := by rw [hN]; exact hcs
      _ ≤ N * (Kt * (N * E)) := mul_le_mul_of_nonneg_left hsq hNpos.le
  have hsumabs : ∑ k : FaceIndex d j0 Mt, |c k| ≤ N * Real.sqrt (Kt * E) := by
    have hrhs : (0 : ℝ) ≤ N * Real.sqrt (Kt * E) := by positivity
    have hsq : (N * Real.sqrt (Kt * E)) ^ 2 = N * (Kt * (N * E)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    nlinarith [habs, hrhs,
      Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => abs_nonneg (c k))]
  have hintc : ∫ x in S, f x = L ^ d * ∑ k : FaceIndex d j0 Mt, c k := by
    rw [hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc]
    simp only
    rw [averageOn, volumeAverage, volume_axisCube_toReal _ hL.le]
    field_simp
  have habsInt : |∫ x in S, f x| ≤ L ^ d * (N * Real.sqrt (Kt * E)) := by
    rw [hintc, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ L ^ d)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (Finset.abs_sum_le_sum_abs _ _).trans hsumabs
  have hmean : |averageOn S f| ≤ (2 : ℝ) ^ d * Real.sqrt (Kt * E) := by
    rw [averageOn, volumeAverage, abs_mul, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ ((volume S).toReal)⁻¹)]
    have hSlow : N * L ^ d / (2 : ℝ) ^ d ≤ (volume S).toReal := by
      have heq : N * (L / 2) ^ d = N * L ^ d / (2 : ℝ) ^ d := by
        rw [div_pow]; ring
      rw [← heq, hN]
      exact hSlower
    have hkey : ((volume S).toReal)⁻¹ * (L ^ d * (N * Real.sqrt (Kt * E))) ≤
        (2 : ℝ) ^ d * Real.sqrt (Kt * E) := by
      rw [inv_mul_le_iff₀ hSpos]
      have hs : (0 : ℝ) ≤ Real.sqrt (Kt * E) := Real.sqrt_nonneg _
      have h2d : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      have h1 : N * L ^ d ≤ (volume S).toReal * (2 : ℝ) ^ d := by
        rw [div_le_iff₀ h2d] at hSlow; linarith
      nlinarith [mul_le_mul_of_nonneg_right h1 hs]
    calc ((volume S).toReal)⁻¹ * |∫ x in S, f x|
        ≤ ((volume S).toReal)⁻¹ * (L ^ d * (N * Real.sqrt (Kt * E))) :=
          mul_le_mul_of_nonneg_left habsInt (by positivity)
      _ ≤ (2 : ℝ) ^ d * Real.sqrt (Kt * E) := hkey
  have hfinal : averageOn S f ^ 2 ≤ ((2 : ℝ) ^ d * Real.sqrt (Kt * E)) ^ 2 := by
    nlinarith [hmean, abs_nonneg (averageOn S f), sq_abs (averageOn S f)]
  refine hfinal.trans (le_of_eq ?_)
  have hpow : ((2 : ℝ) ^ d) ^ 2 = (4 : ℝ) ^ d := by
    rw [← pow_mul, mul_comm d 2, pow_mul]
    norm_num
  rw [mul_pow, Real.sq_sqrt (by positivity), hpow]

/-! ## The parent-mean transfer -/

/-- **§13.6 item 3: the parent-mean transfer, abstract slab form.**

Let `P` be the projected parent and `S` an inner slab adjacent to the face
carrying the tile family.  Given a family of tiles of side `L` covering that
face, each carrying the boundary tile price `(f)_T ^ 2 ≤ Kt · (e)_T` for the
`a`-weighted density `e`, the parent mean obeys

```text
(f)_P ^ 2  ≤  2 · 4^d · Kt · (e)_W  +  2 · (|P| / |S|) · ‖f − (f)_P‖²_{L̄²(P)} .
```

Both legs carry the free tile parameter in the direction §13.6 predicts: `Kt`
contains the tile scale factor `L²`, while `|P| / |S| ≍ 2 |P| / (L · |face|)`
grows only linearly in `L⁻¹`.  No pointwise ellipticity ratio occurs: the
coefficient enters only through `Kt` and the weighted density `e`. -/
theorem sq_averageOn_le_tileFamily_of_tileMeanCap
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {Mt : ℕ}
    (hcard : 0 < Fintype.card (FaceIndex d j0 Mt))
    {P S : Set (Vec d)} {f e : Vec d → ℝ} {Kt : ℝ} (hKt : 0 ≤ Kt)
    (hSmeas : MeasurableSet S) (hsub : S ⊆ P)
    (hPtop : volume P ≠ ⊤) (hPpos : 0 < (volume P).toReal)
    (hSpos : 0 < (volume S).toReal)
    (hSlower : (Fintype.card (FaceIndex d j0 Mt) : ℝ) * (L / 2) ^ d ≤
      (volume S).toReal)
    (hint : ∫ x in S, f x =
      ∑ k : FaceIndex d j0 Mt,
        ∫ x in axisCube (faceTileCorner j0 a b L k) L, f x)
    (hfP : IntegrableOn f P) (hf2P : IntegrableOn (fun x => f x ^ 2) P)
    (heW : IntegrableOn e (faceDoubledSlab j0 a b L Mt))
    (henonneg : ∀ x, 0 ≤ e x)
    (hcap : ∀ k : FaceIndex d j0 Mt,
      averageOn (axisCube (faceTileCorner j0 a b L k) L) f ^ 2 ≤
        Kt * averageOn (axisCube (faceTileCorner j0 a b L k) L) e) :
    averageOn P f ^ 2 ≤
      2 * (4 : ℝ) ^ d * (Kt * averageOn (faceDoubledSlab j0 a b L Mt) e) +
        2 * ((volume P).toReal / (volume S).toReal) *
          normalizedL2On P (fun x => f x - averageOn P f) ^ 2 := by
  classical
  have hslab := sq_averageOn_slab_le_of_tileMeanCap j0 a b hL hcard hKt hSpos
    hSlower hint heW henonneg hcap
  have hcompare := abs_averageOn_subset_sub_averageOn_le
    (Q := P) (P := S) (f := f) hSmeas hsub hPtop hPpos hSpos hfP hf2P
  set A : ℝ := averageOn S f with hA
  set B : ℝ := Real.sqrt ((volume P).toReal / (volume S).toReal) *
      normalizedL2On P (fun x => f x - averageOn P f) with hB
  have htri : |averageOn P f| ≤ |A| + B := by
    have h1 : |averageOn P f| ≤ |A| + |A - averageOn P f| := by
      cases abs_cases (A - averageOn P f) with
      | inl h => cases abs_cases A with
        | inl h2 => cases abs_cases (averageOn P f) with
          | inl h3 => linarith [h.1, h2.1, h3.1]
          | inr h3 => linarith [h.1, h2.1, h3.1]
        | inr h2 => cases abs_cases (averageOn P f) with
          | inl h3 => linarith [h.1, h2.1, h3.1]
          | inr h3 => linarith [h.1, h2.1, h3.1]
      | inr h => cases abs_cases A with
        | inl h2 => cases abs_cases (averageOn P f) with
          | inl h3 => linarith [h.1, h2.1, h3.1]
          | inr h3 => linarith [h.1, h2.1, h3.1]
        | inr h2 => cases abs_cases (averageOn P f) with
          | inl h3 => linarith [h.1, h2.1, h3.1]
          | inr h3 => linarith [h.1, h2.1, h3.1]
    linarith [h1, hcompare]
  have hBnonneg : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : averageOn P f ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    have h0 : |averageOn P f| ^ 2 ≤ (|A| + B) ^ 2 := by
      nlinarith [htri, abs_nonneg (averageOn P f), abs_nonneg A, hBnonneg]
    have h1 : (|A| + B) ^ 2 ≤ 2 * |A| ^ 2 + 2 * B ^ 2 := by
      nlinarith [sq_nonneg (|A| - B)]
    rw [sq_abs] at h0 h1
    linarith [h0, h1]
  have hBsq : B ^ 2 = ((volume P).toReal / (volume S).toReal) *
      normalizedL2On P (fun x => f x - averageOn P f) ^ 2 := by
    rw [hB, mul_pow, Real.sq_sqrt (by positivity)]
  rw [hBsq] at hsq
  nlinarith [hsq, hslab]

/-- **§13.6 item 3, met-face orientation.**  The parent-mean transfer for a
residual vanishing above the face `{x_{j0} = a}`, with the covering slab
`upperFaceInnerSlab`.  This is the orientation in which `∂𝔠_m` is the upper
face of the projected parent (§13.5), so that the zero extension of
`u − h ∈ H¹₀(𝔠_m)` vanishes on the outer half of every tile. -/
theorem sq_averageOn_le_upperFaceTileFamily_of_tileMeanCap
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {Mt : ℕ}
    (hcard : 0 < Fintype.card (FaceIndex d j0 Mt))
    {P : Set (Vec d)} {f e : Vec d → ℝ} {Kt : ℝ} (hKt : 0 ≤ Kt)
    (hsub : upperFaceInnerSlab j0 a b L Mt ⊆ P)
    (hPtop : volume P ≠ ⊤) (hPpos : 0 < (volume P).toReal)
    (hfzero : ∀ x : Vec d, a < x j0 → f x = 0)
    (hfW : IntegrableOn f (faceDoubledSlab j0 a b L Mt))
    (hfP : IntegrableOn f P) (hf2P : IntegrableOn (fun x => f x ^ 2) P)
    (heW : IntegrableOn e (faceDoubledSlab j0 a b L Mt))
    (henonneg : ∀ x, 0 ≤ e x)
    (hcap : ∀ k : FaceIndex d j0 Mt,
      averageOn (axisCube (faceTileCorner j0 a b L k) L) f ^ 2 ≤
        Kt * averageOn (axisCube (faceTileCorner j0 a b L k) L) e) :
    averageOn P f ^ 2 ≤
      2 * (4 : ℝ) ^ d * (Kt * averageOn (faceDoubledSlab j0 a b L Mt) e) +
        2 * ((volume P).toReal /
            (volume (upperFaceInnerSlab j0 a b L Mt)).toReal) *
          normalizedL2On P (fun x => f x - averageOn P f) ^ 2 := by
  classical
  obtain ⟨hSpos, _, _⟩ := upperFaceSlab_volumeRatio_le j0 a b hL hcard
  have hWtop : volume (faceDoubledSlab j0 a b L Mt) ≠ ⊤ := by
    rw [volume_faceDoubledSlab j0 a b hL Mt]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hStop : volume (upperFaceInnerSlab j0 a b L Mt) ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)
  have hSlower : (Fintype.card (FaceIndex d j0 Mt) : ℝ) * (L / 2) ^ d ≤
      (volume (upperFaceInnerSlab j0 a b L Mt)).toReal := by
    have h := ENNReal.toReal_mono hStop
      (volume_upperFaceInnerSlab_lower j0 a b hL Mt)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ L / 2),
      ENNReal.toReal_ofReal (by positivity)] at h
  exact sq_averageOn_le_tileFamily_of_tileMeanCap j0 a b hL hcard hKt
    (measurableSet_upperFaceInnerSlab j0 a b L Mt) hsub hPtop hPpos hSpos
    hSlower
    (setIntegral_upperFaceInnerSlab_eq_sum_faceTiles j0 a b hL hfzero hfW)
    hfP hf2P heW henonneg hcap

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
