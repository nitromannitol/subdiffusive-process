module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.QuasiMonotone
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.ScaledInterface
public import SubdiffusiveProcess.Frozen.Section6.Defs.TruncatedCube










@[expose] public section

/-!
# The one-step window family `U_{m,j}(x) = (x + □_j) ∩ □_m`

The section 6 excess-decay lemma runs on the frozen family
`truncatedCube d m j x`, which unfolds to the intersection of a translate of the
centred cube `□_j` with the domain cube `□_m`.  This module proves the geometry
every later leg of the one-step contraction reads off:

* nesting, membership of the centre, openness/convexity/measurability, and the
  two-sided volume bounds obtained from an `axisCube` sandwich of aspect
  ratio `1/9`;
* the explicit volume ratio of two nested windows of the family, and the
  excess quasi-monotonicity it yields **at the paper's `3^{-j}` normalizer**;
* the **window choice** the harmonic-approximation input demands: an explicit
  centre `y` with `U_{m,n-4}(x) ⊆ y + □_{n-2} ⊆ U_{m,n-1}(x)`.  The source
  asserts the existence of such a `y` and exhibits no construction; the witness
  here is the coordinatewise clamp `wellPlacedCentre x m (n-2)` of `x` into the
  set of centres whose cube of side `3^{n-2}` still fits inside `□_m`.

Nothing in this module is an estimate on a solution: every statement is
geometry or measure bookkeeping.

## References

* `l.excess.decay.good.scales.GMC` (the window choice of
  `l.excess.decay.good.scales.GMC`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open MeasureTheory
open Homogenization (axisCube openCubeSet originCube volumeAverage)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-! ### Membership in a translate -/

/-- A point lies in the translate `c + S` exactly when its back-translate lies
in `S`. -/
theorem mem_translate_iff {c p : Vec d} {S : Set (Vec d)} :
    p ∈ (fun y => c + y) '' S ↔ p - c ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [add_sub_cancel_left]
  · intro h
    refine ⟨p - c, h, ?_⟩
    show c + (p - c) = p
    abel

theorem mem_translatedCube_iff {j : ℤ} {c p : Vec d} :
    p ∈ translatedCube d j c ↔ p - c ∈ cube d j :=
  mem_translate_iff

/-- The centred cubes are nested in the scale. -/
theorem cube_subset_cube_of_le {j l : ℤ} (hjl : j ≤ l) :
    cube d j ⊆ cube d l := by
  intro p hp
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hp ⊢
  intro i
  have h3 : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ l := zpow_le_zpow_right₀ (by norm_num) hjl
  have hpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  exact ⟨by linarith only [(hp i).1, h3], by linarith only [(hp i).2, h3, hpos]⟩

theorem zero_mem_cube (d : ℕ) (j : ℤ) : (0 : Vec d) ∈ cube d j := by
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  exact ⟨by simpa using by linarith only [hpos], by simpa using by linarith only [hpos]⟩

/-! ### Basic shape of the truncated windows -/

theorem truncatedCube_eq (d : ℕ) (m j : ℤ) (x : Vec d) :
    truncatedCube d m j x = translatedCube d j x ∩ cube d m := rfl

theorem truncatedCube_subset_translatedCube (d : ℕ) (m j : ℤ) (x : Vec d) :
    truncatedCube d m j x ⊆ translatedCube d j x :=
  Set.inter_subset_left

theorem truncatedCube_subset_cube (d : ℕ) (m j : ℤ) (x : Vec d) :
    truncatedCube d m j x ⊆ cube d m :=
  Set.inter_subset_right

/-- The truncated windows are nested in the scale. -/
theorem truncatedCube_mono (d : ℕ) (m : ℤ) (x : Vec d) {j l : ℤ} (hjl : j ≤ l) :
    truncatedCube d m j x ⊆ truncatedCube d m l x := by
  refine Set.inter_subset_inter_left _ ?_
  rintro p ⟨y, hy, rfl⟩
  exact ⟨y, cube_subset_cube_of_le hjl hy, rfl⟩

/-- The centre of a truncated window lies in it, as soon as it lies in the
domain cube. -/
theorem mem_truncatedCube_self {x : Vec d} {m : ℤ} (j : ℤ) (hx : x ∈ cube d m) :
    x ∈ truncatedCube d m j x :=
  ⟨⟨0, zero_mem_cube d j, by simp⟩, hx⟩

theorem sub_mem_cube_of_mem_truncatedCube {j m : ℤ} {x p : Vec d}
    (hp : p ∈ truncatedCube d m j x) : p - x ∈ cube d j :=
  mem_translatedCube_iff.mp (truncatedCube_subset_translatedCube d m j x hp)

/-! ### Openness, convexity, measurability -/

theorem isOpenBoundedConvexDomain_cube (d : ℕ) (j : ℤ) :
    Homogenization.IsOpenBoundedConvexDomain (cube d j) :=
  Homogenization.isOpenBoundedConvexDomain_openCubeSet (originCube d j)

theorem isOpenBoundedConvexDomain_translatedCube (d : ℕ) (j : ℤ) (x : Vec d) :
    Homogenization.IsOpenBoundedConvexDomain (translatedCube d j x) := by
  obtain ⟨hopen, ⟨R, hRpos, hR⟩, hconv⟩ := isOpenBoundedConvexDomain_cube d j
  refine ⟨?_, ⟨R + ∑ i : Fin d, |x i|, by positivity, ?_⟩, ?_⟩
  · exact (Homeomorph.addLeft x).isOpenMap _ hopen
  · rintro p ⟨y, hy, rfl⟩ i
    have hy' := hR y hy i
    have hxi : |x i| ≤ ∑ i : Fin d, |x i| :=
      Finset.single_le_sum (f := fun i : Fin d => |x i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have := abs_add_le (x i) (y i)
    simp only [Pi.add_apply]
    linarith only [hy', hxi, this]
  · exact hconv.translate x

theorem isOpenBoundedConvexDomain_truncatedCube (d : ℕ) (m j : ℤ) (x : Vec d) :
    Homogenization.IsOpenBoundedConvexDomain (truncatedCube d m j x) := by
  obtain ⟨hopen, ⟨R, hRpos, hR⟩, hconv⟩ := isOpenBoundedConvexDomain_translatedCube d j x
  obtain ⟨hopen', _, hconv'⟩ := isOpenBoundedConvexDomain_cube d m
  exact ⟨hopen.inter hopen', ⟨R, hRpos, fun y hy i => hR y hy.1 i⟩, hconv.inter hconv'⟩

theorem isOpen_truncatedCube (d : ℕ) (m j : ℤ) (x : Vec d) :
    IsOpen (truncatedCube d m j x) :=
  (isOpenBoundedConvexDomain_truncatedCube d m j x).isOpen

theorem convex_truncatedCube (d : ℕ) (m j : ℤ) (x : Vec d) :
    Convex ℝ (truncatedCube d m j x) :=
  (isOpenBoundedConvexDomain_truncatedCube d m j x).convex

theorem measurableSet_truncatedCube (d : ℕ) (m j : ℤ) (x : Vec d) :
    MeasurableSet (truncatedCube d m j x) :=
  (isOpen_truncatedCube d m j x).measurableSet

theorem volume_truncatedCube_lt_top (d : ℕ) (m j : ℤ) (x : Vec d) :
    volume (truncatedCube d m j x) < ⊤ :=
  (isOpenBoundedConvexDomain_truncatedCube d m j x).volume_lt_top

/-! ### The well-placed centre -/

/-- The clamping gap `3^m/2 - 3^k/2` of the well-placed cube. -/
def wellPlacedHalfGap (m k : ℤ) : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k

/-- **The centre of the well-placed cube**: the coordinatewise clamp of `x` into
the set of centres whose cube of side `3^k` still fits inside `□_m`. -/
def wellPlacedCentre (x : Vec d) (m k : ℤ) : Vec d :=
  fun i => max (-wellPlacedHalfGap m k) (min (wellPlacedHalfGap m k) (x i))

theorem wellPlacedHalfGap_nonneg {m k : ℤ} (hkm : k ≤ m) :
    0 ≤ wellPlacedHalfGap m k := by
  have h : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) hkm
  rw [wellPlacedHalfGap]
  linarith only [h]

theorem neg_wellPlacedHalfGap_le_wellPlacedCentre (x : Vec d) (m k : ℤ) (i : Fin d) :
    -wellPlacedHalfGap m k ≤ wellPlacedCentre x m k i :=
  le_max_left _ _

theorem wellPlacedCentre_le_wellPlacedHalfGap {m k : ℤ} (hkm : k ≤ m) (x : Vec d)
    (i : Fin d) : wellPlacedCentre x m k i ≤ wellPlacedHalfGap m k :=
  max_le (by linarith only [wellPlacedHalfGap_nonneg hkm]) (min_le_left _ _)

/-- **The well-placed cube never leaves `□_m`.** -/
theorem translatedCube_wellPlacedCentre_subset_cube {m k : ℤ} (x : Vec d) (hkm : k ≤ m) :
    translatedCube d k (wellPlacedCentre x m k) ⊆ cube d m := by
  intro p hp
  rw [mem_translatedCube_iff, cube, Homogenization.mem_openCubeSet_originCube_iff] at hp
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hlow := neg_wellPlacedHalfGap_le_wellPlacedCentre x m k i
  have hhigh := wellPlacedCentre_le_wellPlacedHalfGap hkm x i
  have hi := hp i
  rw [wellPlacedHalfGap] at hlow hhigh
  simp only [Pi.sub_apply] at hi
  exact ⟨by linarith only [hi.1, hlow], by linarith only [hi.2, hhigh]⟩

/-- A clamped centre moves by less than half a side. -/
private theorem wellPlacedCentre_sub_bound {m k : ℤ} (hkm : k ≤ m) {x : Vec d}
    (i : Fin d) (hx1 : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < x i)
    (hx2 : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    -((1 / 2 : ℝ) * (3 : ℝ) ^ k) < wellPlacedCentre x m k i - x i ∧
      wellPlacedCentre x m k i - x i < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  have hkpos : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hA : 0 ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  have hAdef : wellPlacedHalfGap m k =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := rfl
  rcases le_total (x i) (-wellPlacedHalfGap m k) with h1 | h1
  · have hc : wellPlacedCentre x m k i = -wellPlacedHalfGap m k := by
      rw [wellPlacedCentre, min_eq_right (h1.trans (by linarith only [hA]))]
      exact max_eq_left h1
    have h1u : x i ≤ -((1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k) := by
      rw [← hAdef]; exact h1
    rw [hc, hAdef]
    exact ⟨by linarith only [h1u, hkpos], by linarith only [hx1]⟩
  · rcases le_total (x i) (wellPlacedHalfGap m k) with h2 | h2
    · have hc : wellPlacedCentre x m k i = x i := by
        rw [wellPlacedCentre, min_eq_right h2]
        exact max_eq_right h1
      rw [hc]
      exact ⟨by linarith only [hkpos], by linarith only [hkpos]⟩
    · have hc : wellPlacedCentre x m k i = wellPlacedHalfGap m k := by
        rw [wellPlacedCentre, min_eq_left h2]
        exact max_eq_right (by linarith only [h2, hA])
      have h2u : (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ x i := by
        rw [← hAdef]; exact h2
      rw [hc, hAdef]
      exact ⟨by linarith only [hx2], by linarith only [h2u, hkpos]⟩

/-- The coordinate computation behind the covering inclusion: the three clamp
regimes (`x_i` below the gap, inside the gap, above the gap). -/
private theorem coord_sub_wellPlacedCentre_bound {m k j : ℤ} {x : Vec d} {i : Fin d}
    {y : ℝ} (hkm : k ≤ m) (hjk : j ≤ k)
    (hj1 : -(1 / 2 : ℝ) * (3 : ℝ) ^ j < y - x i)
    (hj2 : y - x i < (1 / 2 : ℝ) * (3 : ℝ) ^ j)
    (hm1 : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < y)
    (hm2 : y < (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    -(1 / 2 : ℝ) * (3 : ℝ) ^ k < y - wellPlacedCentre x m k i ∧
      y - wellPlacedCentre x m k i < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  have hjk3 : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hjk
  have hA : 0 ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  have hAdef : wellPlacedHalfGap m k =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := rfl
  rcases le_total (x i) (-wellPlacedHalfGap m k) with h1 | h1
  · have hc : wellPlacedCentre x m k i = -wellPlacedHalfGap m k := by
      rw [wellPlacedCentre, min_eq_right (h1.trans (by linarith only [hA]))]
      exact max_eq_left h1
    have h1u : x i ≤ -((1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k) := by
      rw [← hAdef]; exact h1
    rw [hc, hAdef]
    exact ⟨by linarith only [hm1], by linarith only [hj2, h1u, hjk3]⟩
  · rcases le_total (x i) (wellPlacedHalfGap m k) with h2 | h2
    · have hc : wellPlacedCentre x m k i = x i := by
        rw [wellPlacedCentre, min_eq_right h2]
        exact max_eq_right h1
      rw [hc]
      exact ⟨by linarith only [hj1, hjk3], by linarith only [hj2, hjk3]⟩
    · have hc : wellPlacedCentre x m k i = wellPlacedHalfGap m k := by
        rw [wellPlacedCentre, min_eq_left h2]
        exact max_eq_right (by linarith only [h2, hA])
      have h2u : (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ x i := by
        rw [← hAdef]; exact h2
      rw [hc, hAdef]
      exact ⟨by linarith only [hj1, h2u, hjk3], by linarith only [hm2]⟩

/-- **The well-placed cube covers the truncated window.**  For every scale
`j ≤ k` the window `U_{m,j}(x)` lies inside the translated cube `y + □_k`. -/
theorem truncatedCube_subset_translatedCube_wellPlacedCentre {m k j : ℤ} (x : Vec d)
    (hkm : k ≤ m) (hjk : j ≤ k) :
    truncatedCube d m j x ⊆ translatedCube d k (wellPlacedCentre x m k) := by
  intro p hp
  have hpx : p - x ∈ cube d j := sub_mem_cube_of_mem_truncatedCube hp
  have hpm : p ∈ cube d m := truncatedCube_subset_cube d m j x hp
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hpx hpm
  rw [mem_translatedCube_iff, cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hj := hpx i
  simp only [Pi.sub_apply] at hj ⊢
  exact coord_sub_wellPlacedCentre_bound hkm hjk hj.1 hj.2 (hpm i).1 (hpm i).2

/-- **The inscribed cube.**  The well-placed cube of one scale less sits inside
the truncated window. -/
theorem translatedCube_wellPlacedCentre_subset_truncatedCube {m j : ℤ} (x : Vec d)
    (hx : x ∈ cube d m) (hjm : j - 1 ≤ m) :
    translatedCube d (j - 1) (wellPlacedCentre x m (j - 1)) ⊆ truncatedCube d m j x := by
  intro p hp
  have hdomain : p ∈ cube d m := translatedCube_wellPlacedCentre_subset_cube x hjm hp
  refine ⟨?_, hdomain⟩
  rw [mem_translatedCube_iff] at hp ⊢
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hp ⊢
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hx
  intro i
  have hstep : (3 : ℝ) ^ (j - 1) * 3 = (3 : ℝ) ^ j := by
    rw [show j = j - 1 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
  have hcx := wellPlacedCentre_sub_bound (k := j - 1) hjm i (hx i).1 (hx i).2
  have hi := hp i
  simp only [Pi.sub_apply] at hi ⊢
  exact ⟨by linarith only [hi.1, hcx.1, hstep, hpos],
    by linarith only [hi.2, hcx.2, hstep, hpos]⟩

/-! ### The window choice of the printed proof -/

/-- **The window choice.**  With `y := wellPlacedCentre x m (n-2)` the *full*
cube `y + □_{n-2}` lies inside `U_{m,n-1}(x)`, and it contains `U_{m,n-4}(x)`.
This is exactly the pair of inclusions the harmonic-approximation input
demands at its index `n-2`; the source asserts the existence of such a `y` and
exhibits no construction. -/
theorem translatedCube_wellPlacedCentre_subset_truncatedCube_pred {m n : ℤ} {x : Vec d}
    (hx : x ∈ cube d m) (hnm : n - 2 ≤ m) :
    translatedCube d (n - 2) (wellPlacedCentre x m (n - 2)) ⊆ truncatedCube d m (n - 1) x := by
  intro p hp
  have hdomain : p ∈ cube d m := translatedCube_wellPlacedCentre_subset_cube x hnm hp
  refine ⟨?_, hdomain⟩
  rw [mem_translatedCube_iff] at hp ⊢
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hp ⊢
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hx
  intro i
  have hstep : (3 : ℝ) ^ (n - 2) * 9 = (3 : ℝ) ^ n := by
    rw [show n = n - 2 + 2 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hstep1 : (3 : ℝ) ^ (n - 1) * 3 = (3 : ℝ) ^ n := by
    rw [show n = n - 1 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have hcx := wellPlacedCentre_sub_bound (k := n - 2) hnm i (hx i).1 (hx i).2
  have hi := hp i
  simp only [Pi.sub_apply] at hi ⊢
  constructor
  · linarith only [hi.1, hcx.1, hstep, hstep1, hpos]
  · linarith only [hi.2, hcx.2, hstep, hstep1, hpos]

/-- The well-placed centre lies in the domain cube. -/
theorem wellPlacedCentre_mem_cube {m k : ℤ} (x : Vec d) (hkm : k ≤ m) :
    wellPlacedCentre x m k ∈ cube d m := by
  refine translatedCube_wellPlacedCentre_subset_cube x hkm ?_
  exact ⟨0, zero_mem_cube d k, by simp⟩

/-- **The window choice of the printed proof, as the harmonic-approximation
input demands it.**  The source asserts the existence of `y` and exhibits no
construction; the explicit witness is the coordinatewise clamp of `x`. -/
theorem exists_windowChoice {m n : ℤ} {x : Vec d} (hx : x ∈ cube d m) (hnm : n - 2 ≤ m) :
    ∃ y ∈ cube d m,
      truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y ∧
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x :=
  ⟨wellPlacedCentre x m (n - 2), wellPlacedCentre_mem_cube x hnm,
    truncatedCube_subset_translatedCube_wellPlacedCentre x hnm (by omega),
    translatedCube_wellPlacedCentre_subset_truncatedCube_pred hx hnm⟩

/-! ### The `axisCube` sandwich and the volume bounds -/

/-- **The aspect-`1/9` sandwich of a truncated window.** -/
theorem exists_axisCube_sandwich_truncatedCube {m j : ℤ} (x : Vec d)
    (hx : x ∈ cube d m) (hjm : j - 1 ≤ m) :
    ∃ zin zout : Vec d,
      axisCube zin ((3 : ℝ) ^ (j - 2)) ⊆ truncatedCube d m j x ∧
        truncatedCube d m j x ⊆ axisCube zout ((3 : ℝ) ^ j) := by
  refine axisCube_sandwich_of_translateSandwich
    (x := wellPlacedCentre x m (j - 1)) (y := x) ?_
    (truncatedCube_subset_translatedCube d m j x)
  refine subset_trans ?_ (translatedCube_wellPlacedCentre_subset_truncatedCube x hx hjm)
  rintro p ⟨w, hw, rfl⟩
  exact ⟨w, cube_subset_cube_of_le (by omega) hw, rfl⟩

theorem volume_toReal_truncatedCube_bounds {m j : ℤ} (x : Vec d)
    (hx : x ∈ cube d m) (hjm : j - 1 ≤ m) :
    ((3 : ℝ) ^ (j - 2)) ^ d ≤ (volume (truncatedCube d m j x)).toReal ∧
      (volume (truncatedCube d m j x)).toReal ≤ ((3 : ℝ) ^ j) ^ d := by
  obtain ⟨zin, zout, hin, hout⟩ := exists_axisCube_sandwich_truncatedCube x hx hjm
  exact volume_toReal_bounds_of_axisCubeSandwich (d := d) (zin := zin) (zout := zout) hin hout

theorem volume_toReal_truncatedCube_pos {m j : ℤ} (x : Vec d)
    (hx : x ∈ cube d m) (hjm : j - 1 ≤ m) :
    0 < (volume (truncatedCube d m j x)).toReal :=
  lt_of_lt_of_le (by positivity) (volume_toReal_truncatedCube_bounds x hx hjm).1

/-- Squares of affine deviations are integrable on a truncated window. -/
theorem integrableOn_sub_affineEval_sq_truncatedCube {m j : ℤ} (x : Vec d)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (truncatedCube d m j x)))
    (c : ℝ) (g : Vec d) :
    IntegrableOn (fun p => (u p - affineEval c g p) ^ 2) (truncatedCube d m j x) := by
  refine integrableOn_sub_affineEval_sq_of_axisCubeSandwich
    (zout := x + fun _ => -(1 / 2) * (3 : ℝ) ^ j) (Lout := (3 : ℝ) ^ j)
    (zpow_pos (by norm_num) j) (measurableSet_truncatedCube d m j x) ?_ hu c g
  refine subset_trans (truncatedCube_subset_translatedCube d m j x) ?_
  rw [translatedCube, cube, openCubeSet_originCube_eq_axisCube, image_add_axisCube]

/-! ### The volume ratio and excess quasi-monotonicity -/

/-- The explicit ratio constant of the family: `|U_l| / |U_j| ≤ 3^{(l-j+2)d}`. -/
theorem volume_ratio_truncatedCube_le {m j l : ℤ} (x : Vec d)
    (hx : x ∈ cube d m) (hjm : j - 1 ≤ m) (hlm : l - 1 ≤ m) :
    (volume (truncatedCube d m l x)).toReal / (volume (truncatedCube d m j x)).toReal
      ≤ ((3 : ℝ) ^ (l - j + 2)) ^ d := by
  obtain ⟨_, hhi⟩ := volume_toReal_truncatedCube_bounds x hx hlm
  obtain ⟨hlo, _⟩ := volume_toReal_truncatedCube_bounds x hx hjm
  have hjpos : (0 : ℝ) < ((3 : ℝ) ^ (j - 2)) ^ d := by positivity
  have hquot : ((3 : ℝ) ^ l) ^ d / ((3 : ℝ) ^ (j - 2)) ^ d = ((3 : ℝ) ^ (l - j + 2)) ^ d := by
    rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), show l - (j - 2) = l - j + 2 by ring]
  have hbpos : (0 : ℝ) < (volume (truncatedCube d m j x)).toReal := lt_of_lt_of_le hjpos hlo
  rw [← hquot, div_le_div_iff₀ hbpos hjpos]
  calc (volume (truncatedCube d m l x)).toReal * ((3 : ℝ) ^ (j - 2)) ^ d
      ≤ ((3 : ℝ) ^ l) ^ d * ((3 : ℝ) ^ (j - 2)) ^ d :=
        mul_le_mul_of_nonneg_right hhi hjpos.le
    _ ≤ ((3 : ℝ) ^ l) ^ d * (volume (truncatedCube d m j x)).toReal :=
        mul_le_mul_of_nonneg_left hlo (by positivity)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
