module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.CellEnvelope
public import Homogenization.Geometry.Translation
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.SimplexMesh

@[expose] public section

/-!
# The triadic dilation of a Kuhn cell

Step 3 of the strict-decay proof  compares the
mesh of the generation-`NR` simplex with *the* mesh of the unit simplex used to
define `q_R`: "its triadic subdivision into simplices of size `3^{(N-1)R}` is,
after rescaling, the mesh used in `e.strict.decay.qR.def`".

This file supplies that rescaling as an explicit map on Kuhn cells.  With

```text
phi y = 3^k y + z ,      z = cubeCenter (scale k cube of index c),
```

the cell `V` of scale `-R` is carried to `dilateKuhnCell k R c V`, of scale
`k - R`, and *all three* realizations of a Kuhn cell -- the open simplex, the
half-open partition cell, and the closed simplex -- are carried to their images
under `phi`.  The proof is one computation: the triadic local coordinates of
`phi y` in the image cube are `3^k` times those of `y` in `V`, and every
defining condition of the three realizations is invariant under multiplying the
local coordinates and the cube size by the same positive number.

The order-sorting condition of the half-open cell needs the extra remark that
`Tuple.sort` is invariant under scaling by a positive constant, which is
`Tuple.sort_const_mul` below.

## Consequences

* `cellSup_dilateKuhnCell` -- the cellwise supremum transports,
  `sup_{closure (Psi V)} B = sup_{closure V} (B o phi)`, which is the geometric
  identity the outer weight of Step 3 needs;
* `volume_openCarrier_dilateKuhnCell` -- the volume scales by `3^{kd}`;
* `openCarrier_inter_dilateKuhnCell` -- intersections with the parent transport,
  so the cell weights `|U cap T|` scale by the same factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

open Homogenization Set MeasureTheory

open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-! ## The affine map -/

/-- The affine map `y ↦ 3^k y + z`, with `z` the
centre of the scale-`k` triadic cube of index `c`. -/
def cellAffineMap (k : ℕ) (c : Fin d → ℤ) (y : Vec d) : Vec d :=
  fun i => (c i : ℝ) * (3 : ℝ) ^ (k : ℤ) + (3 : ℝ) ^ (k : ℤ) * y i

theorem three_zpow_pos' (m : ℤ) : (0 : ℝ) < (3 : ℝ) ^ m :=
  zpow_pos (by norm_num) m

theorem cellAffineMap_eq_smul_add (k : ℕ) (c : Fin d → ℤ) (y : Vec d) :
    cellAffineMap k c y =
      ((3 : ℝ) ^ (k : ℤ)) • y +
        cubeCenter (⟨(k : ℤ), c⟩ : TriadicCube d) := by
  funext i
  simp only [cellAffineMap, cubeCenter, cubeScaleFactor, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem cellAffineMap_injective (k : ℕ) (c : Fin d → ℤ) :
    Function.Injective (cellAffineMap (d := d) k c) := by
  intro y y' h
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := three_zpow_pos' (k : ℤ)
  funext i
  have hi := congrFun h i
  simp only [cellAffineMap] at hi
  have hcancel : (3 : ℝ) ^ (k : ℤ) * y i = (3 : ℝ) ^ (k : ℤ) * y' i := by linarith
  exact mul_left_cancel₀ (ne_of_gt hpos) hcancel

/-- The affine map is surjective. -/
theorem cellAffineMap_surjective (k : ℕ) (c : Fin d → ℤ) (x : Vec d) :
    ∃ y : Vec d, cellAffineMap k c y = x := by
  have ha : ((3 : ℝ) ^ (k : ℤ)) ≠ 0 := ne_of_gt (three_zpow_pos' (k : ℤ))
  refine ⟨fun i => ((3 : ℝ) ^ (k : ℤ))⁻¹ * (x i - (c i : ℝ) * (3 : ℝ) ^ (k : ℤ)), ?_⟩
  funext i
  simp only [cellAffineMap]
  rw [mul_inv_cancel_left₀ ha]
  ring

/-! ## The cell map -/

/-- The Kuhn cell obtained from a scale-`-R` cell by the affine map
`cellAffineMap k c`. -/
def dilateKuhnCell (k R : ℕ) (c : Fin d → ℤ) (V : KuhnCell d) : KuhnCell d :=
  ⟨⟨V.supportCube.scale + (k : ℤ), fun i => V.supportCube.index i + 3 ^ R * c i⟩,
    V.order⟩

@[simp] theorem dilateKuhnCell_order (k R : ℕ) (c : Fin d → ℤ) (V : KuhnCell d) :
    (dilateKuhnCell k R c V).order = V.order := rfl

@[simp] theorem dilateKuhnCell_scale (k R : ℕ) (c : Fin d → ℤ) (V : KuhnCell d) :
    (dilateKuhnCell k R c V).supportCube.scale =
      V.supportCube.scale + (k : ℤ) := rfl

theorem dilateKuhnCell_injective (k R : ℕ) (c : Fin d → ℤ) :
    Function.Injective (dilateKuhnCell (d := d) k R c) := by
  rintro ⟨⟨s, idx⟩, sigma⟩ ⟨⟨s', idx'⟩, sigma'⟩ h
  simp only [dilateKuhnCell, KuhnCell.mk.injEq, TriadicCube.mk.injEq] at h
  obtain ⟨⟨hs, hidx⟩, hsigma⟩ := h
  have hs' : s = s' := by omega
  refine congrArg₂ KuhnCell.mk (congrArg₂ TriadicCube.mk hs' ?_) hsigma
  funext i
  have := congrFun hidx i
  omega

theorem cubeScaleFactor_dilateKuhnCell (k R : ℕ) (c : Fin d → ℤ) (V : KuhnCell d) :
    cubeScaleFactor (dilateKuhnCell k R c V).supportCube =
      (3 : ℝ) ^ (k : ℤ) * cubeScaleFactor V.supportCube := by
  simp only [cubeScaleFactor, dilateKuhnCell]
  rw [add_comm, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]

/-- **The local coordinates scale.**  The triadic local coordinates of the image
point in the image cube are `3^k` times those of the original point. -/
theorem triadicLocalCoordinate_cellAffineMap {k R : ℕ} {c : Fin d → ℤ}
    {V : KuhnCell d} (hV : V.supportCube.scale = -(R : ℤ)) (y : Vec d) (i : Fin d) :
    triadicLocalCoordinate (dilateKuhnCell k R c V).supportCube
        (cellAffineMap k c y) i =
      (3 : ℝ) ^ (k : ℤ) * triadicLocalCoordinate V.supportCube y i := by
  simp only [triadicLocalCoordinate, dilateKuhnCell, cellAffineMap, cubeScaleFactor,
    hV]
  push_cast
  rw [add_comm (-(R : ℤ)) (k : ℤ), zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
    zpow_neg, ← zpow_natCast (3 : ℝ) R]
  have hne : ((3 : ℝ) ^ (R : ℤ)) ≠ 0 := ne_of_gt (three_zpow_pos' (R : ℤ))
  field_simp
  ring

/-! ## Sorting is invariant under a positive rescaling -/

/-- `Tuple.sort` does not see a positive scaling of its argument. -/
theorem sort_const_mul {a : ℝ} (ha : 0 < a) (f : Fin d → ℝ) :
    Tuple.sort (fun i => a * f i) = Tuple.sort f := by
  obtain ⟨hmono, htie⟩ :=
    (Tuple.eq_sort_iff (f := f) (σ := Tuple.sort f)).1 rfl
  refine ((Tuple.eq_sort_iff (f := fun i => a * f i)
    (σ := Tuple.sort f)).2 ⟨?_, ?_⟩).symm
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (hmono hij) ha.le
  · intro i j hij heq
    exact htie i j hij (mul_left_cancel₀ (ne_of_gt ha) heq)

/-! ## The three realizations transport -/

private theorem mem_cubeSet_iff_loc {Q : TriadicCube d} {x : Vec d} :
    x ∈ cubeSet Q ↔ ∀ i : Fin d,
      -((1 : ℝ) / 2) * cubeScaleFactor Q ≤ triadicLocalCoordinate Q x i ∧
        triadicLocalCoordinate Q x i < (1 / 2 : ℝ) * cubeScaleFactor Q := by
  simp only [cubeSet, Set.mem_ofPred_eq, triadicLocalCoordinate, sub_mul, add_mul]
  constructor <;> intro h i <;> exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩

private theorem mem_openCubeSet_iff_loc {Q : TriadicCube d} {x : Vec d} :
    x ∈ openCubeSet Q ↔ ∀ i : Fin d,
      -((1 : ℝ) / 2) * cubeScaleFactor Q < triadicLocalCoordinate Q x i ∧
        triadicLocalCoordinate Q x i < (1 / 2 : ℝ) * cubeScaleFactor Q := by
  simp only [openCubeSet, Set.mem_ofPred_eq, triadicLocalCoordinate, sub_mul, add_mul]
  constructor <;> intro h i <;> exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩

private theorem mem_closedBall_iff_loc {Q : TriadicCube d} {x : Vec d} :
    x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) ↔ ∀ i : Fin d,
      -((1 : ℝ) / 2) * cubeScaleFactor Q ≤ triadicLocalCoordinate Q x i ∧
        triadicLocalCoordinate Q x i ≤ (1 / 2 : ℝ) * cubeScaleFactor Q := by
  rw [closedBall_cubeCenter_eq_pi_Icc]
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc,
    triadicLocalCoordinate, cubeCenter, cubeRadius]
  constructor <;> intro h i <;> exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩

/-- The open simplex transports. -/
theorem mem_openCarrier_dilateKuhnCell_iff {k R : ℕ} {c : Fin d → ℤ}
    {V : KuhnCell d} (hV : V.supportCube.scale = -(R : ℤ)) {y : Vec d} :
    cellAffineMap k c y ∈ (dilateKuhnCell k R c V).openCarrier ↔
      y ∈ V.openCarrier := by
  have ha : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := three_zpow_pos' (k : ℤ)
  have hloc := triadicLocalCoordinate_cellAffineMap (d := d) (k := k) (c := c) hV y
  have hs := cubeScaleFactor_dilateKuhnCell (d := d) k R c V
  rw [KuhnCell.mem_openCarrier_iff, KuhnCell.mem_openCarrier_iff,
    mem_openCubeSet_iff_loc, mem_openCubeSet_iff_loc]
  simp only [hloc, hs, dilateKuhnCell_order]
  constructor
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · have := (hbox i).1
      nlinarith [this]
    · have := (hbox i).2
      nlinarith [this]
    · have := hord i j hij
      nlinarith [this]
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · have := (hbox i).1
      nlinarith [this]
    · have := (hbox i).2
      nlinarith [this]
    · have := hord i j hij
      nlinarith [this]

/-- The closed simplex transports. -/
theorem mem_closedCarrier_dilateKuhnCell_iff {k R : ℕ} {c : Fin d → ℤ}
    {V : KuhnCell d} (hV : V.supportCube.scale = -(R : ℤ)) {y : Vec d} :
    cellAffineMap k c y ∈ (dilateKuhnCell k R c V).closedCarrier ↔
      y ∈ V.closedCarrier := by
  have ha : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := three_zpow_pos' (k : ℤ)
  have hloc := triadicLocalCoordinate_cellAffineMap (d := d) (k := k) (c := c) hV y
  have hs := cubeScaleFactor_dilateKuhnCell (d := d) k R c V
  simp only [KuhnCell.closedCarrier, Set.mem_ofPred_eq]
  rw [mem_closedBall_iff_loc, mem_closedBall_iff_loc]
  simp only [hloc, hs, dilateKuhnCell_order]
  constructor
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · have := (hbox i).1
      nlinarith [this]
    · have := (hbox i).2
      nlinarith [this]
    · have := hord i j hij
      nlinarith [this]
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · have := (hbox i).1
      nlinarith [this]
    · have := (hbox i).2
      nlinarith [this]
    · have := hord i j hij
      nlinarith [this]

/-- The half-open partition cell transports. -/
theorem mem_carrier_dilateKuhnCell_iff {k R : ℕ} {c : Fin d → ℤ}
    {V : KuhnCell d} (hV : V.supportCube.scale = -(R : ℤ)) {y : Vec d} :
    cellAffineMap k c y ∈ (dilateKuhnCell k R c V).carrier ↔ y ∈ V.carrier := by
  have ha : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := three_zpow_pos' (k : ℤ)
  have hloc := triadicLocalCoordinate_cellAffineMap (d := d) (k := k) (c := c) hV y
  have hs := cubeScaleFactor_dilateKuhnCell (d := d) k R c V
  have hsort : Tuple.sort (triadicLocalCoordinate
      (dilateKuhnCell k R c V).supportCube (cellAffineMap k c y)) =
      Tuple.sort (triadicLocalCoordinate V.supportCube y) := by
    have hfun : triadicLocalCoordinate (dilateKuhnCell k R c V).supportCube
        (cellAffineMap k c y) =
        fun i => (3 : ℝ) ^ (k : ℤ) * triadicLocalCoordinate V.supportCube y i :=
      funext hloc
    rw [hfun, sort_const_mul ha]
  simp only [KuhnCell.carrier, Set.mem_ofPred_eq, hsort, dilateKuhnCell_order]
  rw [mem_cubeSet_iff_loc, mem_cubeSet_iff_loc]
  simp only [hloc, hs]
  constructor
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ⟨?_, ?_⟩, hord⟩
    · have := (hbox i).1
      nlinarith [this]
    · have := (hbox i).2
      nlinarith [this]
  · rintro ⟨hbox, hord⟩
    refine ⟨fun i => ⟨?_, ?_⟩, hord⟩
    · have := (hbox i).1
      nlinarith [this]
    · have := (hbox i).2
      nlinarith [this]

/-! ## The image formulations -/

theorem openCarrier_dilateKuhnCell {k R : ℕ} {c : Fin d → ℤ} {V : KuhnCell d}
    (hV : V.supportCube.scale = -(R : ℤ)) :
    (dilateKuhnCell k R c V).openCarrier = cellAffineMap k c '' V.openCarrier := by
  ext x
  obtain ⟨y, rfl⟩ := cellAffineMap_surjective k c x
  constructor
  · intro hx
    exact ⟨y, (mem_openCarrier_dilateKuhnCell_iff hV).1 hx, rfl⟩
  · rintro ⟨y', hy', hy'eq⟩
    have hyy : y' = y := cellAffineMap_injective k c hy'eq
    subst hyy
    exact (mem_openCarrier_dilateKuhnCell_iff hV).2 hy'

theorem closedCarrier_dilateKuhnCell {k R : ℕ} {c : Fin d → ℤ} {V : KuhnCell d}
    (hV : V.supportCube.scale = -(R : ℤ)) :
    (dilateKuhnCell k R c V).closedCarrier =
      cellAffineMap k c '' V.closedCarrier := by
  ext x
  obtain ⟨y, rfl⟩ := cellAffineMap_surjective k c x
  constructor
  · intro hx
    exact ⟨y, (mem_closedCarrier_dilateKuhnCell_iff hV).1 hx, rfl⟩
  · rintro ⟨y', hy', hy'eq⟩
    have hyy : y' = y := cellAffineMap_injective k c hy'eq
    subst hyy
    exact (mem_closedCarrier_dilateKuhnCell_iff hV).2 hy'

theorem carrier_dilateKuhnCell {k R : ℕ} {c : Fin d → ℤ} {V : KuhnCell d}
    (hV : V.supportCube.scale = -(R : ℤ)) :
    (dilateKuhnCell k R c V).carrier = cellAffineMap k c '' V.carrier := by
  ext x
  obtain ⟨y, rfl⟩ := cellAffineMap_surjective k c x
  constructor
  · intro hx
    exact ⟨y, (mem_carrier_dilateKuhnCell_iff hV).1 hx, rfl⟩
  · rintro ⟨y', hy', hy'eq⟩
    have hyy : y' = y := cellAffineMap_injective k c hy'eq
    subst hyy
    exact (mem_carrier_dilateKuhnCell_iff hV).2 hy'

/-! ## The cellwise supremum -/

/-- **The cellwise supremum transports.**  This is the geometric identity that
identifies the outer weight  with the unit-scale
cell weight of `e.strict.decay.qR.def`. -/
theorem cellSup_dilateKuhnCell {k R : ℕ} {c : Fin d → ℤ} {V : KuhnCell d}
    (hV : V.supportCube.scale = -(R : ℤ)) (B : Vec d → ℝ) :
    cellSup B (dilateKuhnCell k R c V) =
      cellSup (fun y => B (cellAffineMap k c y)) V := by
  rw [cellSup, cellSup, closedCarrier_dilateKuhnCell hV, Set.image_image]

/-! ## Volumes -/

/-- The image of a set under the affine map is a dilate followed by a
translation. -/
theorem image_cellAffineMap_eq (k : ℕ) (c : Fin d → ℤ) (A : Set (Vec d)) :
    cellAffineMap k c '' A =
      translateSet (cubeCenter (⟨(k : ℤ), c⟩ : TriadicCube d))
        (((3 : ℝ) ^ (k : ℤ)) • A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨((3 : ℝ) ^ (k : ℤ)) • y, ⟨y, hy, rfl⟩, cellAffineMap_eq_smul_add k c y⟩
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (cellAffineMap_eq_smul_add k c y)⟩

/-- The affine map scales volume by `3^{kd}`. -/
theorem volume_image_cellAffineMap (k : ℕ) (c : Fin d → ℤ) (A : Set (Vec d)) :
    volume (cellAffineMap k c '' A) =
      ENNReal.ofReal (((3 : ℝ) ^ (k : ℤ)) ^ d) * volume A := by
  rw [image_cellAffineMap_eq, volume_translateSet_eq, Measure.addHaar_smul]
  congr 2
  rw [Module.finrank_fin_fun, abs_of_pos (pow_pos (three_zpow_pos' (k : ℤ)) d)]

/-- The real-valued form of the volume scaling. -/
theorem volume_toReal_image_cellAffineMap (k : ℕ) (c : Fin d → ℤ)
    (A : Set (Vec d)) :
    (volume (cellAffineMap k c '' A)).toReal =
      ((3 : ℝ) ^ (k : ℤ)) ^ d * (volume A).toReal := by
  rw [volume_image_cellAffineMap, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt (pow_pos (three_zpow_pos' (k : ℤ)) d))]

/-- Intersections transport, because the affine map is injective. -/
theorem image_cellAffineMap_inter (k : ℕ) (c : Fin d → ℤ) (A B : Set (Vec d)) :
    cellAffineMap k c '' (A ∩ B) =
      (cellAffineMap k c '' A) ∩ (cellAffineMap k c '' B) :=
  Set.image_inter (cellAffineMap_injective k c)

/-- **The cell weights scale by the same factor as the parent volume.** -/
theorem volume_toReal_inter_dilateKuhnCell {k R R' : ℕ} {c : Fin d → ℤ}
    {P V : KuhnCell d} (hP : P.supportCube.scale = -(R' : ℤ))
    (hV : V.supportCube.scale = -(R : ℤ)) :
    (volume ((dilateKuhnCell k R' c P).openCarrier ∩
        (dilateKuhnCell k R c V).openCarrier)).toReal =
      ((3 : ℝ) ^ (k : ℤ)) ^ d *
        (volume (P.openCarrier ∩ V.openCarrier)).toReal := by
  rw [openCarrier_dilateKuhnCell hP, openCarrier_dilateKuhnCell hV,
    ← image_cellAffineMap_inter, volume_toReal_image_cellAffineMap]

/-- The volume of the image cell. -/
theorem volume_toReal_openCarrier_dilateKuhnCell {k R : ℕ} {c : Fin d → ℤ}
    {V : KuhnCell d} (hV : V.supportCube.scale = -(R : ℤ)) :
    (volume (dilateKuhnCell k R c V).openCarrier).toReal =
      ((3 : ℝ) ^ (k : ℤ)) ^ d * (volume V.openCarrier).toReal := by
  rw [openCarrier_dilateKuhnCell hV, volume_toReal_image_cellAffineMap]

/-! ## Separation of a partition cell from a parent simplex -/

/-- **A partition cell that meets the interior of a parent simplex lies inside
it.**  This is the separation statement isolated by the covering half of
`exists_triadicSubMesh`, stated on its own: a half-open scale-`j` cell of the
cube decomposition of `U.supportCube` whose realization contains a point of the
open parent simplex has its whole interior inside that parent. -/
theorem openCarrier_subset_openCarrier_of_mem_carrier {U : KuhnCell d} {j : ℤ}
    (hj : j ≤ U.supportCube.scale) {T : KuhnCell d}
    (hT : T ∈ triadicSimplexPartition U.supportCube j) {x : Vec d}
    (hxU : x ∈ U.openCarrier) (hxT : x ∈ T.carrier) :
    T.openCarrier ⊆ U.openCarrier := by
  obtain ⟨V, hV, hTV⟩ :=
    triadicSimplexPartition_refines_openCarrier U.supportCube
      (le_refl U.supportCube.scale) hj hT
  have hVQ : V.supportCube = U.supportCube := by
    have hmem : V.supportCube ∈
        descendantsAtScale U.supportCube U.supportCube.scale :=
      mem_triadicSimplexPartition_iff.mp hV
    rw [descendantsAtScale_self, Finset.mem_singleton] at hmem
    exact hmem
  have hxVclosed : x ∈ V.closedCarrier :=
    closure_openCarrier_subset_closedCarrier V
      (closure_mono hTV (carrier_subset_closure_openCarrier T hxT))
  have hVU : V = U := by
    have horder : V.order = U.order :=
      order_eq_of_mem_closedCarrier_of_mem_openCarrier hVQ hxVclosed hxU
    cases V with
    | mk QV piV =>
        cases U with
        | mk QU piU =>
            simp only at hVQ horder
            simp only [KuhnCell.mk.injEq]
            exact ⟨hVQ, horder⟩
  rw [← hVU]
  exact hTV

/-- **The dichotomy the mesh restriction uses.**  A partition cell either has
its interior inside the parent simplex or misses it entirely. -/
theorem openCarrier_inter_eq_empty_of_not_subset {U : KuhnCell d} {j : ℤ}
    (hj : j ≤ U.supportCube.scale) {T : KuhnCell d}
    (hT : T ∈ triadicSimplexPartition U.supportCube j)
    (hsub : ¬ T.openCarrier ⊆ U.openCarrier) :
    U.openCarrier ∩ T.openCarrier = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  exact hsub (openCarrier_subset_openCarrier_of_mem_carrier hj hT hx.1
    (T.openCarrier_subset_carrier hx.2))

/-! ## The inverse map -/

/-- The inverse of `cellAffineMap k c`. -/
def cellAffineMapInv (k : ℕ) (c : Fin d → ℤ) (x : Vec d) : Vec d :=
  fun i => ((3 : ℝ) ^ (k : ℤ))⁻¹ * (x i - (c i : ℝ) * (3 : ℝ) ^ (k : ℤ))

theorem cellAffineMapInv_cellAffineMap (k : ℕ) (c : Fin d → ℤ) (y : Vec d) :
    cellAffineMapInv k c (cellAffineMap k c y) = y := by
  have ha : ((3 : ℝ) ^ (k : ℤ)) ≠ 0 := ne_of_gt (three_zpow_pos' (k : ℤ))
  funext i
  simp only [cellAffineMapInv, cellAffineMap]
  field_simp
  ring

theorem cellAffineMap_cellAffineMapInv (k : ℕ) (c : Fin d → ℤ) (x : Vec d) :
    cellAffineMap k c (cellAffineMapInv k c x) = x := by
  have ha : ((3 : ℝ) ^ (k : ℤ)) ≠ 0 := ne_of_gt (three_zpow_pos' (k : ℤ))
  funext i
  simp only [cellAffineMapInv, cellAffineMap]
  rw [mul_inv_cancel_left₀ ha]
  ring

theorem measurable_cellAffineMapInv (k : ℕ) (c : Fin d → ℤ) :
    Measurable (cellAffineMapInv (d := d) k c) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact ((measurable_pi_apply i).sub measurable_const).const_mul _

theorem image_cellAffineMap_eq_preimage (k : ℕ) (c : Fin d → ℤ) (A : Set (Vec d)) :
    cellAffineMap k c '' A = cellAffineMapInv k c ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [cellAffineMapInv_cellAffineMap] using hy
  · intro hx
    exact ⟨cellAffineMapInv k c x, hx, cellAffineMap_cellAffineMapInv k c x⟩

theorem measurableSet_image_cellAffineMap (k : ℕ) (c : Fin d → ℤ) {A : Set (Vec d)}
    (hA : MeasurableSet A) : MeasurableSet (cellAffineMap k c '' A) := by
  rw [image_cellAffineMap_eq_preimage]
  exact measurable_cellAffineMapInv k c hA

/-! ## The explicit sub-mesh -/

/-- **The triadic sub-mesh of a triadic simplex**, as an explicit `Finset`: the
scale-`(scale U - R)` cells of the cube decomposition whose interiors lie inside
`U`.  This is the witness of `exists_triadicSubMesh`, named so that its
membership in the cube decomposition is available to consumers. -/
def triadicSubMesh (U : KuhnCell d) (R : ℕ) : Finset (KuhnCell d) :=
  @Finset.filter _ (fun T => T.openCarrier ⊆ U.openCarrier)
    (fun _ => Classical.propDecidable _)
    (triadicSimplexPartition U.supportCube (U.supportCube.scale - (R : ℤ)))

theorem triadicSubMesh_subset (U : KuhnCell d) (R : ℕ) :
    triadicSubMesh U R ⊆
      triadicSimplexPartition U.supportCube (U.supportCube.scale - (R : ℤ)) := by
  intro T hT
  simp only [triadicSubMesh, Finset.mem_filter] at hT
  exact hT.1

theorem supportCube_scale_of_mem_triadicSubMesh {U : KuhnCell d} {R : ℕ}
    {T : KuhnCell d} (hT : T ∈ triadicSubMesh U R) :
    T.supportCube.scale = U.supportCube.scale - (R : ℤ) :=
  supportCube_scale_eq_of_mem_triadicSimplexPartition (by omega)
    (triadicSubMesh_subset U R hT)

theorem openCarrier_subset_of_mem_triadicSubMesh {U : KuhnCell d} {R : ℕ}
    {T : KuhnCell d} (hT : T ∈ triadicSubMesh U R) :
    T.openCarrier ⊆ U.openCarrier := by
  simp only [triadicSubMesh, Finset.mem_filter] at hT
  exact hT.2

/-- The explicit sub-mesh covers the parent simplex. -/
theorem openCarrier_subset_iUnion_triadicSubMesh (U : KuhnCell d) (R : ℕ) :
    U.openCarrier ⊆ ⋃ T ∈ (triadicSubMesh U R : Set (KuhnCell d)), T.carrier := by
  classical
  intro x hx
  have hj : U.supportCube.scale - (R : ℤ) ≤ U.supportCube.scale := by omega
  have hxcube : x ∈ cubeSet U.supportCube :=
    openCubeSet_subset_cubeSet U.supportCube (U.openCarrier_subset_openCubeSet hx)
  rw [cubeSet_eq_iUnion_triadicSimplexPartition U.supportCube hj] at hxcube
  obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hxcube
  refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨?_, hxT⟩⟩
  refine Finset.mem_coe.mpr ?_
  simp only [triadicSubMesh, Finset.mem_filter]
  exact ⟨hT, openCarrier_subset_openCarrier_of_mem_carrier hj hT hx hxT⟩

/-- A cell of the decomposition outside the sub-mesh misses the parent. -/
theorem inter_openCarrier_eq_empty_of_notMem_triadicSubMesh {U : KuhnCell d}
    {R : ℕ} {T : KuhnCell d}
    (hT : T ∈ triadicSimplexPartition U.supportCube (U.supportCube.scale - (R : ℤ)))
    (hTn : T ∉ triadicSubMesh U R) :
    U.openCarrier ∩ T.openCarrier = ∅ := by
  classical
  have hsub : ¬ T.openCarrier ⊆ U.openCarrier := by
    intro hcon
    refine hTn ?_
    simp only [triadicSubMesh, Finset.mem_filter]
    exact ⟨hT, hcon⟩
  exact openCarrier_inter_eq_empty_of_not_subset (by omega) hT hsub

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn
