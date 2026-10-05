module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CubeHalfVolume
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius.TranslatedZeroExtension
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalEllipticityControl

@[expose] public section

/-!
# The met-face tile datum: zero extension and anchor containment

 §13.6 items 1 and 2.

The tile price `exists_boundaryTileResidualMeanCap_half` consumes two inputs
that are purely geometric / functional-analytic:

* an `H1Function (openCubeSet (originCube d k))` which vanishes on the half of
  the tile lying outside the domain `V` (item 1), and
* the containment `translateSet (p − z) (cubeSet (originCube d k)) ⊆
  cubeSet (originCube d (n+2))` of the tile's translate in the good-event
  anchor (item 2).

Item 1 is the translated zero extension of `Section6HarmonicRadius`, read on
the tile: for `T = originCube d k` the coordinate hyperplane through the
centre is `{x j0 = 0}`, so the vanishing hypothesis of
`exists_boundaryTileResidualMeanCap_half` reduces to the statement that the
translated half-space misses `V`.  The three side conditions
(`IntegrableOn`, `IntegrableOn (·^2)`, `MemLp (· − mean) 2`) are read off the
`H1Function` package on a finite-measure cube.

Item 2 is the scale-generic form of
`Section6HarmonicApproximation.closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow`:
the committed lemma fixes the inner cube at scale `n − 2`, and a tile sits at
scale `k ≤ n − 2`, so plain monotonicity of `cubeSet (originCube d ·)`
suffices.  A second form takes the tile centre `p` as a free point of the met
face, controlled only through `‖p − z‖_∞ ≤ 3^{n−1}`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-! ## Item 2: the anchor containment for a tile of arbitrary scale -/

/-- Triadic origin cubes are nested in the scale. -/
theorem cubeSet_originCube_subset_of_le {k n : ℤ} (hk : k ≤ n) :
    cubeSet (originCube d k) ⊆ cubeSet (originCube d n) := by
  intro x hx
  rw [mem_cubeSet_originCube_iff] at hx ⊢
  intro i
  have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ n :=
    zpow_le_zpow_right₀ (by norm_num) hk
  exact ⟨by linarith only [(hx i).1, hpow], by linarith only [(hx i).2, hpow]⟩

theorem translateSet_mono {c : Vec d} {U W : Set (Vec d)} (h : U ⊆ W) :
    translateSet c U ⊆ translateSet c W := by
  intro x hx
  exact mem_translateSet_iff_sub_mem.mpr (h (mem_translateSet_iff_sub_mem.mp hx))

/-- **§13.6 item 2, window form.**  The scale-generic version of
`closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow`: a tile of any
scale `k ≤ n − 2` centred at a point of the next window has its translate
inside the good-event anchor `z + 𝔠_{n+2}`. -/
theorem translateSet_cubeSet_originCube_subset_anchor_of_mem_nextWindow
    {m n k : ℤ} {x y z : Vec d} (hk : k ≤ n - 2)
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hy : y ∈ truncatedCube d m n x) :
    translateSet (y - z) (cubeSet (originCube d k)) ⊆
      cubeSet (originCube d (n + 2)) :=
  (translateSet_mono (cubeSet_originCube_subset_of_le hk)).trans
    (closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow hx hy)

/-- **§13.6 item 2, met-face form.**  For a tile centred at an arbitrary point
`p` of the met face `∂𝔠_m ∩ ∂P_q`, the only information used is the sup-norm
bound `‖p − z‖_∞ ≤ 3^{n−1}` — the met face is a face of the projected parent
`z + 𝔠_{n−2}` shifted inside the `(n−1)`-window (§13.5) — together with the
tile scale bound `k ≤ n − 2`.  The anchor `z + 𝔠_{n+2}` has room to spare:
the extreme corner reached is `3.5 · 3^{n−2}` against the anchor's
`40.5 · 3^{n−2}`. -/
theorem translateSet_cubeSet_originCube_subset_anchor_of_mem_metFace
    {n k : ℤ} {p z : Vec d} (hk : k ≤ n - 2)
    (hp : ∀ i, |(p - z) i| ≤ (3 : ℝ) ^ (n - 1)) :
    translateSet (p - z) (cubeSet (originCube d k)) ⊆
      cubeSet (originCube d (n + 2)) := by
  intro w hw
  have hw0 : w - (p - z) ∈ cubeSet (originCube d k) :=
    mem_translateSet_iff_sub_mem.mp hw
  rw [mem_cubeSet_originCube_iff] at hw0 ⊢
  intro i
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ (n - 1) = 3 * (3 : ℝ) ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have h2 : (3 : ℝ) ^ (n + 2) = 81 * (3 : ℝ) ^ (n - 2) := by
    rw [show n + 2 = (n - 2) + 4 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (n - 2) :=
    zpow_le_zpow_right₀ (by norm_num) hk
  have hpi := abs_le.mp (hp i)
  have hid : w i = (w - (p - z)) i + (p - z) i := by
    simp only [Pi.sub_apply]; ring
  rw [h1] at hpi
  rw [hid, h2]
  constructor <;>
    linarith only [(hw0 i).1, (hw0 i).2, hpi.1, hpi.2, hpow, hbase]

/-! ## Item 1: the tile-frame zero extension -/

/-- **§13.6 item 1.**  The zero extension of an `H¹₀(V)` datum, read in the
frame translated by the tile centre `c`, is an `H1Function` on the tile
`openCubeSet (originCube d k)` which vanishes on the upper half
`cubeUpperHalf (originCube d k) j0` and satisfies the three integrability side
conditions of `exists_boundaryTileResidualMeanCap_half`.

The only hypothesis is the geometric separation `houtside`: every point of the
translated open half-space `{x j0 > 0}` lies outside `V`.  For a tile centred
on the met face `∂𝔠_m` (a face of the projected parent, §13.5) this is exactly
the statement that `𝔠_m` lies on the near side of that hyperplane. -/
theorem exists_metFaceTile_zeroExtendedH1 {V : Set (Vec d)}
    (hV : MeasurableSet V) (rho : H10Function V) (c : Vec d) (k : ℤ)
    (j0 : Fin d) (houtside : ∀ x : Vec d, 0 < x j0 → x + c ∉ V) :
    ∃ w : H1Function (openCubeSet (originCube d k)),
      (∀ x, w.toFun x = zeroExtend V rho.toH1Function.toFun (x + c)) ∧
      (∀ x, w.grad x = zeroExtendGrad V rho.toH1Function.grad (x + c)) ∧
      (∀ x ∈ cubeUpperHalf (originCube d k) j0, w.toFun x = 0) ∧
      IntegrableOn w.toFun (openCubeSet (originCube d k)) ∧
      IntegrableOn (fun x => w.toFun x ^ 2) (openCubeSet (originCube d k)) ∧
      MemLp (fun x => w.toFun x - cubeAverage (originCube d k) w.toFun) 2
        (volume.restrict (openCubeSet (originCube d k))) := by
  classical
  set T : TriadicCube d := originCube d k with hT
  let : IsFiniteMeasure (volume.restrict (openCubeSet T)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top T
  refine ⟨translatedZeroExtendH1 hV rho c (openCubeSet T), fun x => rfl,
    fun x => rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx0 : (0 : ℝ) < x j0 := by
      have := ((mem_cubeUpperHalf_iff T j0 x).mp hx).2
      simpa [hT, originCube] using this
    exact zeroExtend_of_notMem _ (houtside x hx0)
  · exact (translatedZeroExtendH1 hV rho c (openCubeSet T)).memL2.integrable
      (by norm_num)
  · simpa only [IntegrableOn] using
      (translatedZeroExtendH1 hV rho c (openCubeSet T)).memL2.integrable_sq
  · exact (translatedZeroExtendH1 hV rho c (openCubeSet T)).memL2.sub
      (memLp_const _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
