module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalControlGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.OffGridFrame
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PaperErrorBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability

@[expose] public section

/-!
# Local ellipticity control for harmonic approximation

This module transports the good-scale error from the anchored cube
`z + cube_(n+2)` to the off-grid comparison cube `y + cube_(n-2)`.  It keeps
the full Chapter-2 error first; the ellipticity and Caccioppoli prefactor caps
are composed in the next layer.

Use the exact translated representative, off-grid stability, and then the
local error-to-ellipticity conversion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section

variable {d : ℕ}

/-- Translating the sample from `z` to `y` is the same as translating the
ambient coefficient field by `y-z`. -/
theorem aCutoffFamily_coeffField_translate_sub
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d) :
    ∀ Q : TriadicCube d,
      ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn Q).toCoeffField =
        translateCoeffField (y - z)
          ((aCutoffFamily M L (translatePotentialSample z omega)).coeffOn Q).toCoeffField := by
  intro Q
  funext p
  change scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample y omega)) p =
    scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega))
        (p + (y - z))
  ext i j
  simp only [scalarCoeffField]
  rw [Section6Covariance.aCutoff_translatePotentialSample,
    Section6Covariance.aCutoff_translatePotentialSample]
  congr 2
  ext k
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The half-open carrier required by off-grid stability still fits in the
anchor cube.  This strengthens the open-cube containment in
`LocalControlGeometry`; the four-scale margin makes the boundary harmless. -/
theorem closedOffGridCube_subset_originAnchorParent
    {m n : ℤ} {x y z : Vec d}
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hD : translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x) :
    translateSet (y - z) (cubeSet (originCube d (n - 2))) ⊆
      cubeSet (originCube d (n + 2)) := by
  intro p hp
  have hyD : y ∈ translatedCube d (n - 2) y := by
    rw [Section6ExcessDecay.mem_translatedCube_iff, sub_self, cube,
      mem_openCubeSet_originCube_iff]
    intro i
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
    simp only [Pi.zero_apply]
    constructor <;> linarith
  have hyx : y - x ∈ cube d (n - 1) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube (hD hyD)
  have hxz : x - z ∈ cube d (n - 3) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hx
  have hp0 : p - (y - z) ∈ cubeSet (originCube d (n - 2)) :=
    mem_translateSet_iff_sub_mem.mp hp
  rw [cube, mem_openCubeSet_originCube_iff] at hyx hxz
  rw [mem_cubeSet_originCube_iff] at hp0 ⊢
  intro i
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ (n - 2) = 3 * (3 : ℝ) ^ (n - 3) := by
    rw [show n - 2 = (n - 3) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have h2 : (3 : ℝ) ^ (n - 1) = 9 * (3 : ℝ) ^ (n - 3) := by
    rw [show n - 1 = (n - 3) + 2 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have h3 : (3 : ℝ) ^ (n + 2) = 243 * (3 : ℝ) ^ (n - 3) := by
    rw [show n + 2 = (n - 3) + 5 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hid : p i = (p - (y - z)) i + (y - x) i + (x - z) i := by
    simp only [Pi.sub_apply]
    ring
  rw [h1] at hp0
  rw [h2] at hyx
  rw [hid, h3]
  constructor <;>
    linarith only [(hp0 i).1, (hp0 i).2, (hyx i).1, (hyx i).2,
      (hxz i).1, (hxz i).2, hbase]

/-- The same half-open containment with the local centre only assumed to lie
in the next (`n`) window.  The anchor has two further scales of slack, so this
is the form needed by the depth-two projected boundary cells. -/
theorem closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow
    {m n : ℤ} {x y z : Vec d}
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hy : y ∈ truncatedCube d m n x) :
    translateSet (y - z) (cubeSet (originCube d (n - 2))) ⊆
      cubeSet (originCube d (n + 2)) := by
  intro p hp
  have hyx : y - x ∈ cube d n :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hy
  have hxz : x - z ∈ cube d (n - 3) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hx
  have hp0 : p - (y - z) ∈ cubeSet (originCube d (n - 2)) :=
    mem_translateSet_iff_sub_mem.mp hp
  rw [cube, mem_openCubeSet_originCube_iff] at hyx hxz
  rw [mem_cubeSet_originCube_iff] at hp0 ⊢
  intro i
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ (n - 2) = 3 * (3 : ℝ) ^ (n - 3) := by
    rw [show n - 2 = (n - 3) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have h2 : (3 : ℝ) ^ n = 27 * (3 : ℝ) ^ (n - 3) := by
    rw [show n = (n - 3) + 3 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have h3 : (3 : ℝ) ^ (n + 2) = 243 * (3 : ℝ) ^ (n - 3) := by
    rw [show n + 2 = (n - 3) + 5 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hid : p i = (p - (y - z)) i + (y - x) i + (x - z) i := by
    simp only [Pi.sub_apply]
    ring
  rw [h1] at hp0
  rw [h2] at hyx
  rw [hid, h3]
  constructor <;>
    linarith only [(hp0 i).1, (hp0 i).2, (hyx i).1, (hyx i).2,
      (hxz i).1, (hxz i).2, hbase]

/-- The local `q=2` error at the manuscript's `s/6` slot is controlled by the
anchored good-scale error at `s/8`. -/
theorem localHomogenizationError_two_le_anchor_of_closedContainment
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L n : ℕ) (hnL : n + 2 ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d)
    (hcontain : translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
      cubeSet (originCube d ((n : ℤ) + 2)))
    (hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  let P : TriadicCube d := originCube d ((n : ℤ) - 2)
  let K : TriadicCube d := originCube d ((n : ℤ) + 2)
  let w : Vec d := y - z
  let A := aCutoffFamily M L (translatePotentialSample z omega)
  let A' := aCutoffFamily M L (translatePotentialSample y omega)
  let a : CoeffField d :=
    scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega))
  let sigma : ℝ := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hrep : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = a := by
    intro Q
    rfl
  have hcompact : IsCompact (closure (cubeSet K)) :=
    (isBounded_cubeSet K).isCompact_closure
  have hnonempty : (closure (cubeSet K)).Nonempty :=
    ⟨cubeCenter K, subset_closure (cubeCenter_mem_cubeSet K)⟩
  let a0 := _root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega)
  have ha : Continuous a0 :=
    _root_.SubdiffusiveProcess.Model.continuous_aCutoff M L (translatePotentialSample z omega)
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty ha.continuousOn
  have hTmeas : MeasurableSet (translateSet w (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage (measurable_id.sub measurable_const)
  have hEll : IsEllipticFieldOn (a0 xmin) (a0 xmax)
      (translateSet w (cubeSet P)) a := by
    constructor
    · have hmatrix : Continuous fun p : Vec d => scalarCoeffField a0 p :=
        ha.smul continuous_const
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      have hentry : Measurable fun p : Vec d => scalarCoeffField a0 p i j :=
        (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
      exact Measurable.ite hTmeas hentry measurable_const
    · intro p hp
      have hpK : p ∈ closure (cubeSet K) := subset_closure (hcontain hp)
      have hlow : a0 xmin ≤ a0 p := hmin hpK
      have hupp : a0 p ≤ a0 xmax := hmax hpK
      exact (isEllipticMatrix_scalarMatrix
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L (translatePotentialSample z omega) p)).mono
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L
            (translatePotentialSample z omega) xmin) hlow hupp
  have hstab := offGridErrorFunctional_le_slot
    (w := w) (P := P) (K := K) A (scalarMatrix (d := d) sigma)
      hs0 (hs.2.trans (by norm_num)) hrep hEll hcontain
  have hscale : (((K.scale - P.scale).toNat : ℕ) : ℝ) = 4 := by
    change (((((n : ℤ) + 2) - ((n : ℤ) - 2)).toNat : ℕ) : ℝ) = 4
    rw [show ((n : ℤ) + 2) - ((n : ℤ) - 2) = 4 by ring]
    rfl
  rw [hscale] at hstab
  have hframe := offGridErrorFunctional_eq_homogenizationErrorOnCube_translate
    w P (by linarith only [hs0] : 0 < s / 6) A' a
      (aCutoffFamily_coeffField_translate_sub M L omega y z)
      (scalarMatrix (d := d) sigma)
  have hparent := homogenizationErrorOnCube_aCutoff_le_section6_of_goodEvent
    M (s := s / 8) (L := L) (m := n + 2)
      (by linarith only [hs.1]) (by linarith only [hs.2]) hnL omega z hgood
  have hparent' : Ch02.HomogenizationErrorOnCube K (s / 8)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤
      section6HomogenizationError M (s / 8) L (n + 2) omega z := by
    simpa [K, A, sigma,
      Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] using hparent
  rw [← hframe]
  exact hstab.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hparent' (Real.rpow_nonneg (by norm_num) _))
    (Real.sqrt_nonneg _))

/-- The local-error transport in the manuscript's original comparison-cube
geometry. -/
theorem localHomogenizationError_two_le_anchor
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L m n : ℕ) (hnL : n + 2 ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x y z : Vec d)
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hD : translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x)
    (hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  apply localHomogenizationError_two_le_anchor_of_closedContainment M hs L n hnL
    omega y z
  · exact closedOffGridCube_subset_originAnchorParent
      (m := (m : ℤ)) (n := (n : ℤ)) hx hD
  · exact hgood

/-- The projected-cell variant: its centre may range in the next truncated
window, which is exactly what the depth-two covering geometry supplies. -/
theorem localHomogenizationError_two_le_anchor_nextWindow
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L m n : ℕ) (hnL : n + 2 ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x y z : Vec d)
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hy : y ∈ truncatedCube d m n x)
    (hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  apply localHomogenizationError_two_le_anchor_of_closedContainment M hs L n hnL
    omega y z
  · exact closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow hx hy
  · exact hgood

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
