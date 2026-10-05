module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepTwoRadiusNeumannAggregation

@[expose] public section

/-!
# Nested source-cell geometry and thermodynamic Neumann readout

The source cells in the one-step lower bound remain at the manuscript's
fixed localization scale while two concentric axis parents are allowed to
grow.  Consequently the retained finite family depends on the auxiliary
radius.  This module records the literal centered-parent geometry and the
correct order of limits: first pass each radius-dependent interior family to
the common thermodynamic readout, then remove the two harmonic radii.

The organization separates geometry from the readout.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

def oneStepCenteredParent {d : ℕ} (z : Vec d) (m : ℤ) : Set (Vec d) :=
  translateSet z (openCubeSet (originCube d m))

theorem openCubeSet_eq_oneStepCenteredParent_cubeCenter {d : ℕ}
    (R : TriadicCube d) :
    openCubeSet R = oneStepCenteredParent (cubeCenter R) R.scale := by
  ext x
  rw [oneStepCenteredParent, mem_translateSet_iff_sub_mem]
  simp only [openCubeSet, cubeScaleFactor, originCube, Pi.zero_apply,
    Int.cast_zero, zero_sub, zero_add]
  constructor
  · intro hx i
    have hi := hx i
    have hlo : -(1 / 2 : ℝ) * (3 : ℝ) ^ R.scale <
        x i - (R.index i : ℝ) * (3 : ℝ) ^ R.scale := by
      calc
        _ = ((R.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ R.scale -
            (R.index i : ℝ) * (3 : ℝ) ^ R.scale := by ring
        _ < _ := sub_lt_sub_right hi.1 _
    have hhi : x i - (R.index i : ℝ) * (3 : ℝ) ^ R.scale <
        (1 / 2 : ℝ) * (3 : ℝ) ^ R.scale := by
      calc
        _ < ((R.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale -
            (R.index i : ℝ) * (3 : ℝ) ^ R.scale :=
          sub_lt_sub_right hi.2 _
        _ = _ := by ring
    simpa [Pi.sub_apply, cubeCenter, cubeScaleFactor] using! And.intro hlo hhi
  · intro hx i
    have hi := hx i
    change -(1 / 2 : ℝ) * (3 : ℝ) ^ R.scale <
        x i - (R.index i : ℝ) * (3 : ℝ) ^ R.scale ∧
      x i - (R.index i : ℝ) * (3 : ℝ) ^ R.scale <
        (1 / 2 : ℝ) * (3 : ℝ) ^ R.scale at hi
    have hlo : ((R.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ R.scale < x i := by
      have := add_lt_add_right hi.1
        ((R.index i : ℝ) * (3 : ℝ) ^ R.scale)
      convert this using 1 <;> ring
    have hhi : x i <
        ((R.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale := by
      have := add_lt_add_right hi.2
        ((R.index i : ℝ) * (3 : ℝ) ^ R.scale)
      convert this using 1 <;> ring
    exact ⟨hlo, hhi⟩

theorem cubeScaleFactor_origin_add_nat_mul_zpow_neg
    {d : ℕ} (m : ℤ) (N : ℕ) :
    cubeScaleFactor (originCube d (m + (N : ℤ))) *
        (3 : ℝ) ^ (-(N : ℤ)) =
      cubeScaleFactor (originCube d m) := by
  simp only [cubeScaleFactor, originCube]
  rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  calc
    (3 : ℝ) ^ m * (3 : ℝ) ^ (N : ℤ) * (3 : ℝ) ^ (-(N : ℤ)) =
        (3 : ℝ) ^ m *
          ((3 : ℝ) ^ (N : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) := by ring
    _ = (3 : ℝ) ^ m * (3 : ℝ) ^ ((N : ℤ) + (-(N : ℤ))) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    _ = (3 : ℝ) ^ m := by simp

theorem openCubeSet_eq_concentricDepthAxisParent {d : ℕ}
    (R : TriadicCube d) (N : ℕ) :
    openCubeSet R =
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner (cubeCenter R) (R.scale + (N : ℤ)))
          (cubeScaleFactor (originCube d (R.scale + (N : ℤ)))) N)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d (R.scale + (N : ℤ)))) N) := by
  rw [openCubeSet_eq_oneStepCenteredParent_cubeCenter,
    oneStepCenteredParent, translateSet_openCubeSet_originCube_eq_axisCube]
  congr 2
  · funext i
    simp only [CubeCalderonZygmund.axisCubeConcentricDepthCorner,
      CubeCalderonZygmund.axisCubeCenter, oneStepCenteredAxisCorner,
      CubeCalderonZygmund.axisCubeConcentricDepthSide]
    rw [cubeScaleFactor_origin_add_nat_mul_zpow_neg]
    ring
  · unfold CubeCalderonZygmund.axisCubeConcentricDepthSide
    exact (cubeScaleFactor_origin_add_nat_mul_zpow_neg R.scale N).symm

theorem concentricDepthAxisCube_subset_axisCubeInnerHalf {d : ℕ}
    (z : Vec d) (L : ℝ) (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N) :
    axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L N)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide L N) ⊆
      axisCubeInnerHalf z L := by
  intro x hx
  rw [axisCubeInnerHalf, mem_translateSet_iff_sub_mem,
    Set.mem_smul_set_iff_inv_smul_mem₀ hL.ne']
  intro i
  have hi := hx i (Set.mem_univ i)
  let r : ℝ := (3 : ℝ) ^ (-(N : ℤ))
  have hr0 : 0 < r := zpow_pos (by norm_num) _
  have hrle : r ≤ (3 : ℝ) ^ (-(1 : ℤ)) := by
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hrthird : r ≤ (1 : ℝ) / 3 := by
    norm_num at hrle ⊢
    exact hrle
  have hcenter : CubeCalderonZygmund.axisCubeCenter z L =
      fun i => z i + L / 2 := rfl
  simp only [CubeCalderonZygmund.axisCubeConcentricDepthCorner,
    CubeCalderonZygmund.axisCubeConcentricDepthSide,
    CubeCalderonZygmund.axisCubeCenter] at hi
  simp only [originCube, cubeCenter, Pi.zero_apply,
    Int.cast_zero, cubeScaleFactor, zpow_zero, cubeRadius,
    Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  have hlo : -(L * r / 2) < x i - (z i + L / 2) := by
    linarith [hi.1]
  have hhi : x i - (z i + L / 2) < L * r / 2 := by
    linarith [hi.2]
  have habs : |x i - (z i + L / 2)| < L * r / 2 := by
    rw [abs_lt]
    exact ⟨by linarith, hhi⟩
  have hratio : L * r / 2 ≤ L / 4 := by
    have := mul_le_mul_of_nonneg_left hrthird hL.le
    nlinarith
  have habs' : |x i - (z i + L / 2)| < L / 4 :=
    habs.trans_le hratio
  rw [abs_lt] at habs'
  simp only [CubeCalderonZygmund.axisCubeCenter, zero_mul, sub_zero]
  norm_num
  rw [abs_of_pos hL]
  calc
    L⁻¹ * |x i - (z i + L / 2)| < L⁻¹ * (L / 4) :=
      mul_lt_mul_of_pos_left (by rw [abs_lt]; exact habs') (inv_pos.mpr hL)
    _ = 1 / 4 := by field_simp [hL.ne']

theorem openCubeSet_subset_centeredParent_innerHalf {d : ℕ}
    (R : TriadicCube d) (N : ℕ) (hN : 1 ≤ N) :
    openCubeSet R ⊆
      axisCubeInnerHalf
        (oneStepCenteredAxisCorner (cubeCenter R) (R.scale + (N : ℤ)))
        (cubeScaleFactor (originCube d (R.scale + (N : ℤ)))) := by
  rw [openCubeSet_eq_concentricDepthAxisParent R N]
  exact concentricDepthAxisCube_subset_axisCubeInnerHalf _ _
    (by
      simpa [cubeScaleFactor] using!
        (zpow_pos (by norm_num : (0 : ℝ) < 3) (R.scale + (N : ℤ)))) N hN

theorem concentricDepthAxisCube_subset_of_le {d : ℕ}
    (z : Vec d) (L : ℝ) (hL : 0 < L) {a b : ℕ} (hab : a ≤ b) :
    axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L b)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide L b) ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L a)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide L a) := by
  intro x hx i _hi
  have hxi := hx i (Set.mem_univ i)
  let rb : ℝ := (3 : ℝ) ^ (-(b : ℤ))
  let ra : ℝ := (3 : ℝ) ^ (-(a : ℤ))
  have hrb0 : 0 < rb := zpow_pos (by norm_num) _
  have hrle : rb ≤ ra := by
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  simp only [CubeCalderonZygmund.axisCubeConcentricDepthCorner,
    CubeCalderonZygmund.axisCubeConcentricDepthSide,
    CubeCalderonZygmund.axisCubeCenter] at hxi ⊢
  change z i + L / 2 - L * ra / 2 < x i ∧
    x i < z i + L / 2 - L * ra / 2 + L * ra
  change z i + L / 2 - L * rb / 2 < x i ∧
    x i < z i + L / 2 - L * rb / 2 + L * rb at hxi
  have hscale : L * rb ≤ L * ra := mul_le_mul_of_nonneg_left hrle hL.le
  constructor <;> linarith

theorem openCubeSet_subset_centeredParent_concentricDepth {d : ℕ}
    (R : TriadicCube d) {a N : ℕ} (haN : a ≤ N) :
    openCubeSet R ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner (cubeCenter R) (R.scale + (N : ℤ)))
          (cubeScaleFactor (originCube d (R.scale + (N : ℤ)))) a)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d (R.scale + (N : ℤ)))) a) := by
  rw [openCubeSet_eq_concentricDepthAxisParent R N]
  exact concentricDepthAxisCube_subset_of_le _ _
    (by
      simpa [cubeScaleFactor] using!
        (zpow_pos (by norm_num : (0 : ℝ) < 3) (R.scale + (N : ℤ)))) haN

/-- Source-scale cells whose centered radius-`N` parent remains in the
ambient origin cube.  This is the literal interior family in the printed
Neumann argument; its complement is the radius-dependent boundary layer. -/
noncomputable def oneStepRetainedSourceCells {d : ℕ}
    (K source : ℤ) (N : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtScale (originCube d K) source).filter fun R =>
    oneStepCenteredParent (cubeCenter R) (source + (N : ℤ)) ⊆
      openCubeSet (originCube d K)

theorem mem_oneStepRetainedSourceCells_iff {d : ℕ}
    {K source : ℤ} {N : ℕ} {R : TriadicCube d} :
    R ∈ oneStepRetainedSourceCells (d := d) K source N ↔
      R ∈ descendantsAtScale (originCube d K) source ∧
      oneStepCenteredParent (cubeCenter R) (source + (N : ℤ)) ⊆
        openCubeSet (originCube d K) := by
  classical
  simp [oneStepRetainedSourceCells]

/-- Complete geometric certificate for one retained source cell and its
centered parent. -/
structure OneStepNestedSourceParentGeometry {d : ℕ}
    (K source : ℤ) (N depth : ℕ) (R : TriadicCube d) : Prop where
  source_mem : R ∈ descendantsAtScale (originCube d K) source
  source_scale : R.scale = source
  parent_subset :
    oneStepCenteredParent (cubeCenter R) (source + (N : ℤ)) ⊆
      openCubeSet (originCube d K)
  source_subset_innerHalf :
    openCubeSet R ⊆
      axisCubeInnerHalf
        (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
        (cubeScaleFactor (originCube d (source + (N : ℤ))))
  source_subset_fixedInterior :
    openCubeSet R ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
          (cubeScaleFactor (originCube d (source + (N : ℤ)))) (depth + 1))
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d (source + (N : ℤ)))) (depth + 1))

theorem oneStepNestedSourceParentGeometry_of_mem {d : ℕ}
    {K source : ℤ} {N depth : ℕ} {R : TriadicCube d}
    (hR : R ∈ oneStepRetainedSourceCells (d := d) K source N)
    (hN : depth + 1 ≤ N) :
    OneStepNestedSourceParentGeometry K source N depth R := by
  rcases mem_oneStepRetainedSourceCells_iff.mp hR with ⟨hdesc, hparent⟩
  have hscale : R.scale = source := scale_eq_of_mem_descendantsAtScale hdesc
  refine ⟨hdesc, hscale, hparent, ?_, ?_⟩
  · simpa only [hscale] using!
      openCubeSet_subset_centeredParent_innerHalf R N (by omega)
  · simpa only [hscale] using!
      openCubeSet_subset_centeredParent_concentricDepth R hN

/-! ## Exact nested normalization -/

/-- The source-side/parent-side quotient is exactly the geometric radius
`3⁻ᴺ`.  This is the scale factor in both arbitrary-axis harmonic
estimates before the normalized restriction ratio is applied. -/
theorem oneStepNested_source_mul_parent_inv {d : ℕ}
    {source : ℤ} (N : ℕ) (R : TriadicCube d)
    (hscale : R.scale = source) :
    cubeScaleFactor R *
        (cubeScaleFactor (originCube d (source + (N : ℤ))))⁻¹ =
      (3 : ℝ) ^ (-(N : ℤ)) := by
  have hparent : 0 < cubeScaleFactor
      (originCube d (source + (N : ℤ))) := by
    simpa [cubeScaleFactor] using!
      (zpow_pos (by norm_num : (0 : ℝ) < 3) (source + (N : ℤ)))
  have hproduct := cubeScaleFactor_origin_add_nat_mul_zpow_neg
    (d := d) source N
  have hR : cubeScaleFactor R = cubeScaleFactor (originCube d source) := by
    simp only [cubeScaleFactor, originCube, hscale]
  rw [hR]
  rw [← hproduct]
  field_simp [hparent.ne']

/-- Exact algebraic form of the literal nested harmonic prefactor.  In
particular the normalized-measure ratio remains present: only the physical
side-length quotient simplifies to `3⁻ᴺ`. -/
theorem oneStepNested_harmonic_prefactor_eq {d : ℕ}
    {source : ℤ} (N : ℕ) (R : TriadicCube d)
    (hscale : R.scale = source) (ratio C S : ℝ) :
    cubeScaleFactor R * (d : ℝ) ^ 2 * ratio *
        (C * (cubeScaleFactor
          (originCube d (source + (N : ℤ))))⁻¹ * S) =
      (d : ℝ) ^ 2 * ratio * C *
        ((3 : ℝ) ^ (-(N : ℤ)) * S) := by
  have hquot := oneStepNested_source_mul_parent_inv N R hscale
  calc
    _ = (d : ℝ) ^ 2 * ratio * C *
        ((cubeScaleFactor R *
          (cubeScaleFactor (originCube d (source + (N : ℤ))))⁻¹) * S) := by
      ring
    _ = _ := by rw [hquot]

/-- Real-volume form of the normalized restriction ratio.  This makes clear
that a larger interior parent produces a ratio larger than one; it is not a
radius-independent harmless constant. -/
theorem triadicAxisNormalizedMeasureRatio_eq_ofReal_volumeRatio {d : ℕ}
    (R : TriadicCube d) {L : ℝ} (hL : 0 < L) :
    triadicAxisNormalizedMeasureRatio R L =
      ENNReal.ofReal (L ^ d / cubeVolume R) := by
  unfold triadicAxisNormalizedMeasureRatio
  rw [← ENNReal.ofReal_div_of_pos
    (inv_pos.mpr (pow_pos hL d))]
  congr 1
  have hvol : 0 < cubeVolume R := cubeVolume_pos R
  field_simp [hvol.ne', (pow_pos hL d).ne']

/-- The fixed Calderon--Zygmund interior side, measured from a source cell
at depth `N`, has the exact residual gap `N - (depth+1)` in the integer
exponent. -/
theorem concentricDepthSide_eq_source_mul_zpow_gap {d : ℕ}
    {source : ℤ} (N depth : ℕ) (R : TriadicCube d)
    (hscale : R.scale = source) :
    CubeCalderonZygmund.axisCubeConcentricDepthSide
        (cubeScaleFactor (originCube d (source + (N : ℤ)))) (depth + 1) =
      cubeScaleFactor R *
        (3 : ℝ) ^ ((N : ℤ) - ((depth + 1 : ℕ) : ℤ)) := by
  unfold CubeCalderonZygmund.axisCubeConcentricDepthSide cubeScaleFactor
  simp only [originCube, hscale]
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
    ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  push_cast
  omega

/-- Exact radius dependence of the normalized-measure restriction factor on
the nested source cell.  Its base is `3^(N-(depth+1))`, so this factor grows
with the auxiliary radius whenever the source cell is strictly inside the
fixed CZ interior. -/
theorem triadicAxisNormalizedMeasureRatio_nested_eq {d : ℕ}
    {source : ℤ} (N depth : ℕ) (R : TriadicCube d)
    (hscale : R.scale = source) :
    triadicAxisNormalizedMeasureRatio R
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d (source + (N : ℤ)))) (depth + 1)) =
      ENNReal.ofReal
        (((3 : ℝ) ^ ((N : ℤ) - ((depth + 1 : ℕ) : ℤ))) ^ d) := by
  let L := CubeCalderonZygmund.axisCubeConcentricDepthSide
    (cubeScaleFactor (originCube d (source + (N : ℤ)))) (depth + 1)
  have hL : 0 < L :=
    CubeCalderonZygmund.axisCubeConcentricDepthSide_pos
      (by
        simpa [cubeScaleFactor] using!
          (zpow_pos (by norm_num : (0 : ℝ) < 3) (source + (N : ℤ)))) _
  rw [triadicAxisNormalizedMeasureRatio_eq_ofReal_volumeRatio R hL]
  congr 1
  rw [show L = cubeScaleFactor R *
      (3 : ℝ) ^ ((N : ℤ) - ((depth + 1 : ℕ) : ℤ)) by
    exact concentricDepthSide_eq_source_mul_zpow_gap N depth R hscale,
    cubeVolume_eq_scaleFactor_pow]
  have hside : 0 < cubeScaleFactor R := by
    simpa [cubeScaleFactor] using!
      (zpow_pos (by norm_num : (0 : ℝ) < 3) R.scale)
  field_simp [hside.ne']
  ring

/-- Fourth-power radius error after retaining the normalized-measure loss in
the nested harmonic estimate.  The first factor is the physical `3⁻ᴺ`
gain.  The second is the fourth power of the `L^(16d)` restriction loss;
the dimension cancels, leaving the quarter power of the residual volume
scale. -/
noncomputable def oneStepNestedHarmonicFourthError
    (depth N : ℕ) : ℝ≥0∞ :=
  ((((3 : ℝ≥0∞)⁻¹) ^ N) ^ (4 : ℕ)) *
    (((3 : ℝ≥0∞) ^ (N - (depth + 1))) ^ (1 / 4 : ℝ))

/-- The literal normalized harmonic error is dominated by a geometric
sequence.  The deliberately coarse base `3⁻⁴ * 3 = 1/27` is enough for
the thermodynamic passage and avoids changing the source-facing constants. -/
theorem oneStepNestedHarmonicFourthError_le_geometric
    (depth N : ℕ) :
    oneStepNestedHarmonicFourthError depth N ≤
      (((3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ) * 3) ^ N) := by
  have hgap : N - (depth + 1) ≤ N := Nat.sub_le _ _
  have hbase : (1 : ℝ≥0∞) ≤ 3 := by norm_num
  have hpow : (3 : ℝ≥0∞) ^ (N - (depth + 1)) ≤ 3 ^ N :=
    pow_le_pow_right₀ hbase hgap
  have hrpow :
      ((3 : ℝ≥0∞) ^ (N - (depth + 1))) ^ (1 / 4 : ℝ) ≤
        ((3 : ℝ≥0∞) ^ N) ^ (1 / 4 : ℝ) :=
    ENNReal.rpow_le_rpow hpow (by norm_num)
  have hone : (1 : ℝ≥0∞) ≤ (3 : ℝ≥0∞) ^ N :=
    one_le_pow₀ hbase
  have hquarter :
      ((3 : ℝ≥0∞) ^ N) ^ (1 / 4 : ℝ) ≤
        (3 : ℝ≥0∞) ^ N := by
    simpa only [ENNReal.rpow_one] using!
      (ENNReal.rpow_le_rpow_of_exponent_le hone
        (by norm_num : (1 / 4 : ℝ) ≤ 1))
  calc
    oneStepNestedHarmonicFourthError depth N ≤
        ((((3 : ℝ≥0∞)⁻¹) ^ N) ^ (4 : ℕ)) *
          ((3 : ℝ≥0∞) ^ N) := by
      exact mul_le_mul_right (hrpow.trans hquarter)
        ((((3 : ℝ≥0∞)⁻¹) ^ N) ^ (4 : ℕ))
    _ = ((((3 : ℝ≥0∞)⁻¹) ^ (4 : ℕ)) * 3) ^ N := by
      rw [← pow_mul, show N * 4 = 4 * N by omega, pow_mul, mul_pow]

/-- The correctly normalized nested harmonic fourth-moment error vanishes
as the auxiliary parent radius tends to infinity. -/
theorem tendsto_oneStepNestedHarmonicFourthError_zero (depth : ℕ) :
    Filter.Tendsto (oneStepNestedHarmonicFourthError depth)
      Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ) * 3 < 1 by
          apply (ENNReal.toReal_lt_toReal (by finiteness) (by norm_num)).mp
          simp
          norm_num))
  · exact Filter.Eventually.of_forall fun _ ↦ bot_le
  · exact Filter.Eventually.of_forall
      (oneStepNestedHarmonicFourthError_le_geometric depth)

/-- Exact fourth-power cancellation of the dimension in the normalized
restriction loss.  This is the deterministic exponent calculation behind
`oneStepNestedHarmonicFourthError`. -/
theorem nestedRestrictionRatio_rpow_four_eq
    {d : ℕ} (hd : 3 ≤ d) {N depth : ℕ} (hN : depth + 1 ≤ N) :
    ((ENNReal.ofReal
        (((3 : ℝ) ^ ((N : ℤ) - ((depth + 1 : ℕ) : ℤ))) ^ d)) ^
        (1 / (oneStepHarmonicExponent d hd).exponent).toReal) ^ (4 : ℕ) =
      ((3 : ℝ≥0∞) ^ (N - (depth + 1))) ^ (1 / 4 : ℝ) := by
  have hd0 : 0 < d := by omega
  have hgap : (N : ℤ) - ((depth + 1 : ℕ) : ℤ) =
      (N - (depth + 1) : ℕ) := by omega
  have hexp :
      (1 / (oneStepHarmonicExponent d hd).exponent).toReal =
        1 / (16 * (d : ℝ)) := by
    rw [ENNReal.toReal_div]
    simp only [ENNReal.toReal_one, oneStepHarmonicExponent_toReal]
  rw [hgap, zpow_natCast]
  rw [ENNReal.ofReal_pow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  rw [← ENNReal.rpow_mul]
  congr 1
  · norm_num
  · rw [hexp]
    field_simp
    norm_num

theorem ofReal_three_neg_nat_zpow_eq_ennreal (N : ℕ) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(N : ℤ))) =
      ((3 : ℝ≥0∞)⁻¹) ^ N := by
  rw [zpow_neg, zpow_natCast,
    ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
  rw [ENNReal.inv_pow]
  norm_num

/-- The fourth power of the literal physical gain times normalized
restriction loss is exactly the vanishing error sequence used by the
thermodynamic family interface. -/
theorem ofReal_nestedHarmonicWeight_four_eq
    {d : ℕ} (hd : 3 ≤ d) {N depth : ℕ} (hN : depth + 1 ≤ N) :
    ENNReal.ofReal
        ((((3 : ℝ) ^ (-(N : ℤ))) *
          ((ENNReal.ofReal
            (((3 : ℝ) ^ ((N : ℤ) - ((depth + 1 : ℕ) : ℤ))) ^ d)) ^
              (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal) ^
            (4 : ℕ)) =
      oneStepNestedHarmonicFourthError depth N := by
  rw [ENNReal.ofReal_pow (mul_nonneg (zpow_nonneg (by norm_num) _)
    ENNReal.toReal_nonneg)]
  rw [ENNReal.ofReal_mul (zpow_nonneg (by norm_num) _)]
  rw [ENNReal.ofReal_toReal]
  · rw [mul_pow, ofReal_three_neg_nat_zpow_eq_ennreal,
      nestedRestrictionRatio_rpow_four_eq hd hN]
    rfl
  · finiteness

/-- Source-cell form of `ofReal_nestedHarmonicWeight_four_eq`, with the
actual normalized restriction ratio from the arbitrary-axis Hessian
estimate. -/
theorem ofReal_triadicNestedHarmonicWeight_four_eq
    {d : ℕ} (hd : 3 ≤ d) {source : ℤ} {N depth : ℕ}
    (R : TriadicCube d) (hscale : R.scale = source)
    (hN : depth + 1 ≤ N) :
    ENNReal.ofReal
        ((((3 : ℝ) ^ (-(N : ℤ))) *
          ((triadicAxisNormalizedMeasureRatio R
            (CubeCalderonZygmund.axisCubeConcentricDepthSide
              (cubeScaleFactor (originCube d (source + (N : ℤ))))
              (depth + 1))) ^
              (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal) ^
            (4 : ℕ)) =
      oneStepNestedHarmonicFourthError depth N := by
  rw [triadicAxisNormalizedMeasureRatio_nested_eq N depth R hscale]
  exact ofReal_nestedHarmonicWeight_four_eq hd hN

/-- Deterministic scalar weight multiplying the stationary parent-gradient
observable in a nested source cell. -/
noncomputable def oneStepNestedHarmonicWeight
    (d : ℕ) (hd : 3 ≤ d) (depth N : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(N : ℤ)) *
    ((ENNReal.ofReal
      (((3 : ℝ) ^ ((N : ℤ) - ((depth + 1 : ℕ) : ℤ))) ^ d)) ^
        (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal

theorem oneStepNestedHarmonicWeight_nonneg
    (d : ℕ) (hd : 3 ≤ d) (depth N : ℕ) :
    0 ≤ oneStepNestedHarmonicWeight d hd depth N := by
  exact mul_nonneg (zpow_nonneg (by norm_num) _) ENNReal.toReal_nonneg

theorem ofReal_oneStepNestedHarmonicWeight_four_eq
    {d : ℕ} (hd : 3 ≤ d) {N depth : ℕ} (hN : depth + 1 ≤ N) :
    ENNReal.ofReal
        (oneStepNestedHarmonicWeight d hd depth N ^ (4 : ℕ)) =
      oneStepNestedHarmonicFourthError depth N := by
  exact ofReal_nestedHarmonicWeight_four_eq hd hN

/-- Fourth-moment sweep for a finite family dominated by the literal nested
harmonic weight.  The stochastic input is only the already-established
uniform fourth moment of the parent-gradient observable. -/
theorem lintegral_average_nestedHarmonic_four_le
    {d : ℕ} (hd : 3 ≤ d) {depth N : ℕ} (hN : depth + 1 ≤ N)
    {I Omega : Type*} [DecidableEq I] [MeasurableSpace Omega]
    (mu : Measure Omega) (s : Finset I) (A : ℝ) (hA : 0 ≤ A)
    (F G : I → Omega → ℝ)
    (hF : ∀ i ∈ s, ∀ omega, 0 ≤ F i omega)
    (hle : ∀ i ∈ s, ∀ omega,
      F i omega ≤ A * oneStepNestedHarmonicWeight d hd depth N * G i omega)
    {C : ℝ≥0∞}
    (hG : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal (G i omega ^ (4 : ℕ))) ∂mu ≤ C) :
    ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal (F i omega ^ (4 : ℕ))) ∂mu ≤
      (ENNReal.ofReal (A ^ (4 : ℕ)) * C) *
        oneStepNestedHarmonicFourthError depth N := by
  have hweight : 0 ≤ A * oneStepNestedHarmonicWeight d hd depth N :=
    mul_nonneg hA (oneStepNestedHarmonicWeight_nonneg d hd depth N)
  calc
    _ ≤ ENNReal.ofReal
          ((A * oneStepNestedHarmonicWeight d hd depth N) ^ (4 : ℕ)) *
        ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (G i omega ^ (4 : ℕ))) ∂mu :=
      lintegral_average_four_le_mul_of_pointwise_le mu s
        (A * oneStepNestedHarmonicWeight d hd depth N) hweight F G hF
        (by simpa only [mul_assoc] using! hle)
    _ ≤ ENNReal.ofReal
          ((A * oneStepNestedHarmonicWeight d hd depth N) ^ (4 : ℕ)) * C :=
      mul_le_mul_right hG _
    _ = (ENNReal.ofReal (A ^ (4 : ℕ)) * C) *
        oneStepNestedHarmonicFourthError depth N := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hA 4),
        ofReal_oneStepNestedHarmonicWeight_four_eq hd hN]
      ring

/-! ## Literal weak-Hessian readout -/

/-- The weak Hessian of the literal large Neumann member of a realized
two-radius family.  It is built from the family's exact gradient split, so it
does not choose a second, potentially unrelated Hessian representative. -/
noncomputable def oneStepTwoRadiusNeumannCombinedHessian
    {d : ℕ} {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    (i : ι) (omega : Omega) :
    HasWeakHessianOn (openCubeSet (cell i)) (F.neumann i omega) :=
  weakHessianOfGradEqAddAdd (F.grad_split i omega)
    (F.dirichletHessian i omega)
    (F.localHarmonicHessian i omega)
    (F.outerHarmonicHessian i omega)

/-- Normalized finite-family fourth moment of the literal large-Neumann weak
Hessian.  This is the source's `average_z E[B_z^4]` before the ambient-volume
limit. -/
noncomputable def oneStepTwoRadiusNeumannHessianReadout
    {d : ℕ} {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    (mu : Measure Omega) (s : Finset ι) (cell : ι → TriadicCube d)
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell) : ℝ≥0∞ :=
  ∫⁻ omega, ((s.card : ℝ≥0∞)⁻¹) *
    ∑ i ∈ s, ENNReal.ofReal
      (oneStepCellB (cell i)
        (oneStepTwoRadiusNeumannCombinedHessian F i omega) ^ (4 : ℕ)) ∂mu

/-- The literal weak-Hessian readout is definitionally the Neumann member of
the proved scalar two-radius interface. -/
theorem oneStepTwoRadiusNeumannHessianReadout_eq_toCellFamily
    {d : ℕ} {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    (mu : Measure Omega) (s : Finset ι) (cell : ι → TriadicCube d)
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell) :
    oneStepTwoRadiusNeumannHessianReadout mu s cell F =
      ∫⁻ omega, ((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F.toCellFamily.neumann i omega) ^ (4 : ℕ)) ∂mu := by
  rfl

/-- Finite-volume moment bound obtained by feeding the literal Hessian
realization to the already proved scalar family fold. -/
theorem oneStepTwoRadiusNeumannHessianReadout_le_of_budgets
    {d : ℕ} {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset ι) (cell : ι → TriadicCube d)
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    {D H₁ H₂ : ℝ≥0∞}
    (hD : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F.toCellFamily.dirichlet i omega) ^ (4 : ℕ))) ∂mu ≤ D)
    (hH₁ : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F.toCellFamily.localHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤ H₁)
    (hH₂ : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F.toCellFamily.outerHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤ H₂) :
    oneStepTwoRadiusNeumannHessianReadout mu s cell F ≤
      64 * D + 64 * H₁ + 64 * H₂ := by
  rw [oneStepTwoRadiusNeumannHessianReadout_eq_toCellFamily]
  exact lintegral_twoRadiusNeumann_four_le_of_budgets s F.toCellFamily
    hD hH₁ hH₂

/-- A thermodynamic readout may use a different retained finite family at
each auxiliary radius.  If every such finite-volume readout converges to the
same literal large-volume observable, the two geometric errors can be sent
to zero after the thermodynamic limit. -/
theorem twoRadiusNeumann_thermodynamic_readout_le_delta_sixtyEight
    {readout : ℕ → ℕ → ℕ → ℝ≥0∞} {X delta CD C₁ C₂ : ℝ≥0∞}
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (hreadout : ∀ N₁ N₂,
      Filter.Tendsto (readout N₁ N₂) Filter.atTop (nhds X))
    (hfinite : ∀ N₁ N₂ K,
      readout N₁ N₂ K ≤
        64 * (CD * delta ^ (68 : ℕ)) +
          64 * (C₁ * (((3 : ℝ≥0∞)⁻¹) ^ N₁) ^ (4 : ℕ)) +
          64 * (C₂ * (((3 : ℝ≥0∞)⁻¹) ^ N₂) ^ (4 : ℕ))) :
    X ≤ (64 * CD) * delta ^ (68 : ℕ) := by
  apply twoRadiusNeumann_four_le_delta_sixtyEight hC₁ hC₂
  intro N₁ N₂
  exact le_of_tendsto (hreadout N₁ N₂)
    (Filter.Eventually.of_forall (hfinite N₁ N₂))

/-- Thermodynamic two-radius close with the literal radius errors left
abstract.  This is the normalization-stable form of the preceding theorem:
the manuscript only needs both harmonic errors to vanish, not that either
one be exactly a pure power of `3⁻¹`.

The finite constants multiplying the two errors are kept explicit because
`ENNReal` multiplication is not continuous at the indeterminate
`∞ * 0` branch. -/
theorem twoRadiusNeumann_thermodynamic_readout_le_of_tendsto_zero
    {readout : ℕ → ℕ → ℕ → ℝ≥0∞}
    {error₁ error₂ : ℕ → ℝ≥0∞} {X D C₁ C₂ : ℝ≥0∞}
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (herror₁ : Filter.Tendsto error₁ Filter.atTop (nhds 0))
    (herror₂ : Filter.Tendsto error₂ Filter.atTop (nhds 0))
    (hreadout : ∀ N₁ N₂,
      Filter.Tendsto (readout N₁ N₂) Filter.atTop (nhds X))
    (hfinite : ∀ N₁ N₂ K,
      readout N₁ N₂ K ≤
        64 * D + 64 * (C₁ * error₁ N₁) +
          64 * (C₂ * error₂ N₂)) :
    X ≤ 64 * D := by
  have hfixed : ∀ N₁ N₂,
      X ≤ 64 * D + 64 * (C₁ * error₁ N₁) +
        64 * (C₂ * error₂ N₂) := by
    intro N₁ N₂
    exact le_of_tendsto (hreadout N₁ N₂)
      (Filter.Eventually.of_forall (hfinite N₁ N₂))
  have houter : ∀ N₁, X ≤ 64 * D + 64 * (C₁ * error₁ N₁) := by
    intro N₁
    have herr := ENNReal.Tendsto.const_mul herror₂ (Or.inr hC₂)
    have hscaled := ENNReal.Tendsto.const_mul herr
      (Or.inr (by norm_num : (64 : ℝ≥0∞) ≠ ∞))
    have hright : Filter.Tendsto
        (fun N₂ ↦ 64 * D + 64 * (C₁ * error₁ N₁) +
          64 * (C₂ * error₂ N₂))
        Filter.atTop (nhds (64 * D + 64 * (C₁ * error₁ N₁))) := by
      simpa using! tendsto_const_nhds.add hscaled
    exact ge_of_tendsto hright
      (Filter.Eventually.of_forall (hfixed N₁))
  have herr := ENNReal.Tendsto.const_mul herror₁ (Or.inr hC₁)
  have hscaled := ENNReal.Tendsto.const_mul herr
    (Or.inr (by norm_num : (64 : ℝ≥0∞) ≠ ∞))
  have hright : Filter.Tendsto
      (fun N₁ ↦ 64 * D + 64 * (C₁ * error₁ N₁))
      Filter.atTop (nhds (64 * D)) := by
    simpa using! tendsto_const_nhds.add hscaled
  exact ge_of_tendsto hright (Filter.Eventually.of_forall houter)

/-- Direct thermodynamic close for literal weak-Hessian families on the
radius-dependent retained cells.  Unlike the older fixed-index fold, the
finite type, its retained set, and its cell map may all depend on the two
auxiliary radii and on the ambient volume.  The only common datum is the
large-volume readout `X`.

The three hypotheses `hD`, `hH₁`, and `hH₂` are exactly the persistent
Dirichlet and two harmonic fourth-moment budgets.  The conclusion follows by
the literal-Hessian-to-scalar-family map and then by removing the radii after
the thermodynamic limit. -/
theorem twoRadiusNeumannHessian_thermodynamic_readout_le_delta_sixtyEight
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (Index : ℕ → ℕ → ℕ → Type*)
    [∀ N₁ N₂ K, DecidableEq (Index N₁ N₂ K)]
    (cells : ∀ N₁ N₂ K, Finset (Index N₁ N₂ K))
    (cell : ∀ N₁ N₂ K, Index N₁ N₂ K → TriadicCube d)
    (F : ∀ N₁ N₂ K,
      OneStepTwoRadiusNeumannHessianFamily d (Index N₁ N₂ K) Omega
        (cells N₁ N₂ K) (cell N₁ N₂ K))
    {X delta CD C₁ C₂ : ℝ≥0∞}
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (hreadout : ∀ N₁ N₂,
      Filter.Tendsto
        (fun K ↦ oneStepTwoRadiusNeumannHessianReadout mu
          (cells N₁ N₂ K) (cell N₁ N₂ K) (F N₁ N₂ K))
        Filter.atTop (nhds X))
    (hD : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.dirichlet i omega) ^ (4 : ℕ))) ∂mu ≤
        CD * delta ^ (68 : ℕ))
    (hH₁ : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.localHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
        C₁ * (((3 : ℝ≥0∞)⁻¹) ^ N₁) ^ (4 : ℕ))
    (hH₂ : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.outerHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
        C₂ * (((3 : ℝ≥0∞)⁻¹) ^ N₂) ^ (4 : ℕ)) :
    X ≤ (64 * CD) * delta ^ (68 : ℕ) := by
  apply twoRadiusNeumann_thermodynamic_readout_le_delta_sixtyEight
    hC₁ hC₂ hreadout
  intro N₁ N₂ K
  exact oneStepTwoRadiusNeumannHessianReadout_le_of_budgets
    (cells N₁ N₂ K) (cell N₁ N₂ K) (F N₁ N₂ K)
    (hD N₁ N₂ K) (hH₁ N₁ N₂ K) (hH₂ N₁ N₂ K)

/-- Literal weak-Hessian version of the normalization-stable thermodynamic
fold.  The two error sequences can carry the normalized restriction ratio
from the nested harmonic estimate; only their convergence to zero is used
when the auxiliary radii are removed. -/
theorem twoRadiusNeumannHessian_thermodynamic_readout_le_of_tendsto_zero
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (Index : ℕ → ℕ → ℕ → Type*)
    [∀ N₁ N₂ K, DecidableEq (Index N₁ N₂ K)]
    (cells : ∀ N₁ N₂ K, Finset (Index N₁ N₂ K))
    (cell : ∀ N₁ N₂ K, Index N₁ N₂ K → TriadicCube d)
    (F : ∀ N₁ N₂ K,
      OneStepTwoRadiusNeumannHessianFamily d (Index N₁ N₂ K) Omega
        (cells N₁ N₂ K) (cell N₁ N₂ K))
    {error₁ error₂ : ℕ → ℝ≥0∞} {X D C₁ C₂ : ℝ≥0∞}
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (herror₁ : Filter.Tendsto error₁ Filter.atTop (nhds 0))
    (herror₂ : Filter.Tendsto error₂ Filter.atTop (nhds 0))
    (hreadout : ∀ N₁ N₂,
      Filter.Tendsto
        (fun K ↦ oneStepTwoRadiusNeumannHessianReadout mu
          (cells N₁ N₂ K) (cell N₁ N₂ K) (F N₁ N₂ K))
        Filter.atTop (nhds X))
    (hD : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.dirichlet i omega) ^ (4 : ℕ))) ∂mu ≤ D)
    (hH₁ : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.localHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
        C₁ * error₁ N₁)
    (hH₂ : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.outerHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
        C₂ * error₂ N₂) :
    X ≤ 64 * D := by
  apply twoRadiusNeumann_thermodynamic_readout_le_of_tendsto_zero
    hC₁ hC₂ herror₁ herror₂ hreadout
  intro N₁ N₂ K
  exact oneStepTwoRadiusNeumannHessianReadout_le_of_budgets
    (cells N₁ N₂ K) (cell N₁ N₂ K) (F N₁ N₂ K)
    (hD N₁ N₂ K) (hH₁ N₁ N₂ K) (hH₂ N₁ N₂ K)

/-- Concrete thermodynamic readout for the correctly normalized nested
source-parent families.  This is the endpoint consumed by the one-step
Neumann variational assembly: both literal harmonic fourth moments may carry
their own fixed CZ depths, while the persistent Dirichlet budget survives. -/
theorem twoRadiusNeumannHessian_nested_thermodynamic_readout_le
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (Index : ℕ → ℕ → ℕ → Type*)
    [∀ N₁ N₂ K, DecidableEq (Index N₁ N₂ K)]
    (cells : ∀ N₁ N₂ K, Finset (Index N₁ N₂ K))
    (cell : ∀ N₁ N₂ K, Index N₁ N₂ K → TriadicCube d)
    (F : ∀ N₁ N₂ K,
      OneStepTwoRadiusNeumannHessianFamily d (Index N₁ N₂ K) Omega
        (cells N₁ N₂ K) (cell N₁ N₂ K))
    (depth₁ depth₂ : ℕ) {X D C₁ C₂ : ℝ≥0∞}
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (hreadout : ∀ N₁ N₂,
      Filter.Tendsto
        (fun K ↦ oneStepTwoRadiusNeumannHessianReadout mu
          (cells N₁ N₂ K) (cell N₁ N₂ K) (F N₁ N₂ K))
        Filter.atTop (nhds X))
    (hD : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.dirichlet i omega) ^ (4 : ℕ))) ∂mu ≤ D)
    (hH₁ : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.localHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
        C₁ * oneStepNestedHarmonicFourthError depth₁ N₁)
    (hH₂ : ∀ N₁ N₂ K,
      ∫⁻ omega, ((((cells N₁ N₂ K).card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ cells N₁ N₂ K, ENNReal.ofReal
            (((F N₁ N₂ K).toCellFamily.outerHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
        C₂ * oneStepNestedHarmonicFourthError depth₂ N₂) :
    X ≤ 64 * D := by
  exact twoRadiusNeumannHessian_thermodynamic_readout_le_of_tendsto_zero
    Index cells cell F hC₁ hC₂
    (tendsto_oneStepNestedHarmonicFourthError_zero depth₁)
    (tendsto_oneStepNestedHarmonicFourthError_zero depth₂)
    hreadout hD hH₁ hH₂

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
