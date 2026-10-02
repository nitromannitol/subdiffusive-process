import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.RetainedParentCovering
import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.AxisFamilyAssembly

/-!
# The `a`-free harmonic cell-Hessian estimate

`nfAxisHarmonic_cell_hessian` bounds the normalized weak Hessian of a harmonic
function on a cell `R` of a concentric parent, but only when the cell lies in
the **fixed** concentric interior of depth `a + 1 = nfAxisHarmonicDepth d hd +
1`.  In the shared-parent design of `provider-43` §10 the cells are all
depth-`(N - 1)` descendants of a scale-`(mm - 1)` overlap centre, and those
lie in the parent's inner half but *not* in its fixed concentric interior.

The remedy is to re-centre the *harmonic* estimate: for a cell whose centre
lies in the scale-`(mm - 1)` cube around `z`, the cell-centred **sub-parent**
of scale `mm - 1` still sits inside the scale-`mm` parent
(`oneStepCenteredParent_subset_of_mem`), the harmonic function restricts to
it, and the cell *is* concentric there, at gap `N - 1`.  The only price is the
comparison of the two normalized measures, which is the dimension-only factor
`3 ^ d`, entering the `L²` estimate as `(3 ^ d) ^ (1/2)`.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

variable {d : ℕ}

/-! ## The sub-parent measure comparison -/

/-- The centred parent, in axis-cube form, at an arbitrary centre. -/
theorem axisCube_oneStepCenteredParent_eq (z : Vec d) (m : ℤ) :
    axisCube (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)) =
      oneStepCenteredParent z m :=
  (translateSet_openCubeSet_originCube_eq_axisCube z m).symm

theorem cubeScaleFactor_originCube_pos (d : ℕ) (m : ℤ) :
    (0 : ℝ) < cubeScaleFactor (originCube d m) := by
  simpa [cubeScaleFactor] using (zpow_pos (by norm_num : (0 : ℝ) < 3) m)

theorem cubeScaleFactor_originCube_pred_mul_three (d : ℕ) (m : ℤ) :
    cubeScaleFactor (originCube d (m - 1)) * 3 =
      cubeScaleFactor (originCube d m) := by
  simp only [cubeScaleFactor, originCube]
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  field_simp

/-- **The one new measure comparison.**  The normalized measure of the
cell-centred sub-parent of scale `mm - 1` is dominated by `3 ^ d` times the
normalized measure of the shared scale-`mm` parent. -/
theorem axisCubeNormalizedMeasure_subParent_le_smul
    {z c : Vec d} {mm : ℤ} (hc : c ∈ oneStepCenteredParent z (mm - 1)) :
    CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner c (mm - 1))
        (cubeScaleFactor (originCube d (mm - 1))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ d) •
        CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner z mm)
          (cubeScaleFactor (originCube d mm)) := by
  have hL' : (0 : ℝ) < cubeScaleFactor (originCube d (mm - 1)) :=
    cubeScaleFactor_originCube_pos d (mm - 1)
  have hL : (0 : ℝ) < cubeScaleFactor (originCube d mm) :=
    cubeScaleFactor_originCube_pos d mm
  have hside := cubeScaleFactor_originCube_pred_mul_three d mm
  have hsub :
      axisCube (oneStepCenteredAxisCorner c (mm - 1))
          (cubeScaleFactor (originCube d (mm - 1))) ⊆
        axisCube (oneStepCenteredAxisCorner z mm)
          (cubeScaleFactor (originCube d mm)) := by
    rw [axisCube_oneStepCenteredParent_eq, axisCube_oneStepCenteredParent_eq]
    exact oneStepCenteredParent_subset_of_mem hc
  have hconst : ENNReal.ofReal ((3 : ℝ) ^ d) *
      ENNReal.ofReal ((cubeScaleFactor (originCube d mm) ^ d)⁻¹) =
      ENNReal.ofReal ((cubeScaleFactor (originCube d (mm - 1)) ^ d)⁻¹) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← hside, mul_pow]
    field_simp
  rw [CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
      _ _ hL',
    CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
      _ _ hL,
    smul_smul, hconst]
  refine Measure.le_iff.2 fun A hA ↦ ?_
  simp only [Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  gcongr

/-! ## Coordinate `L²` transfer -/

/-- Coordinate `L²` norms of an `H¹` gradient are finite in the normalized
measure of an axis cube. -/
theorem eLpNorm_axisCubeNormalized_grad_coord_ne_top
    (z : Vec d) {L : ℝ} (hL : 0 < L) (u : H1Function (axisCube z L))
    (k : Fin d) :
    eLpNorm (fun x ↦ u.grad x k) 2
        (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) ≠ ⊤ := by
  have hvec : MemLp (hilbertifyVecField u.grad) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) :=
    CubeCalderonZygmund.memHilbertVectorL2_axisCubeNormalizedMeasure z hL
      (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2)
  refine ne_top_of_le_ne_top hvec.eLpNorm_ne_top ?_
  exact coordinate_eLpNorm_le_euclidean
    (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)
    FiniteLpExponent.two u.grad k

/-- `L²` norms against a measure dominated by `C • ν` cost `C ^ (1/2)`. -/
theorem toReal_eLpNorm_two_le_of_measure_le_smul
    {alpha : Type*} [MeasurableSpace alpha] {mu nu : Measure alpha}
    {C : ℝ} (hC : 0 ≤ C) (hle : mu ≤ ENNReal.ofReal C • nu)
    (f : alpha → ℝ) (hf : eLpNorm f 2 nu ≠ ⊤) :
    (eLpNorm f 2 mu).toReal ≤ C ^ (1 / 2 : ℝ) * (eLpNorm f 2 nu).toReal := by
  have h1 : eLpNorm f 2 mu ≤ eLpNorm f 2 (ENNReal.ofReal C • nu) :=
    eLpNorm_mono_measure f hle
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num) f (ENNReal.ofReal C)] at h1
  have hexp : ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by
    norm_num
  rw [hexp, smul_eq_mul] at h1
  have hne : ENNReal.ofReal C ^ (1 / 2 : ℝ) * eLpNorm f 2 nu ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ hf
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  refine (ENNReal.toReal_mono hne h1).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hC]

/-! ## The cell inside the shared parent -/

/-- A cell of scale gap `N ≥ 1` whose centre lies in the scale-`(mm - 1)` cube
around `z` sits inside the shared scale-`mm` parent at `z`. -/
theorem openCubeSet_subset_sharedParent
    {z : Vec d} {mm : ℤ} {N : ℕ} (hN : 1 ≤ N) {R : TriadicCube d}
    (hRscale : R.scale + (N : ℤ) = mm)
    (hRcentre : cubeCenter R ∈ oneStepCenteredParent z (mm - 1)) :
    openCubeSet R ⊆
      axisCube (oneStepCenteredAxisCorner z mm)
        (cubeScaleFactor (originCube d mm)) := by
  have hL' : (0 : ℝ) < cubeScaleFactor (originCube d (mm - 1)) :=
    cubeScaleFactor_originCube_pos d (mm - 1)
  have hmm : R.scale + ((N - 1 : ℕ) : ℤ) = mm - 1 := by
    have hcast : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    rw [hcast]
    omega
  have hsub :
      axisCube (oneStepCenteredAxisCorner (cubeCenter R) (mm - 1))
          (cubeScaleFactor (originCube d (mm - 1))) ⊆
        axisCube (oneStepCenteredAxisCorner z mm)
          (cubeScaleFactor (originCube d mm)) := by
    rw [axisCube_oneStepCenteredParent_eq, axisCube_oneStepCenteredParent_eq]
    exact oneStepCenteredParent_subset_of_mem hRcentre
  refine Set.Subset.trans ?_ hsub
  refine (nfAxisCell_subset_concentric d R (a := 0) (N := N - 1)
    (Nat.zero_le _) hmm).trans ?_
  exact nfAxisConcentric_subset_parent d _ _ hL' 0

/-! ## The `a`-free harmonic cell-Hessian estimate -/

/-- **The `a`-free harmonic cell-Hessian estimate.**  A harmonic function on
the concentric scale-`mm` parent at `z` obeys the nested-weight cell-Hessian
bound on *every* cell of scale gap `N` whose centre lies in the scale-`(mm-1)`
cube around `z` — no fixed concentric interior hypothesis.  The price is the
dimension-only factor `((3 : ℝ) ^ d) ^ (1/2)`. -/
theorem nfAxisHarmonic_innerHalf_cell_hessian (d : ℕ) (hd : 3 ≤ d)
    (z : Vec d) (mm : ℤ) (N : ℕ) (hN : nfAxisHarmonicDepth d hd + 2 ≤ N)
    (u : H1Function (axisCube (oneStepCenteredAxisCorner z mm)
      (cubeScaleFactor (originCube d mm))))
    (hu : WeakPoissonEquationOn
      (axisCube (oneStepCenteredAxisCorner z mm)
        (cubeScaleFactor (originCube d mm))) u (fun _ ↦ 0))
    (R : TriadicCube d) (hRscale : R.scale + (N : ℤ) = mm)
    (hRcentre : cubeCenter R ∈ oneStepCenteredParent z (mm - 1)) :
    ∃ (v : H1Function (openCubeSet R))
      (H : HasWeakHessianOn (openCubeSet R) v),
      (∀ x, v.grad x = u.grad x) ∧
      oneStepCellB R H ≤
        ((d : ℝ) ^ 2 * nfAxisHarmonicConst d hd * ((3 : ℝ) ^ d) ^ (1 / 2 : ℝ)) *
          oneStepNestedHarmonicWeight d hd (nfAxisHarmonicDepth d hd) (N - 1) *
          (∑ k : Fin d,
            (eLpNorm (fun x ↦ u.grad x k) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure
                (oneStepCenteredAxisCorner z mm)
                (cubeScaleFactor (originCube d mm)))).toReal) := by
  classical
  have hL : (0 : ℝ) < cubeScaleFactor (originCube d mm) :=
    cubeScaleFactor_originCube_pos d mm
  have hL' : (0 : ℝ) < cubeScaleFactor (originCube d (mm - 1)) :=
    cubeScaleFactor_originCube_pos d (mm - 1)
  -- the cell-centred sub-parent sits inside the shared parent
  have hsub :
      axisCube (oneStepCenteredAxisCorner (cubeCenter R) (mm - 1))
          (cubeScaleFactor (originCube d (mm - 1))) ⊆
        axisCube (oneStepCenteredAxisCorner z mm)
          (cubeScaleFactor (originCube d mm)) := by
    rw [axisCube_oneStepCenteredParent_eq, axisCube_oneStepCenteredParent_eq]
    exact oneStepCenteredParent_subset_of_mem hRcentre
  have hu' : WeakPoissonEquationOn
      (axisCube (oneStepCenteredAxisCorner (cubeCenter R) (mm - 1))
        (cubeScaleFactor (originCube d (mm - 1))))
      (u.restrict (isOpen_axisCube _ _) hsub) (fun _ ↦ 0) :=
    hu.restrict (isOpen_axisCube _ _) hsub
  -- the cell is concentric in the sub-parent, at gap `N - 1`
  have hmm : R.scale + ((N - 1 : ℕ) : ℤ) = mm - 1 := by
    have hcast : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by
      have : 1 ≤ N := by omega
      omega
    rw [hcast]
    omega
  have hhalf : openCubeSet R ⊆
      axisCubeInnerHalf (oneStepCenteredAxisCorner (cubeCenter R) (mm - 1))
        (cubeScaleFactor (originCube d (mm - 1))) :=
    nfAxisCell_subset_innerHalf d R (N := N - 1) (by omega) hmm
  have hinner : openCubeSet R ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner (cubeCenter R) (mm - 1))
          (cubeScaleFactor (originCube d (mm - 1)))
          (nfAxisHarmonicDepth d hd + 1))
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d (mm - 1)))
          (nfAxisHarmonicDepth d hd + 1)) :=
    nfAxisCell_subset_concentric d R (a := nfAxisHarmonicDepth d hd + 1)
      (N := N - 1) (by omega) hmm
  obtain ⟨uS, _huSfun, huSgrad, H, hbound⟩ :=
    nfAxisHarmonic_cell_hessian d hd
      (oneStepCenteredAxisCorner (cubeCenter R) (mm - 1))
      (cubeScaleFactor (originCube d (mm - 1))) hL'
      (u.restrict (isOpen_axisCube _ _) hsub) hu' R hhalf hinner
  refine ⟨uS.restrict (isOpen_openCubeSet R) hhalf,
    H.restrict (isOpen_openCubeSet R) hhalf, fun x ↦ ?_, ?_⟩
  · show uS.grad x = u.grad x
    rw [huSgrad]
    rfl
  -- the sum on the sub-parent, in the shared parent's normalization
  have hcoordFin : ∀ k : Fin d,
      eLpNorm (fun x ↦ u.grad x k) 2
        (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner z mm)
          (cubeScaleFactor (originCube d mm))) ≠ ⊤ := fun k ↦
    eLpNorm_axisCubeNormalized_grad_coord_ne_top _ hL u k
  have hsum :
      (∑ k : Fin d,
        (eLpNorm (fun x ↦
            (u.restrict (isOpen_axisCube _ _) hsub).grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner (cubeCenter R) (mm - 1))
            (cubeScaleFactor (originCube d (mm - 1))))).toReal) ≤
        ((3 : ℝ) ^ d) ^ (1 / 2 : ℝ) *
          ∑ k : Fin d,
            (eLpNorm (fun x ↦ u.grad x k) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure
                (oneStepCenteredAxisCorner z mm)
                (cubeScaleFactor (originCube d mm)))).toReal := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    have hfun : (fun x ↦ (u.restrict (isOpen_axisCube _ _) hsub).grad x k) =
        (fun x ↦ u.grad x k) := rfl
    rw [hfun]
    exact toReal_eLpNorm_two_le_of_measure_le_smul (by positivity)
      (axisCubeNormalizedMeasure_subParent_le_smul hRcentre) _ (hcoordFin k)
  -- assemble
  have hpref := nfAxisHarmonic_prefactor_eq_nestedWeight' d hd (N - 1) R hmm
    (∑ k : Fin d,
      (eLpNorm (fun x ↦ (u.restrict (isOpen_axisCube _ _) hsub).grad x k) 2
        (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter R) (mm - 1))
          (cubeScaleFactor (originCube d (mm - 1))))).toReal)
  rw [hpref] at hbound
  refine hbound.trans ?_
  have hnonneg : (0 : ℝ) ≤ ((d : ℝ) ^ 2 * nfAxisHarmonicConst d hd) *
      oneStepNestedHarmonicWeight d hd (nfAxisHarmonicDepth d hd) (N - 1) := by
    have h1 : (0 : ℝ) ≤ (d : ℝ) ^ 2 * nfAxisHarmonicConst d hd := by
      have := (nfAxisHarmonicConst_pos d hd).le
      positivity
    exact mul_nonneg h1 (oneStepNestedHarmonicWeight_nonneg d hd _ _)
  refine (mul_le_mul_of_nonneg_left hsum hnonneg).trans_eq ?_
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
