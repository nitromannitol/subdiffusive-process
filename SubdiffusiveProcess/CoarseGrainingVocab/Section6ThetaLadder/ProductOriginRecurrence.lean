import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductOneStep

/-!
# Theta-perturbed ladder: the raw origin-cube recurrence

The product comparison is inserted into the already-landed deterministic
one-step excess estimate.  This is the centered coordinate form used after
translating a local comparison window to the origin.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem isWeaklyHarmonicOn_castDomain
    {U V : Set (Vec d)} (hUV : U = V) {a : Vec d → ℝ}
    (u : H1Function U) (hu : IsWeaklyHarmonicOn a U u) :
    IsWeaklyHarmonicOn a V
      (Homogenization.Book.Ch03.castH1Domain hUV u) := by
  subst V
  exact hu

private theorem zero_mem_cube (d : ℕ) (n : ℤ) :
    (0 : Vec d) ∈ cube d n := by
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hp : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  simp only [Pi.zero_apply]
  constructor <;> linarith

private theorem translatedCube_zero_eq_cube (d : ℕ) (n : ℤ) :
    translatedCube d n 0 = cube d n := by
  unfold translatedCube
  simp

private theorem truncatedCube_zero_eq_cube_of_le
    (d : ℕ) {domain n : ℤ} (hn : n ≤ domain) :
    truncatedCube d domain n 0 = cube d n := by
  rw [truncatedCube_eq, translatedCube_zero_eq_cube]
  apply Set.inter_eq_left.mpr
  exact openCubeSet_originCube_subset_of_scale_le hn

/-- The comparison error on the four-scale core, in the exact normalized
`L²` carrier consumed by `excess_oneStep_of_productComparison`. -/
theorem exists_productOriginComparator_coreError
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B)
    {b epsilon alpha Ebase c : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hb : 0 < b) (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (n : ℤ)
    (hparentB : cube d n ⊆ B)
    (u : H1Function (cube d n))
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (cube d n) u)
    (hbaseParent : paperHomogenizationError
      (originCube d n) (originCube d n).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hbaseInner : paperHomogenizationError
      (originCube d (n - 2)) (originCube d (n - 2)).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hparentOne :
      (paperHomogenizationError
        (originCube d n) (originCube d n).scale
        ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta
          hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal ≤ 1) :
    ∃ w : H1Function (translatedCube d (n - 2) 0),
      IsWeaklyHarmonicOn (fun _ ↦ (1 : ℝ))
          (translatedCube d (n - 2) 0) w ∧
      normalizedL2On (truncatedCube d n (n - 4) 0)
          (fun x ↦ u.toFun x - w.toFun x) ≤
        Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) *
          (productComparisonLinearConstant d hd *
            (paperHomogenizationError
              (originCube d (n - 2)) (originCube d (n - 2)).scale
              ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
              (localizedThetaCoeffFamily M L omega hB theta htheta
                hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear)
              alpha).toReal *
            normalizedL2On (cube d n) (fun x ↦ u.toFun x - c)) := by
  have hdomain : cube d n = openCubeSet (originCube d ((n - 2) + 2)) := by
    simp only [cube]
    congr 2
    ring
  let u0 : H1Function (openCubeSet (originCube d ((n - 2) + 2))) :=
    Homogenization.Book.Ch03.castH1Domain hdomain u
  have hu0 : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (openCubeSet (originCube d ((n - 2) + 2))) u0 := by
    exact isWeaklyHarmonicOn_castDomain hdomain u hu
  obtain ⟨v, hv, _htrace, hcmp⟩ :=
    exists_productTwoScaleFlatComparator_linear d hd M L omega hB theta htheta
      hb hepsilon hepsilonHalf hnear halpha (c := c) (n - 2)
      (by simpa only [show n - 2 + 2 = n by ring, cube] using hparentB)
      u0 hu0 (by simpa only [show n - 2 + 2 = n by ring] using hbaseParent)
      hbaseInner (by simpa only [show n - 2 + 2 = n by ring] using hparentOne)
  have hzero : translatedCube d (n - 2) 0 =
      openCubeSet (originCube d (n - 2)) := by
    rw [translatedCube_zero_eq_cube]
    rfl
  let w : H1Function (translatedCube d (n - 2) 0) :=
    Homogenization.Book.Ch03.castH1Domain hzero.symm v
  have hw : IsWeaklyHarmonicOn (fun _ ↦ (1 : ℝ))
      (translatedCube d (n - 2) 0) w := by
    exact isWeaklyHarmonicOn_castDomain hzero.symm v
      (Section6Schauder.isUnitWeaklyHarmonicOn_iff.1 hv)
  refine ⟨w, hw, ?_⟩
  have huMem : MemLp (fun x ↦ u.toFun x - w.toFun x) 2
      (volume.restrict (truncatedCube d n (n - 2) 0)) := by
    rw [truncatedCube_zero_eq_cube_of_le d (by omega)]
    have huInner : MemLp u.toFun 2 (volume.restrict (cube d (n - 2))) :=
      u.memL2.mono_measure
        (Measure.restrict_mono (by
          simpa only [cube] using
            (openCubeSet_originCube_subset_of_scale_le
              (d := d) (by omega : n - 2 ≤ n))) le_rfl)
    have hwInner : MemLp w.toFun 2 (volume.restrict (cube d (n - 2))) := by
      rw [← translatedCube_zero_eq_cube]
      exact w.memL2
    exact huInner.sub hwInner
  have htransfer := normalizedL2On_truncatedCube_le
    (d := d) (m := n) (j := n - 4) (l := n - 2)
    (x := (0 : Vec d)) (zero_mem_cube d n) (by omega) (by omega)
    (by omega) (integrableOn_sq_truncatedCube 0 huMem)
  have hfull : normalizedL2On (truncatedCube d n (n - 2) 0)
        (fun x ↦ u.toFun x - w.toFun x) =
      cubeLpNorm (originCube d (n - 2)) 2
        (fun x ↦ (productConcentricInnerH1 d (n - 2) u0).toFun x -
          v.toFun x) := by
    rw [truncatedCube_zero_eq_cube_of_le d (by omega), cube]
    have hmem : MemLp
        (fun x ↦ (productConcentricInnerH1 d (n - 2) u0).toFun x - v.toFun x) 2
        (volume.restrict (openCubeSet (originCube d (n - 2)))) :=
      (productConcentricInnerH1 d (n - 2) u0).memL2.sub v.memL2
    rw [← normalizedL2On_openCubeSet_eq_cubeLpNorm _ hmem]
    apply normalizedL2On_congr_ae
    filter_upwards with x
    rw [show w.toFun = v.toFun by
      simp only [w, Homogenization.Book.Ch03.castH1Domain_toFun],
      show (productConcentricInnerH1 d (n - 2) u0).toFun = u0.toFun by rfl,
      show u0.toFun = u.toFun by
        simp only [u0, Homogenization.Book.Ch03.castH1Domain_toFun]]
  have hparentNorm : normalizedL2On
        (openCubeSet (originCube d (n - 2 + 2)))
        (fun x ↦ u0.toFun x - c) =
      normalizedL2On (cube d n) (fun x ↦ u.toFun x - c) := by
    rw [show u0.toFun = u.toFun by
      simp only [u0, Homogenization.Book.Ch03.castH1Domain_toFun]]
    have hset : openCubeSet (originCube d (n - 2 + 2)) = cube d n := hdomain.symm
    rw [hset]
  rw [hparentNorm] at hcmp
  rw [hfull] at htransfer
  have hcmp' := mul_le_mul_of_nonneg_left hcmp
    (Real.sqrt_nonneg (((3 : ℝ) ^ (4 : ℤ)) ^ d))
  have hfactor : n - 2 - (n - 4) + 2 = (4 : ℤ) := by ring
  rw [hfactor] at htransfer
  exact htransfer.trans hcmp'

/-- Dimension-only coefficient multiplying the product homogenization error
in the origin-cube excess recurrence. -/
def productOriginRecurrenceErrorConstant (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) (k : ℕ) : ℝ :=
  oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k *
    Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) *
    productComparisonLinearConstant d hd

theorem productOriginRecurrenceErrorConstant_nonneg
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (k : ℕ) :
    0 ≤ productOriginRecurrenceErrorConstant d hd k := by
  unfold productOriginRecurrenceErrorConstant
  exact mul_nonneg
    (mul_nonneg
      (oneStepRemainderConst_nonneg d
        (Section6Schauder.schauderInteriorConst_nonneg d) k)
      (Real.sqrt_nonneg _))
    (productComparisonLinearConstant_nonneg d hd)

/-- Raw homogeneous product-coefficient recurrence at the origin.  The
ordinary cutoff error appears only through the product error `Etheta`; the
second occurrence is the usual affine-slope leg. -/
theorem productOrigin_excessRecurrence
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B)
    {b epsilon alpha Ebase : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hb : 0 < b) (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (n : ℤ) (k : ℕ) (hk : 6 ≤ k)
    (hparentB : cube d n ⊆ B)
    (u : H1Function (cube d n))
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (cube d n) u)
    (hbaseParent : paperHomogenizationError
      (originCube d n) (originCube d n).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hbaseInner : paperHomogenizationError
      (originCube d (n - 2)) (originCube d (n - 2)).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hparentOne :
      (paperHomogenizationError
        (originCube d n) (originCube d n).scale
        ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta
          hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal ≤ 1)
    (ell : Affine d)
    (hell : ell ∈ affineMinimizers (cube d n) u.toFun) :
    let Etheta := (paperHomogenizationError
      (originCube d (n - 2)) (originCube d (n - 2)).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (localizedThetaCoeffFamily M L omega hB theta htheta
        hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal
    excess (n - (k : ℤ)) (cube d (n - (k : ℤ))) u.toFun ≤
      oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
          excess n (cube d n) u.toFun +
        productOriginRecurrenceErrorConstant d hd k * Etheta *
          (excess n (cube d n) u.toFun +
            Real.sqrt (d : ℝ) / 2 * Real.sqrt (vecNormSq ell.slope)) := by
  dsimp only
  let Etheta := (paperHomogenizationError
    (originCube d (n - 2)) (originCube d (n - 2)).scale
    ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
    (localizedThetaCoeffFamily M L omega hB theta htheta
      hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal
  let N := normalizedL2On (cube d n)
    (fun x ↦ u.toFun x - averageOn (cube d n) u.toFun)
  obtain ⟨w, hw, hD⟩ := exists_productOriginComparator_coreError
    d hd M L omega hB theta htheta hb hepsilon hepsilonHalf hnear halpha n
      hparentB u hu hbaseParent hbaseInner hparentOne
      (c := averageOn (cube d n) u.toFun)
  have hsmall : translatedCube d (n - 4) 0 ⊆ cube d n := by
    rw [translatedCube_zero_eq_cube]
    exact openCubeSet_originCube_subset_of_scale_le (by omega)
  have hsub : truncatedCube d n (n - 4) 0 ⊆
      translatedCube d (n - 2) 0 := by
    intro x hx
    have hx' := hx.1
    rw [translatedCube_zero_eq_cube] at hx' ⊢
    exact openCubeSet_originCube_subset_of_scale_le (by omega) hx'
  have hone := excess_oneStep_of_productComparison
    (d := d) (domain := n) (n := n) (k := k) (by omega) hk
    (x := (0 : Vec d)) (y := (0 : Vec d)) (zero_mem_cube d n)
    (by omega) hsmall hsub u w hw hD
  rw [truncatedCube_zero_eq_cube_of_le d (by omega),
    truncatedCube_zero_eq_cube_of_le d (by omega)] at hone
  have huN : MemLp u.toFun 2
      (volume.restrict (truncatedCube d n n 0)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d n n 0) le_rfl)
  have hell' : ell ∈ affineMinimizers (truncatedCube d n n 0) u.toFun := by
    rw [truncatedCube_zero_eq_cube_of_le d le_rfl]
    exact hell
  have hmean := normalizedL2On_sub_average_le
    (d := d) (m := n) (n := n) (x := (0 : Vec d))
    (zero_mem_cube d n) (by omega) huN hell'
  rw [truncatedCube_zero_eq_cube_of_le d le_rfl] at hmean
  have hcoef : 0 ≤ productOriginRecurrenceErrorConstant d hd k * Etheta :=
    mul_nonneg (productOriginRecurrenceErrorConstant_nonneg d hd k)
      ENNReal.toReal_nonneg
  have hreplace := mul_le_mul_of_nonneg_left hmean hcoef
  have hDscaled :
      oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k *
          ((3 : ℝ) ^ (-n) *
            (Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) *
              (productComparisonLinearConstant d hd * Etheta * N))) ≤
        productOriginRecurrenceErrorConstant d hd k * Etheta *
          ((3 : ℝ) ^ (-n) * N) := by
    unfold productOriginRecurrenceErrorConstant
    norm_num
    ring_nf
    exact le_rfl
  dsimp only [Etheta, N] at hDscaled hreplace ⊢
  exact hone.trans (add_le_add le_rfl
    (hDscaled.trans hreplace))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
