module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveDensityPrices
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail

@[expose] public section

/-!
# Pointwise inverse-ratio price on a Section 6 good event

The finite-`q` ellipticity carrier does not control the pointwise coefficient.
The required inverse price instead comes from `GoodFieldOne`/`GoodFieldTwo`
through the already-landed subunit ratio-energy estimate.

PROVENANCE: this is the normalized-coefficient readout in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryOuterCaccioppoli.lean`,
with GMC's exponential shell-ratio carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The saturated subunit deviation is nonnegative. -/
theorem subunitDeviation_nonneg
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ subunitDeviation M m omega := by
  unfold subunitDeviation
  have hzero : (0 : Vec d) ∈ cube d (m : ℤ) := by
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> linarith
  have hsup : 0 ≤ supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) :=
    (abs_nonneg (fullShellBlock m omega 0)).trans
      (abs_apply_le_supNormOn_cube_of_continuous
        (by unfold fullShellBlock; fun_prop) hzero)
  exact le_min zero_le_one
    (add_nonneg
      (add_nonneg (longRatioGradientTail_nonneg m omega) hsup)
      (mul_nonneg M.G4.tauSq_pos.le (by positivity)))

private theorem memLp_hilbertify_of_forceBesovRegularity
    {Q : TriadicCube d} {s : ℝ} {F : Vec d → Vec d}
    (hF : ForceBesovRegularity Q s F) :
    MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  let T : Vec d →L[ℝ] HilbertVec d :=
    ((HilbertVec.continuousLinearEquivVec d).symm).toContinuousLinearMap
  simpa [hilbertifyVecField] using! T.comp_memLp' hF.memLp

/-- The reciprocal normalized cutoff is bounded pointwise by one plus the
square-root ratio-energy envelope. -/
theorem tailCoefficientCubeAverage_div_aCutoff_le_one_add_subunitEnvelope
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    {x : Vec d} (hx : x ∈ cube d (m : ℤ)) :
    tailCoefficientCubeAverage M L m omega /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤
      1 + subunitCollapseConstant d * subunitEnvelope s m *
        subunitDeviation M m omega := by
  let Y : ℝ := subunitCollapseConstant d * subunitEnvelope s m *
    subunitDeviation M m omega
  have hzero : (0 : Vec d) ∈ cube d (m : ℤ) := by
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> linarith
  have hsup : 0 ≤ supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) :=
    (abs_nonneg (fullShellBlock m omega 0)).trans
      (abs_apply_le_supNormOn_cube_of_continuous
        (by unfold fullShellBlock; fun_prop) hzero)
  have hdev : 0 ≤ subunitDeviation M m omega := by
    unfold subunitDeviation
    exact le_min zero_le_one
      (add_nonneg
        (add_nonneg (longRatioGradientTail_nonneg m omega) hsup)
        (mul_nonneg M.G4.tauSq_pos.le (by positivity)))
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact mul_nonneg
      (mul_nonneg (subunitCollapseConstant_pos d).le
        (subunitEnvelope_pos s m).le)
      hdev
  have hratio := ratioEnergy_le_of_mem_goodEvent M hmL hsLower hsUpper
    omega hgood hx
  have hsquare :
      (tailCoefficientCubeAverage M L m omega /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1) ^ 2 ≤ Y ^ 2 := by
    dsimp only [Y]
    nlinarith [sq_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
        tailCoefficientCubeAverage M L m omega - 1)]
  have habs :
      |tailCoefficientCubeAverage M L m omega /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1| ≤ Y := by
    exact (sq_le_sq₀ (abs_nonneg _) hY).mp (by simpa [sq_abs] using! hsquare)
  have hraw := (le_abs_self
    (tailCoefficientCubeAverage M L m omega /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1)).trans habs
  dsimp only [Y] at hraw ⊢
  linarith only [hraw]

/-- Translation-covariant form of the pointwise inverse-ratio price.  This is
the form used by physical cells in the fixed `9^d` cover. -/
theorem tailAverage_div_aCutoff_le_one_add_subunitEnvelope
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (z : Vec d) (hgood : omega ∈ goodEvent M none m z 1 s)
    {x : Vec d} (hx : x ∈ translatedCube d (m : ℤ) z) :
    tailAverage M L m omega (translatedCube d (m : ℤ) z) /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤
      1 + subunitCollapseConstant d * subunitEnvelope s m *
        subunitDeviation M m (translatePotentialSample z omega) := by
  have hgood0 : translatePotentialSample z omega ∈
      goodEvent M none m 0 1 s :=
    (Section6Covariance.mem_goodEvent_iff_translate_zero
      M none m 1 s z omega).mp hgood
  have hx0 : x - z ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.mem_translatedCube_iff.mp hx
  have hbase :=
    tailCoefficientCubeAverage_div_aCutoff_le_one_add_subunitEnvelope
      M hmL hsLower hsUpper (translatePotentialSample z omega) hgood0 hx0
  rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample,
    Section6Covariance.aCutoff_translatePotentialSample] at hbase
  simpa [sub_add_cancel] using! hbase



theorem volumeAverage_boundaryCoerciveForceDensity_cubeFluctuation_le_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s t : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hQ : openCubeSet Q ⊆ cube d (m : ℤ))
    (g : Vec d → Vec d) (hg : ForceBesovRegularity Q t g) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveForceDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
          (cubeFluctuationVec Q g)) ≤
      (tailCoefficientCubeAverage M L m omega)⁻¹ *
        (1 + subunitCollapseConstant d * subunitEnvelope s m *
          subunitDeviation M m omega) *
        (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q t g ^ 2 := by
  let sigma := tailCoefficientCubeAverage M L m omega
  let B := 1 + subunitCollapseConstant d * subunitEnvelope s m *
    subunitDeviation M m omega
  have hsigma : 0 < sigma := tailCoefficientCubeAverage_pos M L m omega
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg zero_le_one
      (mul_nonneg
        (mul_nonneg (subunitCollapseConstant_pos d).le
          (subunitEnvelope_pos s m).le)
        (subunitDeviation_nonneg M m omega))
  have hgc := forceBesovRegularity_cubeFluctuationVec hg
  have hgcL2 : MemVectorL2 (openCubeSet Q) (cubeFluctuationVec Q g) := by
    have h := memVectorL2_cubeSet_of_forceBesovRegularity hgc
    rw [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at h
    exact h
  have hratio : ∀ x ∈ openCubeSet Q,
      sigma / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤ B := by
    intro x hx
    exact tailCoefficientCubeAverage_div_aCutoff_le_one_add_subunitEnvelope
      M hmL hsLower hsUpper omega hgood (hQ hx)
  have hbase :=
    volumeAverage_boundaryCoerciveForceDensity_localCanonicalFun_le_ratio
      M L omega Q R center hinner hinnerOuter hsigma
      (cubeFluctuationVec Q g) hgcL2 hratio
  have hread : volumeAverage (openCubeSet Q)
      (fun x ↦ sigma⁻¹ * B * vecNormSq (cubeFluctuationVec Q g x)) =
      sigma⁻¹ * B *
        boundaryNormalizedEuclideanL2 Q (cubeFluctuationVec Q g) ^ 2 :=
    volumeAverage_const_mul_vecNormSq_eq_boundaryNormalizedEuclideanL2_sq
      Q (cubeFluctuationVec Q g) (sigma⁻¹ * B)
        (memLp_hilbertify_of_forceBesovRegularity hgc)
  have hL2 := boundaryNormalizedEuclideanL2_cubeFluctuationVec_le hg
  have hL20 := boundaryNormalizedEuclideanL2_nonneg Q (cubeFluctuationVec Q g)
  have hsemi0 :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hg
  have hsqrtCard0 : 0 ≤ Real.sqrt (Fintype.card (Fin d) : ℝ) := Real.sqrt_nonneg _
  have hsq : boundaryNormalizedEuclideanL2 Q (cubeFluctuationVec Q g) ^ 2 ≤
      (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q t g ^ 2 := by
    have hp := pow_le_pow_left₀ hL20 hL2 2
    calc
      _ ≤ (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q t g) ^ 2 := hp
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hcoef : 0 ≤ sigma⁻¹ * B :=
    mul_nonneg (inv_nonneg.mpr hsigma.le) hB
  rw [hread] at hbase
  refine hbase.trans ?_
  have := mul_le_mul_of_nonneg_left hsq hcoef
  dsimp only [sigma, B] at this ⊢
  simpa only [mul_assoc] using! this

/-- Physical translated-event form of the centered force-density price.  The
normalizer is the manuscript's average on `z + cube_m`; the deviation is read
after translating the sample back to the origin event. -/
theorem volumeAverage_boundaryCoerciveForceDensity_cubeFluctuation_le_goodEventAt
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s t : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hgood : omega ∈ goodEvent M none m z 1 s)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hQ : openCubeSet Q ⊆ translatedCube d (m : ℤ) z)
    (g : Vec d → Vec d) (hg : ForceBesovRegularity Q t g) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveForceDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
          (cubeFluctuationVec Q g)) ≤
      (tailAverage M L m omega (translatedCube d (m : ℤ) z))⁻¹ *
        (1 + subunitCollapseConstant d * subunitEnvelope s m *
          subunitDeviation M m (translatePotentialSample z omega)) *
        (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q t g ^ 2 := by
  let sigma := tailAverage M L m omega (translatedCube d (m : ℤ) z)
  let B := 1 + subunitCollapseConstant d * subunitEnvelope s m *
    subunitDeviation M m (translatePotentialSample z omega)
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L m (translatePotentialSample z omega)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg zero_le_one
      (mul_nonneg
        (mul_nonneg (subunitCollapseConstant_pos d).le
          (subunitEnvelope_pos s m).le)
        (subunitDeviation_nonneg M m (translatePotentialSample z omega)))
  have hgc := forceBesovRegularity_cubeFluctuationVec hg
  have hgcL2 : MemVectorL2 (openCubeSet Q) (cubeFluctuationVec Q g) := by
    have h := memVectorL2_cubeSet_of_forceBesovRegularity hgc
    rw [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at h
    exact h
  have hratio : ∀ x ∈ openCubeSet Q,
      sigma / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤ B := by
    intro x hx
    exact tailAverage_div_aCutoff_le_one_add_subunitEnvelope
      M hmL hsLower hsUpper omega z hgood (hQ hx)
  have hbase :=
    volumeAverage_boundaryCoerciveForceDensity_localCanonicalFun_le_ratio
      M L omega Q R center hinner hinnerOuter hsigma
      (cubeFluctuationVec Q g) hgcL2 hratio
  have hread : volumeAverage (openCubeSet Q)
      (fun x ↦ sigma⁻¹ * B * vecNormSq (cubeFluctuationVec Q g x)) =
      sigma⁻¹ * B *
        boundaryNormalizedEuclideanL2 Q (cubeFluctuationVec Q g) ^ 2 :=
    volumeAverage_const_mul_vecNormSq_eq_boundaryNormalizedEuclideanL2_sq
      Q (cubeFluctuationVec Q g) (sigma⁻¹ * B)
        (memLp_hilbertify_of_forceBesovRegularity hgc)
  have hL2 := boundaryNormalizedEuclideanL2_cubeFluctuationVec_le hg
  have hL20 := boundaryNormalizedEuclideanL2_nonneg Q (cubeFluctuationVec Q g)
  have hsq : boundaryNormalizedEuclideanL2 Q (cubeFluctuationVec Q g) ^ 2 ≤
      (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q t g ^ 2 := by
    have hp := pow_le_pow_left₀ hL20 hL2 2
    calc
      _ ≤ (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q t g) ^ 2 := hp
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hcoef : 0 ≤ sigma⁻¹ * B :=
    mul_nonneg (inv_nonneg.mpr hsigma.le) hB
  rw [hread] at hbase
  refine hbase.trans ?_
  have hscaled := mul_le_mul_of_nonneg_left hsq hcoef
  dsimp only [sigma, B] at hscaled ⊢
  simpa only [mul_assoc] using! hscaled

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
