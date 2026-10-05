module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffNormalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.VarianceInterfaces
public import SubdiffusiveProcess.CoarseGrainingVocab.RestrictionContinuousBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentFactorization
public import Homogenization.Book.Ch04.Theorems.PartitionAverageMoments.Rosenthal
public import Homogenization.Book.Ch04.Theorems.BlockResponseConcentration
public import Homogenization.CoarseGraining.Subadditivity
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

@[expose] public section

/-!
# Centered response averages for the Section 4 homogenization step

This file contains the finite-range probabilistic payload in source : local cutoff observables are centered, split into finitely many
spatial color classes, estimated by the real-exponent Rosenthal endpoint, and
recombined by the triangle inequality.

 the mutual-independence upgrade mirrors the finite-union proof in
`Algsuperdiff/Probability/ColoredAverage.lean` and the GMC specialization in
`NegativeBesovSupport.lean`.  The Rosenthal/recombination layer follows
`Homogenization/Book/Ch04/SourceDescendantMoments.lean`.  In contrast with the
variance-only estimate, pairwise independence is not used here: Rosenthal
requires mutual independence inside each color class.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ProbabilityTheory

noncomputable section


/-- A positive, dimension-dependent radius used only to recover restriction
information from the integral-local cutoff sigma field. -/
noncomputable def responseRestrictionBridgeRadius (d : ℕ) : ℝ :=
  (4 * ((d : ℝ) + 1))⁻¹

theorem responseRestrictionBridgeRadius_pos (d : ℕ) :
    0 < responseRestrictionBridgeRadius d := by
  dsimp [responseRestrictionBridgeRadius]
  positivity

theorem continuous_aCutoffRegCoeffField_entry_for_response {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (i j : Fin d) :
    Continuous (fun x : Vec d => aCutoffRegCoeffField M L omega x i j) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d176_continuous_aCutoffRegCoeffField_entry (d := d) (M := M) (L := L) (omega := omega) (i := i) (j := j)

/-- The scalar cutoff response on a deterministic triadic cube. -/
noncomputable def cutoffResponseOnCube {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  J (Ch02.cubeDomain R) ((aCutoffFamily M L omega).coeffOn R) p q

/-- A cell response centered by the expectation on the origin cube at the
same prescribed scale. -/
noncomputable def centeredCutoffResponseOnCube {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  cutoffResponseOnCube M L p q R omega -
    ∫ eta, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta
      ∂M.P.toMeasure

theorem measurable_cutoffResponseOnCube {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    Measurable (cutoffResponseOnCube M L p q R) := by
  simpa [cutoffResponseOnCube, aCutoffFamily, aCutoffTriadicData] using!
    measurable_cutoff_responseJ M L (Ch02.cubeDomain R) p q

theorem integrable_cutoffResponseOnCube {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    Integrable (cutoffResponseOnCube M L p q R) M.P.toMeasure := by
  simpa [cutoffResponseOnCube, aCutoffFamily, aCutoffTriadicData] using!
    integrable_cutoffResponseJ M L (Ch02.cubeDomain R) p q

theorem measurable_centeredCutoffResponseOnCube {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    Measurable (centeredCutoffResponseOnCube M L n p q R) :=
  (measurable_cutoffResponseOnCube M L p q R).sub measurable_const

theorem integrable_centeredCutoffResponseOnCube {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    Integrable (centeredCutoffResponseOnCube M L n p q R) M.P.toMeasure :=
  (integrable_cutoffResponseOnCube M L p q R).sub (integrable_const _)

/-- Translation covariance of the actual cutoff response. -/
theorem cutoffResponseOnCube_eq_originCube_translate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffResponseOnCube M L p q R omega =
      cutoffResponseOnCube M L p q (originCube d R.scale)
        (translatePotentialSequence (triadicCubeShift R) omega) := by
  unfold cutoffResponseOnCube
  change Ch02.responseJ (Ch02.cubeDomain R)
      ((aCutoffFamily M L omega).coeffOn R) p q =
    Ch02.responseJ (Ch02.cubeDomain (originCube d R.scale))
      ((aCutoffFamily M L
        (translatePotentialSequence (triadicCubeShift R) omega)).coeffOn
          (originCube d R.scale)) p q
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  rw [Ch02.cubeDomain_coe,
    openCubeSet_eq_translateSet_originCube_of_triadicCube R]
  rw [ResponseJ_translateSet_eq_translateCoeffField]
  apply congrArg (ResponseJ (openCubeSet (originCube d R.scale)) p q)
  funext x
  change scalarMatrix
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega (x + triadicCubeShift R)) =
    scalarMatrix
      (_root_.SubdiffusiveProcess.Model.aCutoff M L
        (translatePotentialSequence (triadicCubeShift R) omega) x)
  exact congrArg scalarMatrix
    (aCutoff_translatePotentialSequence M L (triadicCubeShift R) omega x).symm

/-- Stationarity identifies every translated cell expectation with the origin
cube expectation at the same scale. -/
theorem integral_cutoffResponseOnCube_eq_originCube {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    ∫ omega, cutoffResponseOnCube M L p q R omega ∂M.P.toMeasure =
      ∫ omega, cutoffResponseOnCube M L p q (originCube d R.scale) omega
        ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, cutoffResponseOnCube M L p q (originCube d R.scale)
        (translatePotentialSequence (triadicCubeShift R) omega) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact cutoffResponseOnCube_eq_originCube_translate M L p q R omega
    _ = _ := by
      simpa [Function.comp_def] using integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence (triadicCubeShift R))
        (potentialSequenceLaw_stationary M (triadicCubeShift R))
        (cutoffResponseOnCube M L p q (originCube d R.scale))
        (measurable_cutoffResponseOnCube M L p q
          (originCube d R.scale)).aestronglyMeasurable

theorem integral_centeredCutoffResponseOnCube_eq_zero {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (hRscale : R.scale = (n : ℤ)) :
    ∫ omega, centeredCutoffResponseOnCube M L n p q R omega
      ∂M.P.toMeasure = 0 := by
  rw [show (fun omega => centeredCutoffResponseOnCube M L n p q R omega) =
      fun omega => cutoffResponseOnCube M L p q R omega -
        ∫ eta, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta
          ∂M.P.toMeasure by rfl]
  rw [integral_sub (integrable_cutoffResponseOnCube M L p q R) (integrable_const _),
    integral_const, probReal_univ, one_smul,
    integral_cutoffResponseOnCube_eq_originCube M L p q R, hRscale, sub_self]

theorem centeredCutoffResponseOnCube_eq_originCube_translate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (hRscale : R.scale = (n : ℤ)) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    centeredCutoffResponseOnCube M L n p q R omega =
      centeredCutoffResponseOnCube M L n p q (originCube d (n : ℤ))
        (translatePotentialSequence (triadicCubeShift R) omega) := by
  unfold centeredCutoffResponseOnCube
  rw [cutoffResponseOnCube_eq_originCube_translate M L p q R omega, hRscale]

/-- Stationarity transports every real centered-response moment from a cell
to the origin cube at the same scale. -/
theorem integral_abs_centeredCutoffResponseOnCube_rpow_eq_originCube
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (hRscale : R.scale = (n : ℤ)) (xi : ℝ)
    (hxi : 0 ≤ xi) :
    ∫ omega, |centeredCutoffResponseOnCube M L n p q R omega| ^ xi
        ∂M.P.toMeasure =
      ∫ omega,
        |centeredCutoffResponseOnCube M L n p q (originCube d (n : ℤ)) omega| ^ xi
        ∂M.P.toMeasure := by
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    |centeredCutoffResponseOnCube M L n p q (originCube d (n : ℤ)) omega| ^ xi
  have hg : Measurable g := by
    simpa only [g, Real.norm_eq_abs] using!
      (Real.continuous_rpow_const hxi).measurable.comp
        (measurable_centeredCutoffResponseOnCube M L n p q
          (originCube d (n : ℤ))).norm
  calc
    _ = ∫ omega, g (translatePotentialSequence (triadicCubeShift R) omega)
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [centeredCutoffResponseOnCube_eq_originCube_translate
        M L n p q R hRscale omega]
    _ = _ := by
      simpa [g, Function.comp_def] using integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence (triadicCubeShift R))
        (potentialSequenceLaw_stationary M (triadicCubeShift R)) g
        hg.aestronglyMeasurable

/-- Integrability of a centered response moment is likewise stationary. -/
theorem integrable_abs_centeredCutoffResponseOnCube_rpow_iff_originCube
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (hRscale : R.scale = (n : ℤ)) (xi : ℝ)
    (hxi : 0 ≤ xi) :
    Integrable
        (fun omega => |centeredCutoffResponseOnCube M L n p q R omega| ^ xi)
        M.P.toMeasure ↔
      Integrable
        (fun omega =>
          |centeredCutoffResponseOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ xi) M.P.toMeasure := by
  let T := translatePotentialSequence (triadicCubeShift R)
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    |centeredCutoffResponseOnCube M L n p q (originCube d (n : ℤ)) omega| ^ xi
  have hT : MeasurePreserving T M.P.toMeasure M.P.toMeasure :=
    ⟨measurable_translatePotentialSequence (triadicCubeShift R),
      potentialSequenceLaw_stationary M (triadicCubeShift R)⟩
  have hg : AEStronglyMeasurable g M.P.toMeasure := by
    have hmeas : Measurable g := by
      simpa only [g, Real.norm_eq_abs] using!
        (Real.continuous_rpow_const hxi).measurable.comp
          (measurable_centeredCutoffResponseOnCube M L n p q
            (originCube d (n : ℤ))).norm
    exact hmeas.aestronglyMeasurable
  have hcomp := hT.integrable_comp hg
  have heq : (fun omega =>
      |centeredCutoffResponseOnCube M L n p q R omega| ^ xi) = g ∘ T := by
    funext omega
    rw [centeredCutoffResponseOnCube_eq_originCube_translate
      M L n p q R hRscale omega]
    rfl
  rwa [← heq] at hcomp

/-- Deterministic response subadditivity on a finite triadic descendant
partition, specialized to the actual cutoff coefficient family. -/
theorem cutoffResponseOnCube_le_descendantsAverage {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (Q : TriadicCube d) (j : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffResponseOnCube M L p q Q omega ≤
      descendantsAverage Q j
        (fun R => cutoffResponseOnCube M L p q R omega) := by
  let F := aCutoffFamily M L omega
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hcell : ∀ i : Pcell.Cell,
      Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    intro i
    exact F.restrictsTo_of_subset (Pcell.cell_subset_parent i)
  have hsub :=
    (Ch02.responseSubadditivityAndScalingTheory
      (Ch02.cubeDomain Q) (F.coeffOn Q)).responseJ_subadditive
      Pcell (fun i : Pcell.Cell => F.coeffOn i.1) hcell p q
  simpa [cutoffResponseOnCube, F, Pcell] using hsub.trans_eq
    (Ch02.descendantsDomainPartition_weightedAverage Q j
      (fun R => cutoffResponseOnCube M L p q R omega))

/-- Source  before taking the `L^p` norm: the large-cube
response is bounded by the centered scale-`n` cell average plus its stationary
mean. -/
theorem cutoffResponseOnCube_le_centeredDescendantAverage_add_mean
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ) (hnm : n ≤ m)
    (p q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffResponseOnCube M L p q (originCube d (m : ℤ)) omega ≤
      (((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            centeredCutoffResponseOnCube M L n p q R omega +
        ∫ eta, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta
          ∂M.P.toMeasure := by
  let Q := originCube d (m : ℤ)
  let D := descendantsAtScale Q (n : ℤ)
  let mu0 := ∫ eta, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta
    ∂M.P.toMeasure
  have hscale : (n : ℤ) ≤ Q.scale := by
    change (n : ℤ) ≤ (m : ℤ)
    exact_mod_cast hnm
  have hdepth : Int.toNat (Q.scale - (n : ℤ)) = m - n := by
    simp only [Q, originCube]
    omega
  have hD : D = descendantsAtDepth Q (m - n) := by
    dsimp [D]
    rw [descendantsAtScale_eq_descendantsAtDepth Q hscale, hdepth]
  have hsub := cutoffResponseOnCube_le_descendantsAverage
    M L p q Q (m - n) omega
  have hDnonempty : D.Nonempty := descendantsAtScale_nonempty Q hscale
  have hcard : ((D.card : ℝ)) ≠ 0 := by
    exact_mod_cast hDnonempty.card_ne_zero
  calc
    cutoffResponseOnCube M L p q Q omega ≤
        ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
          cutoffResponseOnCube M L p q R omega := by
      simpa [descendantsAverage, ← hD] using hsub
    _ = ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
          centeredCutoffResponseOnCube M L n p q R omega + mu0 := by
      simp only [centeredCutoffResponseOnCube, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      field_simp
      dsimp [mu0]
      ring

/-! ## The restriction-local representative argument -/

/-- The fresh-shell palette has a factor-three separation at every natural
scale.  The older cutoff endpoint intentionally exposed only the weaker
factor-one consequence. -/
private theorem three_mul_cutoffRangeSeparated_of_cubeFreshShellColor_eq
    {d L : ℕ} {R S : TriadicCube d}
    (hRscale : R.scale = (L : ℤ)) (hSscale : S.scale = (L : ℤ))
    (hcolor : cubeFreshShellColor R = cubeFreshShellColor S) (hne : R ≠ S) :
    ∀ ⦃x y : Vec d⦄, x ∈ cubeSet R → y ∈ cubeSet S →
      3 * (Real.sqrt (d : ℝ) * (3 : ℝ) ^ L) ≤ Ch02.vecNorm (x - y) := by
  intro x y hx hy
  let k : ℤ := -((L : ℤ) + 1)
  let R' := Ch02.dilateCube k R
  let S' := Ch02.dilateCube k S
  have hR' : R'.scale = -1 := by simp [R', k, hRscale]
  have hS' : S'.scale = -1 := by simp [S', k, hSscale]
  have hcolor' : cubeFreshShellColor R' = cubeFreshShellColor S' := by
    simpa [R', S', cubeFreshShellColor, Ch02.dilateCube] using! hcolor
  have hne' : R' ≠ S' := fun h => hne (Ch02.dilateCube_injective k h)
  have hx' : Ch02.dilateVec k x ∈ cubeSet R' := by
    intro i
    let r : ℝ := Ch02.triadicDilationFactor k
    have hr : 0 < r := Ch02.triadicDilationFactor_pos k
    specialize hx i
    constructor
    · simpa [R', Ch02.dilateVec, Ch02.cubeScaleFactor_dilateCube,
        r, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hx.1 hr.le
    · simpa [R', Ch02.dilateVec, Ch02.cubeScaleFactor_dilateCube,
        r, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        mul_lt_mul_of_pos_left hx.2 hr
  have hy' : Ch02.dilateVec k y ∈ cubeSet S' := by
    intro i
    let r : ℝ := Ch02.triadicDilationFactor k
    have hr : 0 < r := Ch02.triadicDilationFactor_pos k
    specialize hy i
    constructor
    · simpa [S', Ch02.dilateVec, Ch02.cubeScaleFactor_dilateCube,
        r, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hy.1 hr.le
    · simpa [S', Ch02.dilateVec, Ch02.cubeScaleFactor_dilateCube,
        r, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        mul_lt_mul_of_pos_left hy.2 hr
  have hsep := potentialRangeSeparated_of_cubeFreshShellColor_eq_of_scale_neg_one
    hR' hS' hcolor' hne' hx' hy'
  have hnormEq (z : Vec d) : Homogenization.euclideanNorm z = Ch02.vecNorm z := by
    rw [← sq_eq_sq₀ (Homogenization.euclideanNorm_nonneg z) (Ch02.vecNorm_nonneg z),
      Homogenization.euclideanNorm_sq, Ch02.vecNorm_sq_eq_vecNormSq]
  have hscaled : Real.sqrt (d : ℝ) ≤
      Ch02.triadicDilationFactor k * Ch02.vecNorm (x - y) := by
    rw [← hnormEq]
    simpa [Ch02.dilateVec, ← smul_sub, Homogenization.euclideanNorm_smul,
      abs_of_pos (Ch02.triadicDilationFactor_pos k)] using hsep
  have hkEq : Ch02.triadicDilationFactor k = (3 : ℝ)⁻¹ * ((3 : ℝ) ^ L)⁻¹ := by
    dsimp only [k, Ch02.triadicDilationFactor]
    rw [zpow_neg, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hpow : 0 < (3 : ℝ) ^ L := by positivity
  rw [hkEq] at hscaled
  have hmul := mul_le_mul_of_nonneg_left hscaled
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hpow.le)
  have hcancel : (3 * (3 : ℝ) ^ L) *
      ((3 : ℝ)⁻¹ * ((3 : ℝ) ^ L)⁻¹ * Ch02.vecNorm (x - y)) =
      Ch02.vecNorm (x - y) := by
    field_simp [ne_of_gt hpow]
  rw [hcancel] at hmul
  nlinarith



private theorem cutoffRangeSeparated_thickenings_of_cubeFreshShellColor_eq
    {d L n : ℕ} [NeZero d] {R S : TriadicCube d}
    (hLn : L ≤ n) (hRscale : R.scale = (n : ℤ)) (hSscale : S.scale = (n : ℤ))
    (hcolor : cubeFreshShellColor R = cubeFreshShellColor S) (hne : R ≠ S) :
    ∀ ⦃x y : Vec d⦄,
      x ∈ Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R) →
      y ∈ Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet S) →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y) := by
  intro x y hx hy
  obtain ⟨x0, hx0, hxx0⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨y0, hy0, hyy0⟩ := Metric.mem_thickening_iff.mp hy
  have hbase := three_mul_cutoffRangeSeparated_of_cubeFreshShellColor_eq
    hRscale hSscale hcolor hne hx0 hy0
  have hnormEq (z : Vec d) : Homogenization.euclideanNorm z = Ch02.vecNorm z := by
    rw [← sq_eq_sq₀ (Homogenization.euclideanNorm_nonneg z) (Ch02.vecNorm_nonneg z),
      Homogenization.euclideanNorm_sq, Ch02.vecNorm_sq_eq_vecNormSq]
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hpertx : Ch02.vecNorm (x0 - x) <
      (d : ℝ) * responseRestrictionBridgeRadius d := by
    rw [← hnormEq]
    exact lt_of_le_of_lt (euclideanNorm_le_dimension_mul_norm (x0 - x)) (by
      rw [← dist_eq_norm]
      simpa [dist_comm] using mul_lt_mul_of_pos_left hxx0 hdpos)
  have hperty : Ch02.vecNorm (y - y0) <
      (d : ℝ) * responseRestrictionBridgeRadius d := by
    rw [← hnormEq]
    exact lt_of_le_of_lt (euclideanNorm_le_dimension_mul_norm (y - y0)) (by
      rw [← dist_eq_norm]
      exact mul_lt_mul_of_pos_left hyy0 hdpos)
  have htri : Ch02.vecNorm (x0 - y0) ≤
      Ch02.vecNorm (x0 - x) + Ch02.vecNorm (x - y) + Ch02.vecNorm (y - y0) := by
    rw [← hnormEq, ← hnormEq, ← hnormEq, ← hnormEq]
    have hid : x0 - y0 = (x0 - x) + (x - y) + (y - y0) := by abel
    rw [hid, Homogenization.euclideanNorm_eq_norm_ofVec,
      Homogenization.euclideanNorm_eq_norm_ofVec,
      Homogenization.euclideanNorm_eq_norm_ofVec,
      Homogenization.euclideanNorm_eq_norm_ofVec]
    simpa only [map_add] using!
      (norm_add₃_le (a := HilbertVec.ofVec (x0 - x))
        (b := HilbertVec.ofVec (x - y)) (c := HilbertVec.ofVec (y - y0)))
  have hpow : (3 : ℝ) ^ L ≤ (3 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hLn
  have hsqrt : 1 ≤ Real.sqrt (d : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ d from NeZero.one_le)
  have hnat : Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
  have heps : (d : ℝ) * responseRestrictionBridgeRadius d < 1 / 4 := by
    rw [responseRestrictionBridgeRadius, inv_eq_one_div, mul_one_div]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((d : ℝ) + 1))]
    nlinarith
  by_contra hgoal
  have hxy : Ch02.vecNorm (x - y) < Real.sqrt (d : ℝ) * (3 : ℝ) ^ L :=
    lt_of_not_ge hgoal
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hunitPow : 1 ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ n := by
    exact le_trans hsqrt (by nlinarith [Real.sqrt_nonneg (d : ℝ)])
  nlinarith

/-- Pull a Chapter-4 restriction-local representative of the raw response
back to the potential sample.  Equality with the totalized response is only
needed almost surely, exactly as in the verified Chapter-4 pattern. -/
theorem exists_cutoffResponseOnCube_thickenedLocal_ae_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    ∃ Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR
          (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
            (aCutoffRegCoeffField M L)) _ Y ∧
      cutoffResponseOnCube M L p q R =ᵐ[M.P.toMeasure] Y := by
  let P := aCutoffRestrictionLaw M L
  let A := aCutoffRegCoeffField M L
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet R (-p, q) with
    ⟨Y0, hY0local, hY0eq⟩
  let Z : RegCoeffField d → ℝ := fun a => Y0 a - vecDot p q
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := Z ∘ A
  refine ⟨Y, ?_, ?_⟩
  · have hZlocal : Ch04.IsRestrictionLocalRandomVariable
        (cubeSet R) (measurableSet_cubeSet R) Z := by
      simpa [Z] using hY0local.sub
        (Ch04.IsRestrictionLocalRandomVariable.const (cubeSet R)
          (measurableSet_cubeSet R) (vecDot p q))
    have hcomp : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((RestrictionSigmaR (cubeSet R) (measurableSet_cubeSet R)).comap A) _ Y := by
      exact hZlocal.comp (Measurable.of_comap_le le_rfl)
    exact hcomp.mono
      (comap_restrictionSigmaR_le_comap_localSigmaR_thickening A
        (fun omega i j => continuous_aCutoffRegCoeffField_entry_for_response
          M L omega i j)
        (cubeSet R) (measurableSet_cubeSet R) (responseRestrictionBridgeRadius d)
        (responseRestrictionBridgeRadius_pos d)) le_rfl
  · have hresp :
        (fun a : RegCoeffField d => ResponseJ (cubeSet R) p q a.toFun) =ᵐ[P] Z := by
      exact (hP.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_ae R p q).trans
        (hY0eq.sub Filter.EventuallyEq.rfl)
    have hpull :
        (fun omega => ResponseJ (cubeSet R) p q (A omega).toFun) =ᵐ[M.P.toMeasure] Y := by
      exact ae_eq_comp (measurable_aCutoffRegCoeffField M L).aemeasurable
        (by simpa [P, aCutoffRestrictionLaw_eq_map, Y, A] using hresp)
    filter_upwards [hpull] with omega homega
    calc
      cutoffResponseOnCube M L p q R omega =
          ResponseJ (cubeSet R) p q (A omega).toFun := by
        unfold cutoffResponseOnCube
        change ResponseJ (openCubeSet R) p q (A omega).toFun =
          ResponseJ (cubeSet R) p q (A omega).toFun
        exact (responseJ_cubeSet_eq_openCubeSet_of_triadicCube R p q
          (A omega).toFun).symm
      _ = Y omega := homega

/-- Centering preserves both thickened locality and the a.e. identification. -/
private theorem exists_centeredCutoffResponseOnCube_thickenedLocal_ae_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    ∃ Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR
          (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
            (aCutoffRegCoeffField M L)) _ Y ∧
      centeredCutoffResponseOnCube M L n p q R =ᵐ[M.P.toMeasure] Y := by
  rcases exists_cutoffResponseOnCube_thickenedLocal_ae_eq M L p q R with
    ⟨Y0, hY0, hY0eq⟩
  let c := ∫ eta, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta
    ∂M.P.toMeasure
  refine ⟨fun omega => Y0 omega - c, hY0.sub measurable_const, ?_⟩
  filter_upwards [hY0eq] with omega homega
  simp only [centeredCutoffResponseOnCube, c, homega]

private theorem measurableSet_biInter_cutoffLocalSigma_biUnion
    {d : ℕ} {ι : Type*} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {U : ι → Set (Vec d)} {f : ι → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d)} {s : Finset ι}
    (hf : ∀ i ∈ s,
      @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialSample d)
        ((LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L)) (f i)) :
    @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialSample d)
      ((LocalSigmaR (⋃ i ∈ s, U i)).comap (aCutoffRegCoeffField M L))
      (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialSample d)
            ((LocalSigmaR (⋃ j ∈ insert i s, U j)).comap
              (aCutoffRegCoeffField M L)) (f i) :=
        (MeasurableSpace.comap_mono (localSigmaR_mono hsubset_i))
          (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialSample d)
            ((LocalSigmaR (⋃ j ∈ insert i s, U j)).comap
              (aCutoffRegCoeffField M L)) (⋂ j ∈ s, f j) :=
        (MeasurableSpace.comap_mono (localSigmaR_mono hsubset_s))
          (⋂ j ∈ s, f j) (ih fun j hj => hf j (by simp [hj]))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

private theorem cutoffRangeSeparated_biUnion_right {d : ℕ} {ι : Type*}
    {U : Set (Vec d)} {V : ι → Set (Vec d)} {s : Finset ι} {r : ℝ}
    (hsep : ∀ j ∈ s, ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V j →
      r ≤ Ch02.vecNorm (x - y)) :
    ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ ⋃ j ∈ s, V j →
      r ≤ Ch02.vecNorm (x - y) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨j, hy⟩
  rcases hy with ⟨hj, hy⟩
  exact hsep j hj hx hy

/-- A pairwise cutoff-range-separated family of local cutoff sigma fields is
mutually independent.  This is the strengthening of the pairwise independence result
which the Rosenthal endpoint genuinely needs. -/
theorem iIndep_cutoffLocalSigma_of_rangeSeparated {d : ℕ} [NeZero d]
    {ι : Type*} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {U : ι → Set (Vec d)} (hU : ∀ i, IsOpen (U i))
    (hsep : Pairwise fun i j =>
      ∀ ⦃x y : Vec d⦄, x ∈ U i → y ∈ U j →
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y)) :
    iIndep (fun i => (LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L))
      M.P.toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsep_union : ∀ ⦃x y : Vec d⦄, x ∈ U i → y ∈ ⋃ j ∈ s, U j →
          Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y) := by
        apply cutoffRangeSeparated_biUnion_right
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_open : IsOpen (⋃ j ∈ s, U j) :=
        isOpen_biUnion fun j _ => hU j
      have hs_meas :
          @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialSample d)
            ((LocalSigmaR (⋃ j ∈ s, U j)).comap (aCutoffRegCoeffField M L))
            (⋂ j ∈ s, f j) :=
        measurableSet_biInter_cutoffLocalSigma_biUnion M L
          (U := U) (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          M.P.toMeasure (f i ∩ ⋂ j ∈ s, f j) =
            M.P.toMeasure (f i) * M.P.toMeasure (⋂ j ∈ s, f j) := by
        exact (Indep_iff
          ((LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L))
          ((LocalSigmaR (⋃ j ∈ s, U j)).comap (aCutoffRegCoeffField M L))
          M.P.toMeasure).1
            (indep_aCutoffRegCoeffField_local_of_separation M L
              (U i) (⋃ j ∈ s, U j) (hU i) hs_open hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        M.P.toMeasure (⋂ j ∈ insert i s, f j) =
            M.P.toMeasure (f i ∩ ⋂ j ∈ s, f j) := by simp
        _ = M.P.toMeasure (f i) * M.P.toMeasure (⋂ j ∈ s, f j) := h_inter
        _ = M.P.toMeasure (f i) * ∏ j ∈ s, M.P.toMeasure (f j) := by
          rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, M.P.toMeasure (f j) := by
          simp [Finset.prod_insert, hi]

/-- Local scalar observables of a range-separated cutoff family are mutually
independent. -/
theorem iIndepFun_cutoffLocal_of_rangeSeparated {d : ℕ} [NeZero d]
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {U : ι → Set (Vec d)} {X : ∀ i, _root_.SubdiffusiveProcess.Model.PotentialSample d → β i}
    (hU : ∀ i, IsOpen (U i))
    (hsep : Pairwise fun i j =>
      ∀ ⦃x y : Vec d⦄, x ∈ U i → y ∈ U j →
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y))
    (hX : ∀ i,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (β i)
        ((LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L)) _ (X i)) :
    iIndepFun X M.P.toMeasure := by
  rw [iIndepFun_iff_iIndep, iIndep_iff]
  intro s f hf
  exact (iIndep_iff
    (fun i => (LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L))
    M.P.toMeasure).1
      (iIndep_cutoffLocalSigma_of_rangeSeparated M L hU hsep) s
      (fun i hi => (Measurable.comap_le (hX i)) (f i) (hf i hi))

/-- The fresh-shell coloring gives mutual independence for cutoff-local
observables on scale-`n` descendants whenever the cutoff scale is at most
`n`. -/
theorem iIndepFun_cutoff_descendants_colorClass {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (c : FreshShellColor d)
    (X : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (hX : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _
        (X R)) :
    iIndepFun
      (fun R : {R : TriadicCube d //
          R ∈ (descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).filter
            (fun S => cubeFreshShellColor S = c)} => X R.1)
      M.P.toMeasure := by
  let I := {R : TriadicCube d //
    R ∈ (descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).filter
      (fun S => cubeFreshShellColor S = c)}
  apply iIndepFun_cutoffLocal_of_rangeSeparated M L
    (U := fun R : I => openCubeSet R.1)
  · intro R
    exact isOpen_openCubeSet R.1
  · intro R S hRS x y hx hy
    have hR := Finset.mem_filter.mp R.2
    have hS := Finset.mem_filter.mp S.2
    have hsep_n := cutoffRangeSeparated_of_cubeFreshShellColor_eq_of_scale
      (L := n)
      (scale_eq_of_mem_descendantsAtScale hR.1)
      (scale_eq_of_mem_descendantsAtScale hS.1)
      (hR.2.trans hS.2.symm)
      (fun h => hRS (Subtype.ext h)) hx hy
    have hpow : (3 : ℝ) ^ L ≤ (3 : ℝ) ^ n :=
      pow_le_pow_right₀ (by norm_num) hLn
    exact (mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)).trans hsep_n
  · intro R
    exact hX R.1 (Finset.mem_of_mem_filter R.1 R.2)

/-- A.e.-local version of the color-class independence theorem.  The chosen
representatives are independent on positively thickened cube sets; independence
then transports back to the raw observables through `iIndepFun.congr`. -/
theorem iIndepFun_cutoff_descendants_colorClass_of_ae_thickenedLocal
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (c : FreshShellColor d)
    (X : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (hX : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      ∃ Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
        @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
          ((LocalSigmaR
            (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
              (aCutoffRegCoeffField M L)) _ Y ∧
        X R =ᵐ[M.P.toMeasure] Y) :
    iIndepFun
      (fun R : {R : TriadicCube d //
          R ∈ (descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).filter
            (fun S => cubeFreshShellColor S = c)} => X R.1)
      M.P.toMeasure := by
  classical
  let I := {R : TriadicCube d //
    R ∈ (descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).filter
      (fun S => cubeFreshShellColor S = c)}
  let Y : I → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun R =>
    Classical.choose (hX R.1 (Finset.mem_of_mem_filter R.1 R.2))
  have hYlocal : ∀ R : I,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR
          (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R.1))).comap
            (aCutoffRegCoeffField M L)) _ (Y R) := by
    intro R
    exact (Classical.choose_spec
      (hX R.1 (Finset.mem_of_mem_filter R.1 R.2))).1
  have hYindep : iIndepFun Y M.P.toMeasure := by
    apply iIndepFun_cutoffLocal_of_rangeSeparated M L
      (U := fun R : I =>
        Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R.1))
    · intro R
      exact Metric.isOpen_thickening
    · intro R S hRS x y hx hy
      have hR := Finset.mem_filter.mp R.2
      have hS := Finset.mem_filter.mp S.2
      exact cutoffRangeSeparated_thickenings_of_cubeFreshShellColor_eq hLn
        (scale_eq_of_mem_descendantsAtScale hR.1)
        (scale_eq_of_mem_descendantsAtScale hS.1)
        (hR.2.trans hS.2.symm) (fun h => hRS (Subtype.ext h)) hx hy
    · exact hYlocal
  exact hYindep.congr fun R =>
    (Classical.choose_spec
      (hX R.1 (Finset.mem_of_mem_filter R.1 R.2))).2.symm

/-! ## Rosenthal on a finite coloring -/

/-- Real-exponent Rosenthal, applied to every color class and recombined by
Minkowski.  The right side deliberately retains the two paper channels: the
`p`-moment/max channel and the quadratic/variance channel. -/
theorem integral_abs_finsetSum_rpow_rpow_inv_le_colored_rosenthal
    {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq κ]
    (s : Finset ι) (color : ι → κ)
    {X : ι → Ω → ℝ} {p : ℝ} (hp : 2 ≤ p)
    (hindep : ∀ c ∈ s.image color,
      iIndepFun
        (fun i : {i : ι // i ∈ s.filter (fun j => color j = c)} => X i.1) μ)
    (hXmeas : ∀ i ∈ s, Measurable (X i))
    (hXp : ∀ i ∈ s, Integrable (fun omega => |X i omega| ^ p) μ)
    (hXmean : ∀ i ∈ s, ∫ omega, X i omega ∂μ = 0) :
    (∫ omega, |∑ i ∈ s, X i omega| ^ p ∂μ) ^ p⁻¹ ≤
      ∑ c ∈ s.image color,
        (2 * p *
            (∑ i ∈ s.filter (fun j => color j = c),
              ∫ omega, |X i omega| ^ p ∂μ) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt
              (∑ i ∈ s.filter (fun j => color j = c), moment (X i) 2 μ))) := by
  let colors := s.image color
  let classSum : κ → Ω → ℝ := fun c omega =>
    ∑ i ∈ s.filter (fun j => color j = c), X i omega
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hclassMeas : ∀ c ∈ colors, Measurable (classSum c) := by
    intro c _hc
    exact Finset.measurable_sum _ fun i hi =>
      hXmeas i (Finset.mem_of_mem_filter i hi)
  have hclassInt : ∀ c ∈ colors,
      Integrable (fun omega => |classSum c omega| ^ p) μ := by
    intro c _hc
    exact integrable_abs_finsetSum_rpow hp_one
      (fun i hi => hXmeas i (Finset.mem_of_mem_filter i hi))
      (fun i hi => hXp i (Finset.mem_of_mem_filter i hi))
  have hclass : ∀ c ∈ colors,
      (∫ omega, |classSum c omega| ^ p ∂μ) ^ p⁻¹ ≤
        2 * p *
            (∑ i ∈ s.filter (fun j => color j = c),
              ∫ omega, |X i omega| ^ p ∂μ) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt
              (∑ i ∈ s.filter (fun j => color j = c), moment (X i) 2 μ)) := by
    intro c hc
    have ht : (s.filter (fun j => color j = c)).Nonempty := by
      obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hc
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hic⟩⟩
    let t := s.filter (fun j => color j = c)
    have hraw :=
      integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
        (μ := μ) (X := fun i : {i : ι // i ∈ t} => X i.1)
        (s := t.attach) (Finset.attach_nonempty_iff.mpr ht) hp
        (by simpa [t] using hindep c hc)
        (fun i => hXmeas i.1 (Finset.mem_of_mem_filter i.1 i.2))
        (fun i _ => hXp i.1 (Finset.mem_of_mem_filter i.1 i.2))
        (fun i _ => hXmean i.1 (Finset.mem_of_mem_filter i.1 i.2))
    have hsumX (omega : Ω) :
        ∑ i ∈ t.attach, X i.1 omega = ∑ i ∈ t, X i omega :=
      Finset.sum_attach t fun i => X i omega
    have hsumP :
        ∑ i ∈ t.attach, ∫ omega, |X i.1 omega| ^ p ∂μ =
          ∑ i ∈ t, ∫ omega, |X i omega| ^ p ∂μ :=
      Finset.sum_attach t fun i => ∫ omega, |X i omega| ^ p ∂μ
    have hsumTwo :
        ∑ i ∈ t.attach, moment (X i.1) 2 μ =
          ∑ i ∈ t, moment (X i) 2 μ :=
      Finset.sum_attach t fun i => moment (X i) 2 μ
    simp_rw [hsumX] at hraw
    rw [hsumP, hsumTwo] at hraw
    simpa only [classSum, t] using hraw
  have htriangle := integral_abs_finsetSum_rpow_rpow_inv_le_sum
    (μ := μ) hp_one hclassMeas hclassInt
  have hpartition : (fun omega => ∑ c ∈ colors, classSum c omega) =
      (fun omega => ∑ i ∈ s, X i omega) := by
    funext omega
    exact Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem color hi) (fun i => X i omega)
  have htriangle' :
      (∫ omega, |∑ i ∈ s, X i omega| ^ p ∂μ) ^ p⁻¹ ≤
        ∑ c ∈ colors, (∫ omega, |classSum c omega| ^ p ∂μ) ^ p⁻¹ := by
    simpa only [congrFun hpartition] using htriangle
  exact htriangle'.trans (Finset.sum_le_sum fun c hc => hclass c hc)

/-- Uniform-moment specialization of the colored Rosenthal bound.  The
palette-size parameter is real-valued so a caller may use either the exact
number of used colors or a dimension-only upper bound. -/
theorem integral_abs_finsetSum_rpow_rpow_inv_le_colored_rosenthal_uniform
    {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq κ]
    (s : Finset ι) (color : ι → κ)
    {X : ι → Ω → ℝ} {p K colorCount : ℝ}
    (hp : 2 ≤ p) (hK : 0 ≤ K)
    (hcolorCount : ((s.image color).card : ℝ) ≤ colorCount)
    (hindep : ∀ c ∈ s.image color,
      iIndepFun
        (fun i : {i : ι // i ∈ s.filter (fun j => color j = c)} => X i.1) μ)
    (hXmeas : ∀ i ∈ s, Measurable (X i))
    (hXp : ∀ i ∈ s, Integrable (fun omega => |X i omega| ^ p) μ)
    (hXmean : ∀ i ∈ s, ∫ omega, X i omega ∂μ = 0)
    (hXroot : ∀ i ∈ s,
      (∫ omega, |X i omega| ^ p ∂μ) ^ p⁻¹ ≤ K) :
    (∫ omega, |∑ i ∈ s, X i omega| ^ p ∂μ) ^ p⁻¹ ≤
      2 * p * (colorCount ^ (1 - p⁻¹) * (s.card : ℝ) ^ p⁻¹ * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * (Real.sqrt colorCount * Real.sqrt (s.card : ℝ) * K)) := by
  let colors := s.image color
  let classSet : κ → Finset ι := fun c => s.filter (fun i => color i = c)
  let classSum : κ → Ω → ℝ := fun c omega => ∑ i ∈ classSet c, X i omega
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hclassMeas : ∀ c ∈ colors, Measurable (classSum c) := by
    intro c _hc
    exact Finset.measurable_sum _ fun i hi =>
      hXmeas i (Finset.mem_of_mem_filter i hi)
  have hclassInt : ∀ c ∈ colors,
      Integrable (fun omega => |classSum c omega| ^ p) μ := by
    intro c _hc
    exact integrable_abs_finsetSum_rpow hp_one
      (fun i hi => hXmeas i (Finset.mem_of_mem_filter i hi))
      (fun i hi => hXp i (Finset.mem_of_mem_filter i hi))
  have hclass : ∀ c ∈ colors,
      (∫ omega, |classSum c omega| ^ p ∂μ) ^ p⁻¹ ≤
        2 * p * ((classSet c).card : ℝ) ^ p⁻¹ * K +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * (Real.sqrt ((classSet c).card : ℝ) * K)) := by
    intro c hc
    have ht : (classSet c).Nonempty := by
      obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hc
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hic⟩⟩
    let t := classSet c
    let Y : {i : ι // i ∈ t} → Ω → ℝ := fun i => X i.1
    have hraw :=
      integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
        (μ := μ) (X := Y) (s := t.attach) (p := p) (K := K)
        (Finset.attach_nonempty_iff.mpr ht) hp hK
        (by simpa [Y, t, classSet] using hindep c hc)
        (fun i => hXmeas i.1 (Finset.mem_of_mem_filter i.1 i.2))
        (fun i _ => hXp i.1 (Finset.mem_of_mem_filter i.1 i.2))
        (fun i _ => hXmean i.1 (Finset.mem_of_mem_filter i.1 i.2))
        (fun i _ => hXroot i.1 (Finset.mem_of_mem_filter i.1 i.2))
    have hsumY : (fun omega => ∑ i ∈ t.attach, Y i omega) =
        (fun omega => ∑ i ∈ t, X i omega) := by
      funext omega
      exact Finset.sum_attach t fun i => X i omega
    change (∫ omega, |(fun omega => ∑ i ∈ t.attach, Y i omega) omega| ^ p ∂μ) ^ p⁻¹ ≤ _
      at hraw
    rw [hsumY] at hraw
    simpa [classSum, classSet, t, mul_assoc] using hraw
  have htriangle := integral_abs_finsetSum_rpow_rpow_inv_le_sum
    (μ := μ) hp_one hclassMeas hclassInt
  have hpartition : (fun omega => ∑ c ∈ colors, classSum c omega) =
      (fun omega => ∑ i ∈ s, X i omega) := by
    funext omega
    exact Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem color hi) (fun i => X i omega)
  have hsum_card :
      ∑ c ∈ colors, ((classSet c).card : ℝ) = (s.card : ℝ) := by
    have hnat : s.card = ∑ c ∈ s.image color, (s.filter (fun i => color i = c)).card :=
      Finset.card_eq_sum_card_image color s
    exact_mod_cast hnat.symm
  have hpinv_le_one : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp_one
  have hexp_nonneg : 0 ≤ 1 - p⁻¹ := by linarith
  have hsum_rpow :
      ∑ c ∈ colors, ((classSet c).card : ℝ) ^ p⁻¹ ≤
        colorCount ^ (1 - p⁻¹) * (s.card : ℝ) ^ p⁻¹ := by
    have hbase := sum_rpow_inv_le_card_rpow_mul_rpow_sum
      (s := colors) (p := p) (f := fun c => ((classSet c).card : ℝ))
      hp_one (fun c hc => by positivity)
    rw [hsum_card] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) hcolorCount hexp_nonneg) (by positivity))
  have hsqrt_sum :
      ∑ c ∈ colors, Real.sqrt ((classSet c).card : ℝ) ≤
        Real.sqrt colorCount * Real.sqrt (s.card : ℝ) := by
    have hbase :
        ∑ c ∈ colors, Real.sqrt ((classSet c).card : ℝ) ≤
          Real.sqrt (colors.card : ℝ) * Real.sqrt (s.card : ℝ) := by
      simpa [hsum_card] using
        (Real.sum_sqrt_mul_sqrt_le
          (s := colors) (f := fun _ => (1 : ℝ))
          (g := fun c => ((classSet c).card : ℝ))
          (hf := fun c => by positivity) (hg := fun c => by positivity))
    exact hbase.trans (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hcolorCount) (Real.sqrt_nonneg _))
  have hRB : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst,
      Homogenization.IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have htriangle' :
      (∫ omega, |∑ i ∈ s, X i omega| ^ p ∂μ) ^ p⁻¹ ≤
        ∑ c ∈ colors, (∫ omega, |classSum c omega| ^ p ∂μ) ^ p⁻¹ := by
    simpa only [congrFun hpartition] using htriangle
  calc
    (∫ omega, |∑ i ∈ s, X i omega| ^ p ∂μ) ^ p⁻¹ ≤
        ∑ c ∈ colors, (∫ omega, |classSum c omega| ^ p ∂μ) ^ p⁻¹ := htriangle'
    _ ≤ ∑ c ∈ colors,
        (2 * p * ((classSet c).card : ℝ) ^ p⁻¹ * K +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * (Real.sqrt ((classSet c).card : ℝ) * K))) :=
      Finset.sum_le_sum fun c hc => hclass c hc
    _ = (2 * p * K) * ∑ c ∈ colors, ((classSet c).card : ℝ) ^ p⁻¹ +
        (4 * rosenthalBennettIntegralConst * Real.sqrt p * K) *
          ∑ c ∈ colors, Real.sqrt ((classSet c).card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro c hc <;> ring
    _ ≤ (2 * p * K) *
          (colorCount ^ (1 - p⁻¹) * (s.card : ℝ) ^ p⁻¹) +
        (4 * rosenthalBennettIntegralConst * Real.sqrt p * K) *
          (Real.sqrt colorCount * Real.sqrt (s.card : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsum_rpow (by positivity))
        (mul_le_mul_of_nonneg_left hsqrt_sum (by positivity))
    _ = 2 * p * (colorCount ^ (1 - p⁻¹) * (s.card : ℝ) ^ p⁻¹ * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * (Real.sqrt colorCount * Real.sqrt (s.card : ℝ) * K)) := by
      ring

/-- Pull a nonnegative deterministic scalar out of the real `L^p` root used by
the Rosenthal endpoint. -/
theorem integral_abs_const_mul_rpow_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) :
    (∫ omega, |c * f omega| ^ p ∂μ) ^ p⁻¹ =
      c * (∫ omega, |f omega| ^ p ∂μ) ^ p⁻¹ := by
  have hp0 : p ≠ 0 := hp.ne'
  have hInt : 0 ≤ ∫ omega, |f omega| ^ p ∂μ :=
    integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  rw [show (∫ omega, |c * f omega| ^ p ∂μ) =
      c ^ p * ∫ omega, |f omega| ^ p ∂μ by
        simp_rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
        exact integral_const_mul _ _]
  rw [Real.mul_rpow (Real.rpow_nonneg hc _) hInt]
  rw [← Real.rpow_mul hc, mul_inv_cancel₀ hp0, Real.rpow_one]

/-! ## GMC descendant specialization -/

/-- Uniform colored Rosenthal for cutoff-local observables on all scale-`n`
descendants of the scale-`m` origin cube.  The only analytic input is the
single-cell `L^p` budget `K`; locality, the palette, and mutual independence
are discharged by the finite-cutoff model. -/
theorem integral_abs_cutoff_descendantSum_rpow_rpow_inv_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (X : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    {p K : ℝ} (hp : 2 ≤ p) (hK : 0 ≤ K)
    (hXlocal : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _
        (X R))
    (hXp : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      Integrable (fun omega => |X R omega| ^ p) M.P.toMeasure)
    (hXmean : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      ∫ omega, X R omega ∂M.P.toMeasure = 0)
    (hXroot : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      (∫ omega, |X R omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤ K) :
    (∫ omega,
        |∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
          X R omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      2 * p *
          ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - p⁻¹)) *
            ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) ^ p⁻¹ * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p *
            (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
              Real.sqrt
                ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) * K)) := by
  let s := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
  apply integral_abs_finsetSum_rpow_rpow_inv_le_colored_rosenthal_uniform
    s cubeFreshShellColor hp hK
  · exact_mod_cast card_image_cubeFreshShellColor_le s
  · intro c _hc
    exact iIndepFun_cutoff_descendants_colorClass M L n m hLn c X hXlocal
  · intro R hR
    exact (hXlocal R hR).mono
      ((MeasurableSpace.comap_mono (LocalSigmaR_le (openCubeSet R))).trans
        (measurable_aCutoffRegCoeffField M L).comap_le) le_rfl
  · exact hXp
  · exact hXmean
  · exact hXroot

/-- Averaged version of `integral_abs_cutoff_descendantSum_rpow_rpow_inv_le`.
This is the direct carrier for source; its two terms become
the printed `3^{-d(m-n)(p-1)/p}` and `3^{-d(m-n)/2}` after the descendant-card
identity is rewritten. -/
theorem integral_abs_cutoff_descendantAverage_rpow_rpow_inv_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (X : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    {p K : ℝ} (hp : 2 ≤ p) (hK : 0 ≤ K)
    (hXlocal : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _
        (X R))
    (hXp : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      Integrable (fun omega => |X R omega| ^ p) M.P.toMeasure)
    (hXmean : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      ∫ omega, X R omega ∂M.P.toMeasure = 0)
    (hXroot : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      (∫ omega, |X R omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤ K) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            X R omega| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      (((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
        (2 * p *
            ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - p⁻¹)) *
              ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) ^ p⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p *
              (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                Real.sqrt
                  ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) * K))) := by
  let s := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
  let A := 2 * p *
      ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - p⁻¹)) *
        (s.card : ℝ) ^ p⁻¹ * K) +
    4 * rosenthalBennettIntegralConst *
      (Real.sqrt p *
        (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
          Real.sqrt (s.card : ℝ) * K))
  have hsum := integral_abs_cutoff_descendantSum_rpow_rpow_inv_le
    M L n m hLn X hp hK hXlocal hXp hXmean hXroot
  have hscale := integral_abs_const_mul_rpow_rpow_inv
    (μ := M.P.toMeasure) (fun omega => ∑ R ∈ s, X R omega)
    (p := p) (c := ((s.card : ℝ)⁻¹)) (by linarith) (by positivity)
  rw [hscale]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Response-specific Step-4 endpoint.  Stationarity, centering,
measurability, integrability, coloring, and Rosenthal are all discharged.  The
single locality premise records the exact public-API boundary between the raw
variational response and the cutoff integral-local sigma field; the response
moment budget remains explicit, as required by the payload argument. -/
theorem integral_abs_centeredCutoffResponseAverage_rpow_rpow_inv_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (p q : Vec d) {xi K : ℝ}
    (hxi : 2 ≤ xi) (hK : 0 ≤ K)
    (hlocal : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _
        (centeredCutoffResponseOnCube M L n p q R))
    (hmoment : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      Integrable
        (fun omega => |centeredCutoffResponseOnCube M L n p q R omega| ^ xi)
        M.P.toMeasure)
    (hroot : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      (∫ omega, |centeredCutoffResponseOnCube M L n p q R omega| ^ xi
          ∂M.P.toMeasure) ^ xi⁻¹ ≤ K) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            centeredCutoffResponseOnCube M L n p q R omega| ^ xi
          ∂M.P.toMeasure) ^ xi⁻¹ ≤
      (((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
        (2 * xi *
            ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - xi⁻¹)) *
              ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) ^ xi⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt xi *
              (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                Real.sqrt
                  ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) * K))) := by
  apply integral_abs_cutoff_descendantAverage_rpow_rpow_inv_le
    M L n m hLn (centeredCutoffResponseOnCube M L n p q) hxi hK hlocal hmoment
  · intro R hR
    exact integral_centeredCutoffResponseOnCube_eq_zero M L n p q R
      (scale_eq_of_mem_descendantsAtScale hR)
  · exact hroot

/-- Stationary one-cell budget form of the response Rosenthal endpoint.  This
is the form consumed by the Section 4 payload: the `xi`-moment is assumed only
on the centered origin cell and transported to every translated cell here. -/
theorem integral_abs_centeredCutoffResponseAverage_rpow_rpow_inv_le_of_origin
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (p q : Vec d) {xi K : ℝ}
    (hxi : 2 ≤ xi) (hK : 0 ≤ K)
    (hlocal : ∀ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _
        (centeredCutoffResponseOnCube M L n p q R))
    (hmoment : Integrable
      (fun omega =>
        |centeredCutoffResponseOnCube M L n p q
          (originCube d (n : ℤ)) omega| ^ xi) M.P.toMeasure)
    (hroot :
      (∫ omega,
          |centeredCutoffResponseOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤ K) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            centeredCutoffResponseOnCube M L n p q R omega| ^ xi
          ∂M.P.toMeasure) ^ xi⁻¹ ≤
      (((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
        (2 * xi *
            ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - xi⁻¹)) *
              ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) ^ xi⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt xi *
              (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                Real.sqrt
                  ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) * K))) := by
  apply integral_abs_centeredCutoffResponseAverage_rpow_rpow_inv_le
    M L n m hLn p q hxi hK hlocal
  · intro R hR
    exact (integrable_abs_centeredCutoffResponseOnCube_rpow_iff_originCube
      M L n p q R (scale_eq_of_mem_descendantsAtScale hR) xi
        (le_trans (by norm_num) hxi)).2 hmoment
  · intro R hR
    rw [integral_abs_centeredCutoffResponseOnCube_rpow_eq_originCube
      M L n p q R (scale_eq_of_mem_descendantsAtScale hR) xi
        (le_trans (by norm_num) hxi)]
    exact hroot

/-- A.e.-representative version of the response Rosenthal endpoint.  This is
the honest totalized-response surface: no exact unthickened locality premise
is exposed to the consumer. -/
theorem integral_abs_centeredCutoffResponseAverage_rpow_rpow_inv_le_of_origin_ae_local
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (p q : Vec d) {xi K : ℝ}
    (hxi : 2 ≤ xi) (hK : 0 ≤ K)
    (hmoment : Integrable
      (fun omega =>
        |centeredCutoffResponseOnCube M L n p q
          (originCube d (n : ℤ)) omega| ^ xi) M.P.toMeasure)
    (hroot :
      (∫ omega,
          |centeredCutoffResponseOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤ K) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            centeredCutoffResponseOnCube M L n p q R omega| ^ xi
          ∂M.P.toMeasure) ^ xi⁻¹ ≤
      (((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
        (2 * xi *
            ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - xi⁻¹)) *
              ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) ^ xi⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt xi *
              (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                Real.sqrt
                  ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) * K))) := by
  let s := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
  let X := centeredCutoffResponseOnCube M L n p q
  let A := 2 * xi *
      ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - xi⁻¹)) *
        (s.card : ℝ) ^ xi⁻¹ * K) +
    4 * rosenthalBennettIntegralConst *
      (Real.sqrt xi *
        (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
          Real.sqrt (s.card : ℝ) * K))
  have hmomentCell : ∀ R ∈ s,
      Integrable (fun omega => |X R omega| ^ xi) M.P.toMeasure := by
    intro R hR
    exact (integrable_abs_centeredCutoffResponseOnCube_rpow_iff_originCube
      M L n p q R (scale_eq_of_mem_descendantsAtScale hR) xi
        (le_trans (by norm_num) hxi)).2 hmoment
  have hrootCell : ∀ R ∈ s,
      (∫ omega, |X R omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤ K := by
    intro R hR
    rw [integral_abs_centeredCutoffResponseOnCube_rpow_eq_originCube
      M L n p q R (scale_eq_of_mem_descendantsAtScale hR) xi
        (le_trans (by norm_num) hxi)]
    exact hroot
  have hsum :
      (∫ omega, |∑ R ∈ s, X R omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤ A := by
    apply integral_abs_finsetSum_rpow_rpow_inv_le_colored_rosenthal_uniform
      s cubeFreshShellColor hxi hK
    · exact_mod_cast card_image_cubeFreshShellColor_le s
    · intro c _hc
      apply iIndepFun_cutoff_descendants_colorClass_of_ae_thickenedLocal
        M L n m hLn c X
      intro R _hR
      exact exists_centeredCutoffResponseOnCube_thickenedLocal_ae_eq M L n p q R
    · intro R _hR
      exact measurable_centeredCutoffResponseOnCube M L n p q R
    · exact hmomentCell
    · intro R hR
      exact integral_centeredCutoffResponseOnCube_eq_zero M L n p q R
        (scale_eq_of_mem_descendantsAtScale hR)
    · exact hrootCell
  have hscale := integral_abs_const_mul_rpow_rpow_inv
    (μ := M.P.toMeasure) (fun omega => ∑ R ∈ s, X R omega)
    (p := xi) (c := ((s.card : ℝ)⁻¹)) (by linarith) (by positivity)
  rw [hscale]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem aux_dedup_d072_responseRosenthal_rhs_le_dimensional_sqrt_card
    {d : ℕ} {xi K N : ℝ} (hxi : 2 ≤ xi) (hK : 0 ≤ K) (hN : 1 ≤ N) :
    N⁻¹ *
        (2 * xi *
            ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - xi⁻¹)) *
              N ^ xi⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt xi *
              (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                Real.sqrt N * K))) ≤
      (2 * ((freshShellColorPeriod d ^ d : ℕ) : ℝ) +
          4 * rosenthalBennettIntegralConst *
            Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ)) *
        xi * K * (Real.sqrt N)⁻¹ := by
  let B : ℝ := ((freshShellColorPeriod d ^ d : ℕ) : ℝ)
  have hperiod : 0 < freshShellColorPeriod d := freshShellColorPeriod_pos d
  have hB : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero d hperiod.ne'))
  have hxi0 : 0 < xi := by linarith
  have hinv : xi⁻¹ ≤ 1 / 2 := by
    simpa using (inv_le_inv₀ hxi0 (by norm_num : (0 : ℝ) < 2)).2 hxi
  have hexp : 1 - xi⁻¹ ≤ 1 := by
    have : 0 ≤ xi⁻¹ := inv_nonneg.mpr hxi0.le
    linarith
  have hBpow : B ^ (1 - xi⁻¹) ≤ B := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hB hexp)
  have hNpow : N ^ xi⁻¹ ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN (by simpa using hinv)
  have hsxi : Real.sqrt xi ≤ xi := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hxi0.le
    · nlinarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hN)
  have hRB : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst,
      Homogenization.IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hmain :
      2 * xi * (B ^ (1 - xi⁻¹) * N ^ xi⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt xi * (Real.sqrt B * Real.sqrt N * K)) ≤
        (2 * B + 4 * rosenthalBennettIntegralConst * Real.sqrt B) * xi * K *
          Real.sqrt N := by
    calc
      _ ≤ 2 * xi * (B * Real.sqrt N * K) +
          4 * rosenthalBennettIntegralConst *
            (xi * (Real.sqrt B * Real.sqrt N * K)) := by
        gcongr
      _ = _ := by ring
  change N⁻¹ *
      (2 * xi * (B ^ (1 - xi⁻¹) * N ^ xi⁻¹ * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt xi * (Real.sqrt B * Real.sqrt N * K))) ≤ _
  calc
    _ ≤ N⁻¹ * ((2 * B + 4 * rosenthalBennettIntegralConst * Real.sqrt B) *
        xi * K * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr (le_trans (by norm_num) hN))
    _ = (2 * B + 4 * rosenthalBennettIntegralConst * Real.sqrt B) *
        xi * K * (Real.sqrt N)⁻¹ := by
      field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hN), hsN.ne']
      rw [Real.sq_sqrt (le_trans (by norm_num) hN)]
      ring

private theorem responseRosenthal_rhs_le_dimensional_sqrt_card
    {d : ℕ} {xi K N : ℝ} (hxi : 2 ≤ xi) (hK : 0 ≤ K) (hN : 1 ≤ N) :
    N⁻¹ *
        (2 * xi *
            ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - xi⁻¹)) *
              N ^ xi⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt xi *
              (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                Real.sqrt N * K))) ≤
      (2 * ((freshShellColorPeriod d ^ d : ℕ) : ℝ) +
          4 * rosenthalBennettIntegralConst *
            Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ)) *
        xi * K * (Real.sqrt N)⁻¹ := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d072_responseRosenthal_rhs_le_dimensional_sqrt_card (d := d) (xi := xi) (K := K) (N := N) (hxi := hxi) (hK := hK) (hN := hN)

theorem aux_dedup_d180_inv_sqrt_card_descendantsAtScale_originCube_eq_rpow
    {d n m : ℕ} (hnm : n ≤ m) :
    (Real.sqrt
      ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ))⁻¹ =
      Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by
  rw [← Real.sqrt_inv]
  rw [inv_card_descendantsAtScale_originCube_eq_rpow hnm]
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow 3 (-((d * (m - n) : ℕ) : ℝ))) (1 / 2) =
        Real.rpow 3 (-((d * (m - n) : ℕ) : ℝ) * (1 / 2)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
        (-((d * (m - n) : ℕ) : ℝ)) (1 / 2)).symm
    _ = _ := by
      congr 1
      push_cast
      ring

private theorem inv_sqrt_card_descendantsAtScale_originCube_eq_rpow
    {d n m : ℕ} (hnm : n ≤ m) :
    (Real.sqrt
      ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ))⁻¹ =
      Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d180_inv_sqrt_card_descendantsAtScale_originCube_eq_rpow (d := d) (n := n) (m := m) (hnm := hnm)

/-- The printed one-line consequence of colored Rosenthal: after centering,
the descendant average gains the uniform square-root cardinality factor. -/
theorem exists_centeredCutoffResponseAverage_dimensional_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (L n m : ℕ), L ≤ n → n ≤ m →
        ∀ (p q : Vec d) (xi K : ℝ), 2 ≤ xi → 0 ≤ K →
        Integrable
          (fun omega =>
            |centeredCutoffResponseOnCube M L n p q
              (originCube d (n : ℤ)) omega| ^ xi) M.P.toMeasure →
        (∫ omega,
            |centeredCutoffResponseOnCube M L n p q
              (originCube d (n : ℤ)) omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤ K →
        (∫ omega,
            |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
              ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
                centeredCutoffResponseOnCube M L n p q R omega| ^ xi
              ∂M.P.toMeasure) ^ xi⁻¹ ≤
          C * xi * K *
            Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by
  let B : ℝ := ((freshShellColorPeriod d ^ d : ℕ) : ℝ)
  let C : ℝ := 1 + 2 * B +
    4 * rosenthalBennettIntegralConst * Real.sqrt B
  have hRB : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst,
      Homogenization.IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hC : 0 < C := by
    dsimp [C, B]
    positivity
  refine ⟨C, hC, ?_⟩
  intro _ M L n m hLn hnm p q xi K hxi hK hmoment hroot
  let N : ℝ :=
    ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (descendantsAtScale_nonempty (originCube d (m : ℤ))
      (by
        change (n : ℤ) ≤ (m : ℤ)
        exact_mod_cast hnm)).card_pos
  have hraw :=
    integral_abs_centeredCutoffResponseAverage_rpow_rpow_inv_le_of_origin_ae_local
      M L n m hLn p q hxi hK hmoment hroot
  have hsimp := responseRosenthal_rhs_le_dimensional_sqrt_card
    (d := d) hxi hK hN
  have hbase := hraw.trans hsimp
  rw [inv_sqrt_card_descendantsAtScale_originCube_eq_rpow hnm] at hbase
  have hcoef :
      2 * B + 4 * rosenthalBennettIntegralConst * Real.sqrt B ≤ C := by
    dsimp [C]
    linarith
  let T := xi * K * Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ))
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  exact hbase.trans (by
    calc
      (2 * B + 4 * rosenthalBennettIntegralConst * Real.sqrt B) * xi * K *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) =
          (2 * B + 4 * rosenthalBennettIntegralConst * Real.sqrt B) * T := by
            ring
      _ ≤ C * T := mul_le_mul_of_nonneg_right hcoef hT
      _ = C * xi * K *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by ring)

/-! ## Conversion back to the paper's `ENNReal` moment carrier -/



theorem paperENNRealLpNorm_ofReal_abs_eq_integral_abs_rpow_root
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ} (hX : Measurable X)
    (hXint : Integrable (fun omega => |X omega| ^ p) mu) :
    paperENNRealLpNorm mu p (fun omega => ENNReal.ofReal |X omega|) =
      ENNReal.ofReal ((∫ omega, |X omega| ^ p ∂mu) ^ p⁻¹) := by
  have hpzero : ENNReal.ofReal p ≠ 0 := by positivity
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnormInt : Integrable
      (fun omega => ‖X omega‖ ^ (ENNReal.ofReal p).toReal) mu := by
    simpa [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using hXint
  have hmem : MemLp X (ENNReal.ofReal p) mu :=
    (integrable_norm_rpow_iff hX.aestronglyMeasurable hpzero hptop).mp hnormInt
  have heq := hmem.eLpNorm_eq_integral_rpow_norm hpzero hptop
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hX.aestronglyMeasurable,
    SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral hpzero hptop] at heq
  unfold paperENNRealLpNorm
  rw [show (fun omega => ENNReal.ofReal |X omega| ^ p) =
      fun omega => ‖X omega‖ₑ ^ p by
    funext omega
    rw [← ofReal_norm, Real.norm_eq_abs]]
  simpa [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using heq

/-- Source  in the carrier used by the conclusion:
subadditivity, centered colored Rosenthal, and the stationary mean combine to
bound one fixed-direction parent response. -/
theorem paperENNRealLpNorm_cutoffResponseOnCube_le_centered_root_add_mean
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (_hLn : L ≤ n) (hnm : n ≤ m) (p q : Vec d) {xi A : ℝ}
    (hxi : 2 ≤ xi)
    (hmoment : Integrable
      (fun omega =>
        |centeredCutoffResponseOnCube M L n p q
          (originCube d (n : ℤ)) omega| ^ xi) M.P.toMeasure)
    (hcenter :
      (∫ omega,
          |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
            ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
              centeredCutoffResponseOnCube M L n p q R omega| ^ xi
          ∂M.P.toMeasure) ^ xi⁻¹ ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
        ENNReal.ofReal
          (cutoffResponseOnCube M L p q (originCube d (m : ℤ)) omega)) ≤
      ENNReal.ofReal
        (A + ∫ omega,
          cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega
            ∂M.P.toMeasure) := by
  let D := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
  let avg : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
      centeredCutoffResponseOnCube M L n p q R omega
  let mean : ℝ := ∫ omega,
    cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega ∂M.P.toMeasure
  have hxi0 : 0 < xi := by linarith
  have hmean0 : 0 ≤ mean := by
    dsimp [mean]
    apply integral_nonneg
    intro omega
    exact Ch02.responseJ_nonneg _ _ _ _
  have havgMeas : Measurable avg := by
    exact measurable_const.mul (Finset.measurable_sum _ fun R hR =>
      measurable_centeredCutoffResponseOnCube M L n p q R)
  have hcellInt : ∀ R ∈ D,
      Integrable
        (fun omega => |centeredCutoffResponseOnCube M L n p q R omega| ^ xi)
        M.P.toMeasure := by
    intro R hR
    exact (integrable_abs_centeredCutoffResponseOnCube_rpow_iff_originCube
      M L n p q R (scale_eq_of_mem_descendantsAtScale hR) xi
        (by linarith)).2 hmoment
  have hsumInt : Integrable
      (fun omega => |∑ R ∈ D,
        centeredCutoffResponseOnCube M L n p q R omega| ^ xi) M.P.toMeasure :=
    IndependentSums.integrable_abs_finsetSum_rpow (by linarith)
      (fun R hR => measurable_centeredCutoffResponseOnCube M L n p q R)
      hcellInt
  have hc0 : 0 ≤ ((D.card : ℝ)⁻¹) := by positivity
  have havgInt : Integrable (fun omega => |avg omega| ^ xi) M.P.toMeasure := by
    have hscaled := hsumInt.const_mul (((D.card : ℝ)⁻¹) ^ xi)
    simpa only [avg, abs_mul, abs_of_nonneg hc0,
      Real.mul_rpow hc0 (abs_nonneg _)] using hscaled
  have hpoint : ∀ omega,
      ENNReal.ofReal
          (cutoffResponseOnCube M L p q (originCube d (m : ℤ)) omega) ≤
        ENNReal.ofReal |avg omega| + ENNReal.ofReal mean := by
    intro omega
    rw [← ENNReal.ofReal_add (abs_nonneg _) hmean0]
    apply ENNReal.ofReal_le_ofReal
    calc
      cutoffResponseOnCube M L p q (originCube d (m : ℤ)) omega ≤
          avg omega + mean := by
        simpa only [avg, mean, D] using
          cutoffResponseOnCube_le_centeredDescendantAverage_add_mean
            M L n m hnm p q omega
      _ ≤ |avg omega| + mean := by linarith [le_abs_self (avg omega)]
  have hmono := paperENNRealLpNorm_mono_ae M.P.toMeasure hxi0.le
    (Filter.Eventually.of_forall hpoint)
  have habsMeas : Measurable (fun omega => |avg omega|) := by
    simpa only [Real.norm_eq_abs] using havgMeas.norm
  have hadd := paperENNRealLpNorm_add_le M.P.toMeasure
    (X := fun omega => ENNReal.ofReal |avg omega|)
    (Y := fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal mean)
    (show 1 ≤ xi by linarith)
    (ENNReal.continuous_ofReal.measurable.comp habsMeas).aemeasurable
    measurable_const.aemeasurable
  have havgNorm :
      paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => ENNReal.ofReal |avg omega|) ≤ ENNReal.ofReal A := by
    rw [paperENNRealLpNorm_ofReal_abs_eq_integral_abs_rpow_root
      M.P.toMeasure hxi0 havgMeas havgInt]
    exact ENNReal.ofReal_le_ofReal hcenter
  have hmeanNorm :
      paperENNRealLpNorm M.P.toMeasure xi (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal mean) =
        ENNReal.ofReal mean := by
    rw [show (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal mean) =
        (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal mean * 1) by
      funext omega
      simp]
    rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure hxi0
        (ENNReal.ofReal mean) (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => 1) measurable_const,
      paperENNRealLpNorm_one, mul_one]
  calc
    _ ≤ paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => ENNReal.ofReal |avg omega| + ENNReal.ofReal mean) := hmono
    _ ≤ paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => ENNReal.ofReal |avg omega|) +
        paperENNRealLpNorm M.P.toMeasure xi
          (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => ENNReal.ofReal mean) := hadd
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal mean := by
      rw [hmeanNorm]
      exact add_le_add havgNorm le_rfl
    _ = ENNReal.ofReal (A + mean) := (ENNReal.ofReal_add (by
      have hrootNonneg : 0 ≤
          (∫ omega, |avg omega| ^ xi ∂M.P.toMeasure) ^ xi⁻¹ := by positivity
      exact hrootNonneg.trans hcenter) hmean0).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab
