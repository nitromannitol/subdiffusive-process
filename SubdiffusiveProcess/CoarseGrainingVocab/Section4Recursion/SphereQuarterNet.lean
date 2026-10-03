module

public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentFactorization
public import SubdiffusiveProcess.CoarseGrainingVocab.Induction
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# A finite quarter-net for normalized response quadratic forms

The net is built in `EuclideanSpace`, rather than with the default supremum
norm on `Fin d → ℝ`.  The response comparison then uses the operator-norm
absorption behind the paper's factor `2`.  The module boundary mirrors
`Algsuperdiff/Section3/Provider/Homogenization/UnionDirectionNet.lean`, but
replaces that file's coordinate-direction estimate by the source-exact
quarter-net argument.
-/

open MeasureTheory Homogenization Homogenization.Book
open Metric
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- A finite Euclidean `1/4`-net of the unit sphere in `Vec d`. -/
structure QuarterNet (d : ℕ) where
  points : Finset (Vec d)
  unit : ∀ e ∈ points, vecNormSq e = 1
  cover : ∀ e : Vec d, vecNormSq e = 1 →
    ∃ v ∈ points, vecNormSq (e - v) < (1 / 4 : ℝ) ^ 2

private lemma euclidean_norm_sq_toLp {d : ℕ} (e : Vec d) :
    ‖WithLp.toLp 2 e‖ ^ 2 = vecNormSq e := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [vecNormSq, vecDot, Real.norm_eq_abs, pow_two]

theorem exists_quarterNet (d : ℕ) : Nonempty (QuarterNet d) := by
  let S : Set (EuclideanSpace ℝ (Fin d)) := Metric.sphere 0 1
  obtain ⟨t, htS, htfin, hcover⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).finite_cover_balls
      (by norm_num : (0 : ℝ) < 1 / 4)
  let F : Finset (EuclideanSpace ℝ (Fin d)) := htfin.toFinset
  refine ⟨{
    points := F.image WithLp.ofLp
    unit := ?_
    cover := ?_ }⟩
  · intro e he
    simp only [Finset.mem_image] at he
    obtain ⟨x, hxF, rfl⟩ := he
    have hxS : x ∈ S := htS (by simpa [F] using hxF)
    have hxnorm : ‖x‖ = 1 := by simpa [S, Metric.mem_sphere] using hxS
    rw [← euclidean_norm_sq_toLp (WithLp.ofLp x)]
    simp [hxnorm]
  · intro e he
    have heNorm : ‖WithLp.toLp 2 e‖ = 1 := by
      have hsquare := euclidean_norm_sq_toLp e
      nlinarith [norm_nonneg (WithLp.toLp 2 e)]
    have heS : WithLp.toLp 2 e ∈ S := by simpa [S, Metric.mem_sphere] using heNorm
    have heUnion := hcover heS
    rw [Set.mem_iUnion] at heUnion
    obtain ⟨x, heUnion⟩ := heUnion
    rw [Set.mem_iUnion] at heUnion
    obtain ⟨hx, hdist⟩ := heUnion
    refine ⟨WithLp.ofLp x, ?_, ?_⟩
    · simp only [Finset.mem_image]
      exact ⟨x, by simpa [F] using hx, rfl⟩
    · have hsquare := euclidean_norm_sq_toLp (e - WithLp.ofLp x)
      have hnorm : ‖WithLp.toLp 2 (e - WithLp.ofLp x)‖ < 1 / 4 := by
        simpa [dist_eq_norm] using hdist
      nlinarith [norm_nonneg (WithLp.toLp 2 (e - WithLp.ofLp x))]

end

private theorem abs_bilinear_le_operatorNorm {d : ℕ} (A : Mat d) (x y : Vec d) :
    |vecDot x (matVecMul A y)| ≤
      Ch02.matrixOperatorNorm A * Ch02.vecNorm x * Ch02.vecNorm y := by
  calc
    |vecDot x (matVecMul A y)| ≤
        Ch02.vecNorm x * Ch02.vecNorm (matVecMul A y) :=
      Ch02.abs_vecDot_le_vecNorm_mul_vecNorm _ _
    _ ≤ Ch02.vecNorm x *
        (Ch02.matrixOperatorNorm A * Ch02.vecNorm y) :=
      mul_le_mul_of_nonneg_left
        (Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm A y)
        (Ch02.vecNorm_nonneg x)
    _ = _ := by ring

private theorem matrixOperatorNorm_le_of_unit_quadratic_le {d : ℕ} [NeZero d]
    {A : Mat d} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (hunit : ∀ e : Vec d, vecNormSq e = 1 →
      vecDot e (matVecMul A e) ≤ c) :
    Ch02.matrixOperatorNorm A ≤ c := by
  have hC : (c • (1 : Mat d)).PosSemidef := Matrix.PosSemidef.one.smul hc
  have hAC : MatLoewnerLE A (c • (1 : Mat d)) := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp [vecDot, matVecMul]
    · have hxnorm : 0 < vecNormSq x :=
        lt_of_le_of_ne (vecNormSq_nonneg x)
          (by simpa [vecNormSq_eq_zero_iff, eq_comm] using hx)
      let t := Real.sqrt (vecNormSq x)
      let e : Vec d := t⁻¹ • x
      have ht : 0 < t := Real.sqrt_pos.2 hxnorm
      have htsq : t ^ 2 = vecNormSq x := Real.sq_sqrt hxnorm.le
      have he : vecNormSq e = 1 := by
        dsimp [e]
        rw [vecNormSq_smul]
        field_simp [ht.ne']
        nlinarith
      have hte : t • e = x := by
        ext i
        simp [e, ht.ne']
      have hscale :
          vecDot x (matVecMul A x) =
            t ^ 2 * vecDot e (matVecMul A e) := by
        conv_lhs => rw [← hte]
        rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
        ring
      have hqx : vecDot x (matVecMul A x) ≤ c * vecNormSq x := by
        rw [hscale, ← htsq]
        calc
          t ^ 2 * vecDot e (matVecMul A e) ≤ t ^ 2 * c :=
            mul_le_mul_of_nonneg_left (hunit e he) (sq_nonneg t)
          _ = c * t ^ 2 := by ring
      rw [smul_matVecMul, vecDot_smul_right]
      have hone : matVecMul (1 : Mat d) x = x := Matrix.one_mulVec x
      rw [hone]
      simpa [vecNormSq] using hqx
  have hop := Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef hA hC hAC
  simpa [Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hc] using hop

theorem QuarterNet.exists_quadratic_max {d : ℕ} [NeZero d] (net : QuarterNet d)
    (A : Mat d) (hA : A.PosSemidef) :
    ∃ v ∈ net.points, ∀ e : Vec d, vecNormSq e = 1 →
      vecDot e (matVecMul A e) ≤ 2 * vecDot v (matVecMul A v) := by
  have hnonempty : net.points.Nonempty := by
    let e : Vec d := Pi.single default 1
    have he : vecNormSq e = 1 := by
      simp only [e, vecNormSq, vecDot]
      rw [Finset.sum_eq_single default]
      · simp
      · intro i _ hi
        have hi0 : i ≠ (0 : Fin d) := by simpa using hi
        simp [hi0]
      · simp
    obtain ⟨v, hv, -⟩ := net.cover e he
    exact ⟨v, hv⟩
  obtain ⟨v, hv, hvmax⟩ := net.points.exists_max_image
    (fun x => vecDot x (matVecMul A x)) hnonempty
  refine ⟨v, hv, ?_⟩
  have hvunit := net.unit v hv
  have hvnorm : Ch02.vecNorm v = 1 := by
    have hsquare := Ch02.vecNorm_sq_eq_vecNormSq v
    nlinarith [Ch02.vecNorm_nonneg v]
  let N := vecDot v (matVecMul A v)
  let op := Ch02.matrixOperatorNorm A
  have hN : 0 ≤ N := by
    simpa [N, dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      hA.dotProduct_mulVec_nonneg v
  have hop : 0 ≤ op := Ch02.matrixOperatorNorm_nonneg A
  have hunitBound : ∀ e : Vec d, vecNormSq e = 1 →
      vecDot e (matVecMul A e) ≤ N + op / 2 := by
    intro e he
    obtain ⟨w, hw, hew⟩ := net.cover e he
    have hwunit := net.unit w hw
    have heNorm : Ch02.vecNorm e = 1 := by
      have hsquare := Ch02.vecNorm_sq_eq_vecNormSq e
      nlinarith [Ch02.vecNorm_nonneg e]
    have hwNorm : Ch02.vecNorm w = 1 := by
      have hsquare := Ch02.vecNorm_sq_eq_vecNormSq w
      nlinarith [Ch02.vecNorm_nonneg w]
    have hewNorm : Ch02.vecNorm (e - w) < 1 / 4 := by
      have hsquare := Ch02.vecNorm_sq_eq_vecNormSq (e - w)
      nlinarith [Ch02.vecNorm_nonneg (e - w)]
    have hwN : vecDot w (matVecMul A w) ≤ N := by
      simpa [N] using hvmax w hw
    have hsymm : A.IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.1
    have hAe : matVecMul A e = matVecMul A w + matVecMul A (e - w) := by
      calc
        matVecMul A e = matVecMul A (w + (e - w)) := by
          congr 1
          abel
        _ = _ := matVecMul_add A w (e - w)
    have hdecomp :
        vecDot e (matVecMul A e) =
          vecDot w (matVecMul A w) +
            vecDot w (matVecMul A (e - w)) +
              vecDot e (matVecMul A (e - w)) := by
      calc
        vecDot e (matVecMul A e) =
            vecDot e (matVecMul A w) +
              vecDot e (matVecMul A (e - w)) := by
          rw [hAe, vecDot_add_right]
        _ = vecDot w (matVecMul A e) +
              vecDot e (matVecMul A (e - w)) := by
          rw [vecDot_matVecMul_comm_of_isSymm hsymm e w]
        _ = _ := by rw [hAe, vecDot_add_right, add_assoc]
    have hcrossW : vecDot w (matVecMul A (e - w)) ≤ op / 4 := by
      calc
        vecDot w (matVecMul A (e - w)) ≤
            |vecDot w (matVecMul A (e - w))| := le_abs_self _
        _ ≤ op * Ch02.vecNorm w * Ch02.vecNorm (e - w) :=
          abs_bilinear_le_operatorNorm A w (e - w)
        _ ≤ op * 1 * (1 / 4) := by
          simpa [hwNorm, mul_assoc] using
            (mul_le_mul_of_nonneg_left hewNorm.le hop)
        _ = op / 4 := by ring
    have hcrossE : vecDot e (matVecMul A (e - w)) ≤ op / 4 := by
      calc
        vecDot e (matVecMul A (e - w)) ≤
            |vecDot e (matVecMul A (e - w))| := le_abs_self _
        _ ≤ op * Ch02.vecNorm e * Ch02.vecNorm (e - w) :=
          abs_bilinear_le_operatorNorm A e (e - w)
        _ ≤ op * 1 * (1 / 4) := by
          simpa [heNorm, mul_assoc] using
            (mul_le_mul_of_nonneg_left hewNorm.le hop)
        _ = op / 4 := by ring
    rw [hdecomp]
    linarith
  have hopBound : op ≤ N + op / 2 := by
    simpa [op] using matrixOperatorNorm_le_of_unit_quadratic_le hA
      (by positivity : 0 ≤ N + op / 2) hunitBound
  intro e he
  have heBound := hunitBound e he
  dsimp [N, op] at hopBound heBound ⊢
  linarith

/-- One fixed quarter-net, chosen once for each dimension. -/
noncomputable def sphereQuarterNet (d : ℕ) : QuarterNet d :=
  Classical.choice (exists_quarterNet d)

theorem sphereQuarterNet_points_nonempty {d : ℕ} [NeZero d] :
    (sphereQuarterNet d).points.Nonempty := by
  let e : Vec d := Pi.single default 1
  have he : vecNormSq e = 1 := by
    simp only [e, vecNormSq, vecDot]
    rw [Finset.sum_eq_single default]
    · simp
    · intro i _ hi
      have hi0 : i ≠ (0 : Fin d) := by simpa using hi
      simp [hi0]
    · simp
  obtain ⟨v, hv, -⟩ := (sphereQuarterNet d).cover e he
  exact ⟨v, hv⟩

noncomputable def normalizedResponseQuarterNetMax {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (U : Ch02.Domain d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ :=
  (sphereQuarterNet d).points.sup' sphereQuarterNet_points_nonempty fun e omega =>
    ENNReal.ofReal
      (J U (aCutoffCoeffOnData M n omega U).toCoeffOn
        ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e))

theorem measurable_normalizedResponseQuarterNetMax {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (U : Ch02.Domain d) :
    Measurable (normalizedResponseQuarterNetMax M n U) := by
  unfold normalizedResponseQuarterNetMax
  apply Finset.measurable_sup'
  intro e he
  exact ENNReal.continuous_ofReal.measurable.comp
    (measurable_cutoff_responseJ M n U
      ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e))

theorem normalizedDefect_le_two_mul_quarterNetMax {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (U : Ch02.Domain d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    normalizedDefect M n U omega ≤
      2 * normalizedResponseQuarterNetMax M n U omega := by
  unfold normalizedDefect paperScalarProbeMaxOn
  apply iSup_le
  intro e
  obtain ⟨v, hv, hmax⟩ :=
    (sphereQuarterNet d).exists_quadratic_max
      (normalizedDefectMatrix M n U omega)
      (normalizedDefectMatrix_posSemidef M n U omega)
  have hq := hmax e e.2
  rw [← normalizedDefectMatrix_quadratic M n U omega e] at hq
  rw [← normalizedDefectMatrix_quadratic M n U omega v] at hq
  calc
    ENNReal.ofReal
        (J U (aCutoffCoeffOnData M n omega U).toCoeffOn
          ((Real.sqrt (ahom M n))⁻¹ • (e : Vec d))
          (Real.sqrt (ahom M n) • (e : Vec d))) ≤
        ENNReal.ofReal
          (2 * J U (aCutoffCoeffOnData M n omega U).toCoeffOn
            ((Real.sqrt (ahom M n))⁻¹ • v)
            (Real.sqrt (ahom M n) • v)) :=
      ENNReal.ofReal_le_ofReal hq
    _ = 2 * ENNReal.ofReal
          (J U (aCutoffCoeffOnData M n omega U).toCoeffOn
            ((Real.sqrt (ahom M n))⁻¹ • v)
            (Real.sqrt (ahom M n) • v)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ 2 * normalizedResponseQuarterNetMax M n U omega := by
      have hle := Finset.le_sup'
        (fun x => ENNReal.ofReal
          (J U (aCutoffCoeffOnData M n omega U).toCoeffOn
            ((Real.sqrt (ahom M n))⁻¹ • x)
            (Real.sqrt (ahom M n) • x))) hv
      have hle' : ENNReal.ofReal
          (J U (aCutoffCoeffOnData M n omega U).toCoeffOn
            ((Real.sqrt (ahom M n))⁻¹ • v)
            (Real.sqrt (ahom M n) • v)) ≤
          normalizedResponseQuarterNetMax M n U omega := by
        simpa only [normalizedResponseQuarterNetMax, Finset.sup'_apply] using hle
      gcongr

theorem paperENNRealLpNorm_finset_sum_le {Omega ι : Type*}
    [MeasurableSpace Omega] [DecidableEq ι] (mu : Measure Omega)
    {xi : ℝ} (hxi : 1 ≤ xi) (s : Finset ι) (X : ι → Omega → ℝ≥0∞)
    (hX : ∀ i ∈ s, Measurable (X i)) :
    paperENNRealLpNorm mu xi (fun omega => ∑ i ∈ s, X i omega) ≤
      ∑ i ∈ s, paperENNRealLpNorm mu xi (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hxiPos : 0 < xi := zero_lt_one.trans_le hxi
      simp [paperENNRealLpNorm, hxiPos]
  | @insert i s hi ih =>
      have hXi : Measurable (X i) := hX i (Finset.mem_insert_self i s)
      have hXs : Measurable (fun omega => ∑ j ∈ s, X j omega) := by
        apply Finset.measurable_sum
        intro j hj
        exact hX j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      calc
        paperENNRealLpNorm mu xi
            (fun omega => X i omega + ∑ j ∈ s, X j omega) ≤
            paperENNRealLpNorm mu xi (X i) +
              paperENNRealLpNorm mu xi (fun omega => ∑ j ∈ s, X j omega) :=
          paperENNRealLpNorm_add_le mu hxi hXi.aemeasurable hXs.aemeasurable
        _ ≤ paperENNRealLpNorm mu xi (X i) +
              ∑ j ∈ s, paperENNRealLpNorm mu xi (X j) := by
          gcongr
          exact ih (fun j hj => hX j (Finset.mem_insert_of_mem hj))

theorem paperENNRealLpNorm_finset_sup'_le_sum {Omega ι : Type*}
    [MeasurableSpace Omega] [DecidableEq ι] (mu : Measure Omega)
    {xi : ℝ} (hxi : 1 ≤ xi) (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Omega → ℝ≥0∞) (hX : ∀ i ∈ s, Measurable (X i)) :
    paperENNRealLpNorm mu xi (s.sup' hs X) ≤
      ∑ i ∈ s, paperENNRealLpNorm mu xi (X i) := by
  calc
    paperENNRealLpNorm mu xi (s.sup' hs X) ≤
        paperENNRealLpNorm mu xi (fun omega => ∑ i ∈ s, X i omega) := by
      apply paperENNRealLpNorm_mono_ae mu (zero_le_one.trans hxi)
      filter_upwards [] with omega
      simp only [Finset.sup'_apply]
      apply Finset.sup'_le
      intro i hi
      exact Finset.single_le_sum (fun j _ => (show 0 ≤ X j omega from zero_le)) hi
    _ ≤ _ := paperENNRealLpNorm_finset_sum_le mu hxi s X hX

theorem paperENNRealLpNorm_normalizedDefect_le_quarterNetSum {d : ℕ}
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ)
    (U : Ch02.Domain d) {xi : ℝ} (hxi : 1 ≤ xi) :
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefect M n U) ≤
      2 * ∑ e ∈ (sphereQuarterNet d).points,
        paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
          ENNReal.ofReal
            (J U (aCutoffCoeffOnData M n omega U).toCoeffOn
              ((Real.sqrt (ahom M n))⁻¹ • e)
              (Real.sqrt (ahom M n) • e))) := by
  let X := fun e : Vec d => fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
    ENNReal.ofReal
      (J U (aCutoffCoeffOnData M n omega U).toCoeffOn
        ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e))
  have hXm : ∀ e ∈ (sphereQuarterNet d).points, Measurable (X e) := by
    intro e he
    exact ENNReal.continuous_ofReal.measurable.comp
      (measurable_cutoff_responseJ M n U
        ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e))
  calc
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefect M n U) ≤
        paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => 2 * normalizedResponseQuarterNetMax M n U omega) := by
      exact paperENNRealLpNorm_mono_ae M.P.toMeasure (zero_le_one.trans hxi)
        (Filter.Eventually.of_forall
          (normalizedDefect_le_two_mul_quarterNetMax M n U))
    _ = 2 * paperENNRealLpNorm M.P.toMeasure xi
          (normalizedResponseQuarterNetMax M n U) := by
      rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure
        (zero_lt_one.trans_le hxi) 2 _
        (measurable_normalizedResponseQuarterNetMax M n U)]
    _ ≤ 2 * ∑ e ∈ (sphereQuarterNet d).points,
          paperENNRealLpNorm M.P.toMeasure xi (X e) := by
      gcongr
      exact paperENNRealLpNorm_finset_sup'_le_sum M.P.toMeasure hxi
        (sphereQuarterNet d).points sphereQuarterNet_points_nonempty X hXm

end SubdiffusiveProcess.CoarseGrainingVocab
