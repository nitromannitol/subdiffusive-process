module

public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section
/-!
# Per-cube response localization

This file is the deterministic sensitivity step in the proof of
`l.ellipticity.bound`. It keeps the stochastic ratio error separate from the
response to the lower cutoff, which is the split needed by the subsequent
independence argument.
-/


namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization Homogenization.Book

noncomputable section

/-- The symmetric scalar-ratio error which localizes a response at cutoff `L`
to cutoff `k`, with the target scalar normalizer `b`. -/
noncomputable def responseLocalizationError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (U : Ch02.Domain d) (b : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  let lambda := b / ahom M k
  scalarRatioLInf U
      (fun x => lambda * _root_.SubdiffusiveProcess.Model.aCutoff M k ω x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) +
    scalarRatioLInf U
      (fun x => lambda⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M L ω x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M k ω)

theorem responseLocalizationError_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (U : Ch02.Domain d) (b : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ responseLocalizationError M L k U b ω :=
  add_nonneg (scalarRatioLInf_nonneg _ _ _) (scalarRatioLInf_nonneg _ _ _)

/-- Paper display before taking the cutoff and
unit-sphere suprema.  The coefficient-ratio error is the exact `L∞` error
consumed by `responseJ_sensitivity`; later field estimates dominate it by the
paper's explicit `X_(m,k)` representative. -/
theorem responseJ_cutoff_le_localized {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (U : Ch02.Domain d) (b : ℝ) (hb : 0 < b)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (e : Vec d)
    (he : vecNormSq e = 1) :
    J U (aCutoffCoeffOnData M L ω U).toCoeffOn
        ((Real.sqrt b)⁻¹ • e) (Real.sqrt b • e) ≤
      2 * J U (aCutoffCoeffOnData M k ω U).toCoeffOn
          ((Real.sqrt (ahom M k))⁻¹ • e) (Real.sqrt (ahom M k) • e) +
        3 * responseLocalizationError M L k U b ω ^ 2 *
          (J U (aCutoffCoeffOnData M k ω U).toCoeffOn
            ((Real.sqrt (ahom M k))⁻¹ • e)
            (Real.sqrt (ahom M k) • e) + 1) := by
  let alpha := ahom M k
  have ha : 0 < alpha := (Real.exp_pos _).trans_le
    (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M k)
  let lambda := b / alpha
  have hlambda : 0 < lambda := div_pos hb ha
  let p : Vec d := (Real.sqrt alpha)⁻¹ • e
  let q : Vec d := Real.sqrt alpha • e
  have hsqrt : Real.sqrt b = Real.sqrt lambda * Real.sqrt alpha := by
    rw [show b = lambda * alpha by
      dsimp [lambda]
      exact (div_mul_cancel₀ b ha.ne').symm]
    exact Real.sqrt_mul hlambda.le alpha
  have hp : (Real.sqrt lambda)⁻¹ • p = (Real.sqrt b)⁻¹ • e := by
    ext i
    simp only [p, Pi.smul_apply, smul_eq_mul]
    rw [hsqrt]
    field_simp [Real.sqrt_ne_zero'.mpr hlambda, Real.sqrt_ne_zero'.mpr ha]
  have hq : Real.sqrt lambda • q = Real.sqrt b • e := by
    ext i
    simp [q, hsqrt, mul_assoc]
  have hpq : vecDot p q = 1 := by
    have he' : vecDot e e = 1 := he
    simp [p, q, vecDot_smul_left, vecDot_smul_right, he',
      Real.sqrt_ne_zero'.mpr ha]
  have hraw := responseJ_sensitivity
    (aCutoffCoeffOnData M k ω U) (aCutoffCoeffOnData M L ω U)
    hlambda (by norm_num : (0 : ℝ) < 1) (le_rfl) p q
  rw [hp, hq, hpq] at hraw
  have hx0 : 0 ≤ scalarRatioLInf U
      (fun x => lambda * _root_.SubdiffusiveProcess.Model.aCutoff M k ω x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) := scalarRatioLInf_nonneg _ _ _
  have hy0 : 0 ≤ scalarRatioLInf U
      (fun x => lambda⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M L ω x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M k ω) := scalarRatioLInf_nonneg _ _ _
  have hsquares :
      scalarRatioLInf U
          (fun x => lambda * _root_.SubdiffusiveProcess.Model.aCutoff M k ω x)
          (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) ^ 2 +
        scalarRatioLInf U
          (fun x => lambda⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M L ω x)
          (_root_.SubdiffusiveProcess.Model.aCutoff M k ω) ^ 2 ≤
        responseLocalizationError M L k U b ω ^ 2 := by
    dsimp [responseLocalizationError, lambda, alpha]
    nlinarith [mul_nonneg hx0 hy0]
  have hJ0 := Ch02.responseJ_nonneg U
    (aCutoffCoeffOnData M k ω U).toCoeffOn p q
  have hfactor : 0 ≤ J U (aCutoffCoeffOnData M k ω U).toCoeffOn p q + 1 := by
    linarith
  have hraw' :
      J U (aCutoffCoeffOnData M L ω U).toCoeffOn
          ((Real.sqrt b)⁻¹ • e) (Real.sqrt b • e) ≤
        2 * J U (aCutoffCoeffOnData M k ω U).toCoeffOn p q +
          3 *
            (scalarRatioLInf U
                (fun x => lambda * _root_.SubdiffusiveProcess.Model.aCutoff M k ω x)
                (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) ^ 2 +
              scalarRatioLInf U
                (fun x => lambda⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M L ω x)
                (_root_.SubdiffusiveProcess.Model.aCutoff M k ω) ^ 2) *
            (J U (aCutoffCoeffOnData M k ω U).toCoeffOn p q + 1) := by
    norm_num at hraw
    exact hraw
  calc
    J U (aCutoffCoeffOnData M L ω U).toCoeffOn
        ((Real.sqrt b)⁻¹ • e) (Real.sqrt b • e) ≤ _ := hraw'
    _ ≤ 2 * J U (aCutoffCoeffOnData M k ω U).toCoeffOn p q +
        3 * responseLocalizationError M L k U b ω ^ 2 *
          (J U (aCutoffCoeffOnData M k ω U).toCoeffOn p q + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hsquares
        (by norm_num : (0 : ℝ) ≤ 3)
      have hmul' := mul_le_mul_of_nonneg_right hmul hfactor
      exact add_le_add_right hmul'
        (2 * J U (aCutoffCoeffOnData M k ω U).toCoeffOn p q)

/-- Unit-sphere form of `responseJ_cutoff_le_localized`, on the frozen
`ENNReal` response carrier. -/
theorem paperScalarProbeMaxOn_cutoff_le_localized {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (U : Ch02.Domain d) (b : ℝ) (hb : 0 < b)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    paperScalarProbeMaxOn U (aCutoffCoeffOnData M L ω U).toCoeffOn b ≤
      2 * normalizedDefect M k U ω +
        3 * ENNReal.ofReal (responseLocalizationError M L k U b ω ^ 2) *
          (normalizedDefect M k U ω + 1) := by
  unfold paperScalarProbeMaxOn
  apply iSup_le
  intro e
  let Jk : ℝ := J U (aCutoffCoeffOnData M k ω U).toCoeffOn
    ((Real.sqrt (ahom M k))⁻¹ • e.1) (Real.sqrt (ahom M k) • e.1)
  let X : ℝ := responseLocalizationError M L k U b ω
  have hJk0 : 0 ≤ Jk := Ch02.responseJ_nonneg U _ _ _
  have hX0 : 0 ≤ X := responseLocalizationError_nonneg M L k U b ω
  have hloc := responseJ_cutoff_le_localized M L k U b hb ω e.1 e.2
  have hreal0 : 0 ≤ 2 * Jk + 3 * X ^ 2 * (Jk + 1) := by positivity
  have hbase : ENNReal.ofReal Jk ≤ normalizedDefect M k U ω := by
    unfold normalizedDefect paperScalarProbeMaxOn
    exact le_iSup (fun v : {v : Vec d // vecNormSq v = 1} =>
      ENNReal.ofReal
        (J U (aCutoffCoeffOnData M k ω U).toCoeffOn
          ((Real.sqrt (ahom M k))⁻¹ • v.1)
          (Real.sqrt (ahom M k) • v.1))) e
  calc
    ENNReal.ofReal
        (J U (aCutoffCoeffOnData M L ω U).toCoeffOn
          ((Real.sqrt b)⁻¹ • e.1) (Real.sqrt b • e.1)) ≤
      ENNReal.ofReal (2 * Jk + 3 * X ^ 2 * (Jk + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [Jk, X] using hloc
    _ = 2 * ENNReal.ofReal Jk +
        3 * ENNReal.ofReal (X ^ 2) * (ENNReal.ofReal Jk + 1) := by
      rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hJk0)
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg X))
            (by linarith : 0 ≤ Jk + 1)),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat,
        ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
          (sq_nonneg X)),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add hJk0 (by norm_num : (0 : ℝ) ≤ 1),
        ENNReal.ofReal_one]
    _ ≤ 2 * normalizedDefect M k U ω +
        3 * ENNReal.ofReal (X ^ 2) * (normalizedDefect M k U ω + 1) := by
      gcongr
    _ = _ := by rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab
