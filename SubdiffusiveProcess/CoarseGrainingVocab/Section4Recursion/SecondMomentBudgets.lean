module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpTwoBlockMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.LargeCubePartitionResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.AnnealedDualMeanDefect
public import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ
public import SubdiffusiveProcess.Frozen.Section4.MultiscaleResponseLargeCubes
public import Homogenization.Sobolev.Foundations.DifferenceQuotient
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Second-moment budgets for the Section 4 recursion

This module supplies the square-integrability and second-moment inputs used in
Steps 3 and 4 of `p.combine.under.S`.

PROVENANCE: the moment downgrade mirrors the `L^Q`-to-`L^2` step in
`Algsuperdiff/HighContrast/EntryScale/MomentConsequences/P1.lean`.  The
large-cube transport is the GMC partition/subadditivity endpoint in
`Section4Support/LargeCubePartitionResponse.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal MatrixOrder

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem normalizedDefect_ne_top {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    normalizedDefect M L U omega ≠ ∞ := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d203_normalizedDefect_ne_top (d := d) (M := M) (L := L) (U := U) (omega := omega)

/-- The manuscript's finite `ENNReal` moment carrier agrees with the ordinary
`eLpNorm` of its real representative. -/
theorem paperENNRealLpNorm_eq_eLpNorm_toReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞}
    (hX : ∀ omega, X omega ≠ ∞) :
    paperENNRealLpNorm mu p X =
      SubdiffusiveProcess.RawLp.eLpNorm (fun omega => (X omega).toReal) (ENNReal.ofReal p) mu := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d121_paperENNRealLpNorm_eq_eLpNorm_toReal (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X) (hX := hX)



theorem paperENNRealLpNorm_eq_guarded_eLpNorm_toReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞}
    (hX : ∀ omega, X omega ≠ ∞)
    (hm : AEStronglyMeasurable (fun omega => (X omega).toReal) mu) :
    paperENNRealLpNorm mu p X = eLpNorm (fun omega => (X omega).toReal) (ENNReal.ofReal p) mu := by
  rw [paperENNRealLpNorm_eq_eLpNorm_toReal mu hp hX, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hm]

/-- Lyapunov downgrade of the propagated normalized defect, with both first
and second real moments exposed. -/
theorem normalizedDefect_toReal_moment_budgets
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L k : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1)
    (hLk : L ≤ k) (hLm0 : L ≤ m0) (Q : TriadicCube d)
    (hQ : Q.scale = (k : ℤ)) :
    let D : Sample d → ℝ := fun omega =>
      (normalizedDefect M L (Ch02.cubeDomain Q) omega).toReal
    MemLp D 2 M.P.toMeasure ∧
      ∫ omega, D omega ∂M.P.toMeasure ≤ delta1 ∧
      ∫ omega, D omega ^ 2 ∂M.P.toMeasure ≤ delta1 ^ 2 := by
  dsimp only
  let X : Sample d → ℝ≥0∞ := normalizedDefect M L (Ch02.cubeDomain Q)
  let D : Sample d → ℝ := fun omega => (X omega).toReal
  have hXmeas : Measurable X :=
    (measurable_normalizedDefect_potentialShellIndexSigma_Iic M L
      (Ch02.cubeDomain Q)).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  have hXtop : ∀ omega, X omega ≠ ∞ := fun omega =>
    normalizedDefect_ne_top M L (Ch02.cubeDomain Q) omega
  have hXxi : paperENNRealLpNorm M.P.toMeasure xi X ≤
      ENNReal.ofReal delta1 := by
    simpa [X] using! normalizedDefect_largeCube_lpnorm_le_induction
      M hS.1 hS hLk hLm0 Q hQ
  have hxiPos : 0 < xi := by linarith
  have hDXi : eLpNorm D (ENNReal.ofReal xi) M.P.toMeasure ≤
      ENNReal.ofReal delta1 := by
    rw [← paperENNRealLpNorm_eq_guarded_eLpNorm_toReal M.P.toMeasure hxiPos hXtop hXmeas.ennreal_toReal.aestronglyMeasurable]
    exact hXxi
  have htwoXi : (2 : ℝ≥0∞) ≤ ENNReal.ofReal xi := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hxi
  have hDTwo : eLpNorm D 2 M.P.toMeasure ≤ ENNReal.ofReal delta1 :=
    (eLpNorm_le_eLpNorm_of_exponent_le htwoXi).trans hDXi
  have hDMem : MemLp D 2 M.P.toMeasure :=
    hDTwo.trans_lt ENNReal.ofReal_lt_top
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  have hDtoReal : (eLpNorm D 2 M.P.toMeasure).toReal ≤ delta1 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hDTwo
    simpa [ENNReal.toReal_ofReal hdelta0] using! this
  have hsecond : ∫ omega, D omega ^ 2 ∂M.P.toMeasure ≤ delta1 ^ 2 := by
    rw [← Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hDMem]
    exact (sq_le_sq₀ (by positivity) hdelta0).2 hDtoReal
  have hvar := ProbabilityTheory.variance_nonneg D M.P.toMeasure
  rw [ProbabilityTheory.variance_eq_sub hDMem] at hvar
  simp only [Pi.pow_apply] at hvar
  have hmean0 : 0 ≤ ∫ omega, D omega ∂M.P.toMeasure :=
    integral_nonneg fun _ => ENNReal.toReal_nonneg
  have hmean : ∫ omega, D omega ∂M.P.toMeasure ≤ delta1 := by
    nlinarith
  simpa [D, X] using! And.intro hDMem (And.intro hmean hsecond)

/-- A headline load `q = ahom_L p`, normalized by `|q|² ≤ ahom_L`, is
pointwise bounded by the normalized scalar defect. -/
theorem cutoffResponseOnCube_le_normalizedDefect_toReal_of_headline_load
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (p q : Vec d)
    (hq : q = ahom M L • p) (hqNorm : vecNormSq q ≤ ahom M L)
    (omega : Sample d) :
    cutoffResponseOnCube M L p q Q omega ≤
      (normalizedDefect M L (Ch02.cubeDomain Q) omega).toReal := by
  let alpha := ahom M L
  let c := Real.sqrt alpha
  let e : Vec d := c • p
  let U := Ch02.cubeDomain Q
  let a := (aCutoffCoeffOnData M L omega U).toCoeffOn
  let R := normalizedDefectMatrix M L U omega
  have halpha : 0 < alpha := by
    simpa [alpha] using! ahom_pos M L
  have hc : 0 < c := Real.sqrt_pos.2 halpha
  have hcSq : c ^ 2 = alpha := Real.sq_sqrt halpha.le
  have hpRep : c⁻¹ • e = p := by
    ext i
    simp [e, hc.ne']
  have hqRep : c • e = q := by
    rw [hq]
    ext i
    simp only [e, smul_smul, Pi.smul_apply]
    change (c * c) * p i = alpha * p i
    rw [show c * c = alpha by nlinarith [hcSq]]
  have hqNorm' : alpha ^ 2 * vecNormSq p ≤ alpha := by
    simpa [hq, vecNormSq_smul] using! hqNorm
  have heNorm : vecNormSq e ≤ 1 := by
    dsimp only [e]
    rw [vecNormSq_smul, hcSq]
    nlinarith [mul_nonneg halpha.le (vecNormSq_nonneg p)]
  have hR : R.PosSemidef := by
    simpa [R, U] using! normalizedDefectMatrix_posSemidef M L U omega
  have hquad :
      J U a (c⁻¹ • e) (c • e) = vecDot e (matVecMul R e) := by
    simpa [a, R, U, alpha, c] using
      normalizedDefectMatrix_quadratic M L U omega e
  have hqform : vecDot e (matVecMul R e) ≤ Ch02.matrixOperatorNorm R := by
    calc
      vecDot e (matVecMul R e) ≤
          Ch02.matrixOperatorNorm R * vecNormSq e :=
        Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
          hR e
      _ ≤ Ch02.matrixOperatorNorm R * 1 :=
        mul_le_mul_of_nonneg_left heNorm (Ch02.matrixOperatorNorm_nonneg R)
      _ = Ch02.matrixOperatorNorm R := mul_one _
  have hENN : ENNReal.ofReal (cutoffResponseOnCube M L p q Q omega) ≤
      normalizedDefect M L U omega := by
    rw [normalizedDefect,
      paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm U a alpha R hR
        (by simpa [a, R, U, alpha, c] using
          normalizedDefectMatrix_quadratic M L U omega)]
    apply ENNReal.ofReal_le_ofReal
    simpa [cutoffResponseOnCube, aCutoffFamily, aCutoffTriadicData, U, a,
      hpRep, hqRep] using! hquad.trans_le hqform
  exact (ENNReal.ofReal_le_iff_le_toReal
    (normalizedDefect_ne_top M L U omega)).mp hENN



theorem cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L k : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1)
    (hLk : L ≤ k) (hLm0 : L ≤ m0)
    (p q : Vec d) (hq : q = ahom M L • p)
    (hqNorm : vecNormSq q ≤ ahom M L) :
    Integrable (fun omega : Sample d =>
        cutoffResponseOnCube M L p q (originCube d (k : ℤ)) omega ^ 2)
        M.P.toMeasure ∧
      ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (k : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤ delta1 ^ 2 := by
  let Q := originCube d (k : ℤ)
  let U := Ch02.cubeDomain Q
  let D : Sample d → ℝ≥0∞ := normalizedDefect M L U
  let Dr : Sample d → ℝ := fun omega => (D omega).toReal
  let Y : Sample d → ℝ := cutoffResponseOnCube M L p q Q
  have hDmeas : Measurable D :=
    (measurable_normalizedDefect_potentialShellIndexSigma_Iic M L U).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  have hDtop : ∀ omega, D omega ≠ ∞ := fun omega => by
    simpa [D, U] using! normalizedDefect_ne_top M L U omega
  have hDxi : paperENNRealLpNorm M.P.toMeasure xi D ≤
      ENNReal.ofReal delta1 := by
    simpa [D, U, Q] using! normalizedDefect_largeCube_lpnorm_le_induction
      M hS.1 hS hLk hLm0 Q rfl
  have hxiPos : 0 < xi := by linarith
  have hDrXi : eLpNorm Dr (ENNReal.ofReal xi) M.P.toMeasure ≤
      ENNReal.ofReal delta1 := by
    rw [← paperENNRealLpNorm_eq_guarded_eLpNorm_toReal M.P.toMeasure hxiPos hDtop hDmeas.ennreal_toReal.aestronglyMeasurable]
    exact hDxi
  have htwoXi : (2 : ℝ≥0∞) ≤ ENNReal.ofReal xi := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hxi
  have hDrTwo : eLpNorm Dr 2 M.P.toMeasure ≤ ENNReal.ofReal delta1 :=
    (eLpNorm_le_eLpNorm_of_exponent_le htwoXi).trans hDrXi
  have hDrMem : MemLp Dr 2 M.P.toMeasure :=
    hDrTwo.trans_lt ENNReal.ofReal_lt_top
  have hYmeas : AEStronglyMeasurable Y M.P.toMeasure := by
    exact (measurable_cutoffResponseOnCube M L p q Q).aestronglyMeasurable
  have hYnonneg : ∀ omega, 0 ≤ Y omega := fun omega =>
    Ch02.responseJ_nonneg U
      (aCutoffCoeffOnData M L omega U).toCoeffOn p q
  have hYD : ∀ omega, Y omega ≤ Dr omega := fun omega => by
    simpa [Y, Dr, D, U, Q] using
      cutoffResponseOnCube_le_normalizedDefect_toReal_of_headline_load
        M L Q p q hq hqNorm omega
  have hYMem : MemLp Y 2 M.P.toMeasure :=
    hDrMem.mono' hYmeas (Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg omega)]
      exact hYD omega)
  have hYnorm : eLpNorm Y 2 M.P.toMeasure ≤ ENNReal.ofReal delta1 :=
    (eLpNorm_mono_ae hYmeas (Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg omega),
        Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact hYD omega)).trans hDrTwo
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  have hYreal : (eLpNorm Y 2 M.P.toMeasure).toReal ≤ delta1 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hYnorm
    simpa [ENNReal.toReal_ofReal hdelta0] using! this
  have hsq : Integrable (fun omega => Y omega ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hYmeas).1 hYMem
  refine ⟨by simpa [Y, Q] using! hsq, ?_⟩
  rw [← Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hYMem]
  exact (sq_le_sq₀ (by positivity) hdelta0).2 hYreal

/-- Stationary translated-cube form of
`cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis`. -/
theorem cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis_cube
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L k : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1)
    (hLk : L ≤ k) (hLm0 : L ≤ m0)
    (Q : TriadicCube d) (hQ : Q.scale = (k : ℤ))
    (p q : Vec d) (hq : q = ahom M L • p)
    (hqNorm : vecNormSq q ≤ ahom M L) :
    Integrable (fun omega : Sample d =>
        cutoffResponseOnCube M L p q Q omega ^ 2) M.P.toMeasure ∧
      ∫ omega, cutoffResponseOnCube M L p q Q omega ^ 2
          ∂M.P.toMeasure ≤ delta1 ^ 2 := by
  let Q0 := originCube d (k : ℤ)
  let Y : Sample d → ℝ := fun omega =>
    cutoffResponseOnCube M L p q Q0 omega ^ 2
  let T := translatePotentialSequence (triadicCubeShift Q)
  have hbase :=
    cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis
      M hxi hS hLk hLm0 p q hq hqNorm
  have hYmeas : AEStronglyMeasurable Y M.P.toMeasure := by
    exact ((measurable_cutoffResponseOnCube M L p q Q0).pow_const 2).aestronglyMeasurable
  have hT : MeasurePreserving T M.P.toMeasure M.P.toMeasure :=
    ⟨measurable_translatePotentialSequence (triadicCubeShift Q),
      potentialSequenceLaw_stationary M (triadicCubeShift Q)⟩
  have heq : (fun omega => cutoffResponseOnCube M L p q Q omega ^ 2) = Y ∘ T := by
    funext omega
    rw [cutoffResponseOnCube_eq_originCube_translate M L p q Q omega, hQ]
    rfl
  have hint : Integrable (fun omega => cutoffResponseOnCube M L p q Q omega ^ 2)
      M.P.toMeasure := by
    rw [heq]
    exact hT.integrable_comp hYmeas |>.2 (by simpa [Y, Q0] using! hbase.1)
  refine ⟨hint, ?_⟩
  calc
    ∫ omega, cutoffResponseOnCube M L p q Q omega ^ 2 ∂M.P.toMeasure =
        ∫ omega, Y (T omega) ∂M.P.toMeasure := by
      rw [heq]
      rfl
    _ = ∫ omega, Y omega ∂M.P.toMeasure :=
      integral_comp_eq_of_map_eq hT.1 hT.2 Y hYmeas
    _ ≤ delta1 ^ 2 := by simpa [Y, Q0] using! hbase.2

/-- Each coordinate response in the local trace term has the source-exact
`ahom⁻² delta₁²` second-moment budget. -/
theorem coordinateLocalResponse_sq_integrable_and_integral_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (Q : TriadicCube d) (hQ : Q.scale = (L : ℤ)) (i : Fin d) :
    let e : Vec d := Pi.single i 1
    Integrable (fun omega : Sample d =>
        cutoffResponseOnCube M L ((ahom M L)⁻¹ • e) e Q omega ^ 2)
        M.P.toMeasure ∧
      ∫ omega, cutoffResponseOnCube M L ((ahom M L)⁻¹ • e) e Q omega ^ 2
          ∂M.P.toMeasure ≤ (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  dsimp only
  let alpha := ahom M L
  let c := Real.sqrt alpha
  let e : Vec d := Pi.single i 1
  let p0 : Vec d := c⁻¹ • e
  let q0 : Vec d := c • e
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  have hc : 0 < c := Real.sqrt_pos.2 halpha
  have hcSq : c ^ 2 = alpha := Real.sq_sqrt halpha.le
  have he : vecNormSq e = 1 := by
    simp only [e, vecNormSq, vecDot]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      simp [hji]
    · simp
  have hq0 : q0 = ahom M L • p0 := by
    dsimp only [q0, p0]
    ext j
    simp only [Pi.smul_apply, smul_smul]
    change c * e j = ahom M L * c⁻¹ * e j
    rw [show ahom M L = c ^ 2 by simpa [alpha] using! hcSq.symm]
    field_simp [hc.ne']
  have hq0Norm : vecNormSq q0 ≤ ahom M L := by
    dsimp only [q0]
    rw [vecNormSq_smul, he, mul_one]
    simpa [alpha] using! hcSq.le
  have hbase :=
    cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis_cube
      M hxi hS le_rfl hLm0 Q hQ p0 q0 hq0 hq0Norm
  have hloadsP : c⁻¹ • p0 = alpha⁻¹ • e := by
    ext j
    simp only [p0, smul_smul, Pi.smul_apply]
    rw [← hcSq]
    field_simp [hc.ne']
  have hloadsQ : c⁻¹ • q0 = e := by
    ext j
    simp [q0, hc.ne']
  have hscale : ∀ omega : Sample d,
      cutoffResponseOnCube M L (alpha⁻¹ • e) e Q omega =
        alpha⁻¹ * cutoffResponseOnCube M L p0 q0 Q omega := by
    intro omega
    change J (Ch02.cubeDomain Q) ((aCutoffFamily M L omega).coeffOn Q)
        (alpha⁻¹ • e) e = _
    rw [← hloadsP, ← hloadsQ]
    calc
      J (Ch02.cubeDomain Q) ((aCutoffFamily M L omega).coeffOn Q)
          (c⁻¹ • p0) (c⁻¹ • q0) =
          (c⁻¹) ^ 2 * J (Ch02.cubeDomain Q)
            ((aCutoffFamily M L omega).coeffOn Q) p0 q0 :=
        Ch02.responseJ_smul c⁻¹ p0 q0
      _ = alpha⁻¹ * cutoffResponseOnCube M L p0 q0 Q omega := by
        rw [show (c⁻¹) ^ 2 = alpha⁻¹ by rw [← hcSq]; field_simp [hc.ne']]
        rfl
  have hsqEq : (fun omega : Sample d =>
      cutoffResponseOnCube M L (alpha⁻¹ • e) e Q omega ^ 2) =
      fun omega => alpha⁻¹ ^ 2 * cutoffResponseOnCube M L p0 q0 Q omega ^ 2 := by
    funext omega
    rw [hscale]
    ring
  constructor
  · rw [hsqEq]
    exact hbase.1.const_mul _
  · rw [hsqEq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hbase.2 (sq_nonneg _)

/-- The coordinate local-response family belongs to `L²`. -/
theorem coordinateLocalResponse_memLp_two
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (Q : TriadicCube d) (hQ : Q.scale = (L : ℤ)) (i : Fin d) :
    let e : Vec d := Pi.single i 1
    MemLp (cutoffResponseOnCube M L ((ahom M L)⁻¹ • e) e Q)
      2 M.P.toMeasure := by
  dsimp only
  let e : Vec d := Pi.single i 1
  let Y := cutoffResponseOnCube M L ((ahom M L)⁻¹ • e) e Q
  have hsq := coordinateLocalResponse_sq_integrable_and_integral_le
    M hxi hS hLm0 Q hQ i
  apply (memLp_two_iff_integrable_sq
    (measurable_cutoffResponseOnCube M L ((ahom M L)⁻¹ • e) e Q).aestronglyMeasurable).2
  simpa [Y, e] using! hsq.1

/-- Jensen's mean-square consequence for one coordinate local response. -/
theorem sq_integral_coordinateLocalResponse_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (Q : TriadicCube d) (hQ : Q.scale = (L : ℤ)) (i : Fin d) :
    let e : Vec d := Pi.single i 1
    (∫ omega, cutoffResponseOnCube M L ((ahom M L)⁻¹ • e) e Q omega
        ∂M.P.toMeasure) ^ 2 ≤ (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  dsimp only
  let e : Vec d := Pi.single i 1
  let Y := cutoffResponseOnCube M L ((ahom M L)⁻¹ • e) e Q
  have hmem : MemLp Y 2 M.P.toMeasure := by
    simpa [Y, e] using! coordinateLocalResponse_memLp_two M hxi hS hLm0 Q hQ i
  have hvar := ProbabilityTheory.variance_nonneg Y M.P.toMeasure
  rw [ProbabilityTheory.variance_eq_sub hmem] at hvar
  simp only [Pi.pow_apply] at hvar
  have hsecond :=
    (coordinateLocalResponse_sq_integrable_and_integral_le
      M hxi hS hLm0 Q hQ i).2
  dsimp only [Y, e] at hvar
  exact (by linarith)



theorem randomAStarInv_entry_sub_ahom_inv_memLp_two
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (i : Fin d) :
    MemLp (fun omega : Sample d =>
      (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i i -
        (ahom M L)⁻¹) 2 M.P.toMeasure := by
  have hmeas : AEStronglyMeasurable (fun omega : Sample d =>
      (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i i)
      M.P.toMeasure :=
    ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain Q)).eval i).eval i).1)
  have hraw : MemLp (fun omega : Sample d =>
      (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i i)
      2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hmeas).2
      (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain Q) i i)
  exact hraw.sub (memLp_const _)

theorem sharpResponseSup_scalarMatrix_eq_normalizedDefect_toReal
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    sharpResponseSup U (aCutoffCoeffOnData M L omega U).toCoeffOn
        (scalarMatrix (d := d) (ahom M L)) =
      (normalizedDefect M L U omega).toReal := by
  classical
  let a := (aCutoffCoeffOnData M L omega U).toCoeffOn
  let alpha := ahom M L
  let b : Mat d := scalarMatrix (d := d) alpha
  let R : Mat d := sharpResponseMatrix U a b
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  have hb : b.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (scalarMatrix_isSymm alpha) ?_
    intro x hx
    have hxpos : 0 < vecNormSq x :=
      lt_of_le_of_ne (vecNormSq_nonneg x)
        (by simpa [vecNormSq_eq_zero_iff, eq_comm] using! hx)
    change 0 < vecDot x (matVecMul b x)
    rw [show matVecMul b x = alpha • x by
      simpa [b] using! matVecMul_scalarMatrix alpha x]
    simpa [vecDot_smul_right] using! mul_pos halpha hxpos
  have hsqrt : matrixSqrt b = Real.sqrt alpha • (1 : Mat d) := by
    dsimp [matrixSqrt]
    apply CFC.sqrt_unique
    · calc
        (Real.sqrt alpha • (1 : Mat d)) *
              (Real.sqrt alpha • (1 : Mat d)) =
            (Real.sqrt alpha * Real.sqrt alpha) • ((1 : Mat d) * 1) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = alpha • (1 : Mat d) := by
          rw [one_mul, Real.mul_self_sqrt halpha.le]
        _ = b := rfl
    · rw [Matrix.nonneg_iff_posSemidef]
      exact Matrix.PosSemidef.one.smul (Real.sqrt_nonneg alpha)
  have hinvsqrt : matrixInvSqrt b =
      (Real.sqrt alpha)⁻¹ • (1 : Mat d) := by
    unfold matrixInvSqrt
    rw [show CFC.sqrt b = Real.sqrt alpha • (1 : Mat d) from hsqrt]
    rw [nonsing_inv_smul (Real.sqrt alpha)
      (Real.sqrt_ne_zero'.mpr halpha) (by simp)]
    simp
  have hquad : ∀ z : Vec d,
      J U a ((Real.sqrt alpha)⁻¹ • z) (Real.sqrt alpha • z) =
        vecDot z (matVecMul R z) := by
    intro z
    rw [← sharpResponse_quadratic U a
      (aCutoffCoeffOnData M L omega U).isSymmetric b hb z]
    rw [hsqrt, hinvsqrt, smul_matVecMul, smul_matVecMul]
    rw [show matVecMul (1 : Mat d) z = z from Matrix.one_mulVec z]
  have hR : R.PosSemidef :=
    sharpResponseMatrix_posSemidef U a
      (aCutoffCoeffOnData M L omega U).isSymmetric b
  have hpaper : paperScalarProbeMaxOn U a alpha =
      ENNReal.ofReal (Ch02.matrixOperatorNorm R) :=
    paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm U a alpha R hR hquad
  calc
    sharpResponseSup U a b = sharpResponseMax U a b :=
      sharpResponseSup_eq_max U a
        (aCutoffCoeffOnData M L omega U).isSymmetric b hb
    _ = Ch02.matrixOperatorNorm R := rfl
    _ = (ENNReal.ofReal (Ch02.matrixOperatorNorm R)).toReal := by
      rw [ENNReal.toReal_ofReal (Ch02.matrixOperatorNorm_nonneg R)]
    _ = (paperScalarProbeMaxOn U a alpha).toReal := by rw [hpaper]
    _ = (normalizedDefect M L U omega).toReal := rfl

/-- Pointwise dual-entry consequence of `l.sharp.compare.J`.  The explicit
constant `10` is the one in the landed deterministic comparison. -/
theorem sq_abs_randomAStarInv_entry_sub_ahom_inv_le_normalizedDefect
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (omega : Sample d) (i : Fin d) :
    |(randomAStarMatrix M L U omega)⁻¹ i i - (ahom M L)⁻¹| ^ 2 ≤
      10 * (ahom M L)⁻¹ ^ 2 *
        (normalizedDefect M L U omega).toReal *
          (1 + (normalizedDefect M L U omega).toReal) := by
  classical
  let a := (aCutoffCoeffOnData M L omega U).toCoeffOn
  let alpha := ahom M L
  let b : Mat d := scalarMatrix (d := d) alpha
  let Astar := aStarMatrix U a
  let H := sharpResponseSup U a b
  let D := (normalizedDefect M L U omega).toReal
  have halpha : 0 < alpha := by simpa [alpha] using! ahom_pos M L
  have hb : b.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (scalarMatrix_isSymm alpha) ?_
    intro x hx
    have hxpos : 0 < vecNormSq x :=
      lt_of_le_of_ne (vecNormSq_nonneg x)
        (by simpa [vecNormSq_eq_zero_iff, eq_comm] using! hx)
    change 0 < vecDot x (matVecMul b x)
    rw [show matVecMul b x = alpha • x by
      simpa [b] using! matVecMul_scalarMatrix alpha x]
    simpa [vecDot_smul_right] using! mul_pos halpha hxpos
  have hsqrt : matrixSqrt b = Real.sqrt alpha • (1 : Mat d) := by
    dsimp [matrixSqrt]
    apply CFC.sqrt_unique
    · calc
        (Real.sqrt alpha • (1 : Mat d)) *
              (Real.sqrt alpha • (1 : Mat d)) =
            (Real.sqrt alpha * Real.sqrt alpha) • ((1 : Mat d) * 1) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = alpha • (1 : Mat d) := by
          rw [one_mul, Real.mul_self_sqrt halpha.le]
        _ = b := rfl
    · rw [Matrix.nonneg_iff_posSemidef]
      exact Matrix.PosSemidef.one.smul (Real.sqrt_nonneg alpha)
  have hmatrix : matrixSqrt b * Astar⁻¹ * matrixSqrt b - 1 =
      alpha • Astar⁻¹ - 1 := by
    rw [hsqrt, Matrix.smul_mul, Matrix.mul_smul]
    simp only [one_mul, mul_one]
    rw [smul_smul, Real.mul_self_sqrt halpha.le]
  have hdev := sharpCompareJ_matrix_deviations U a
    (aCutoffCoeffOnData M L omega U).isSymmetric b hb
  have hterm : Ch02.matrixOperatorNorm (alpha • Astar⁻¹ - 1) ^ 2 ≤
      10 * H * (1 + H) := by
    rw [hmatrix] at hdev
    have hfirst : 0 ≤ Ch02.matrixOperatorNorm
        (matrixInvSqrt b * (aMatrix U a - Astar) * matrixInvSqrt b) :=
      Ch02.matrixOperatorNorm_nonneg _
    have hthird : 0 ≤ Ch02.matrixOperatorNorm
        (matrixInvSqrt b * aMatrix U a * matrixInvSqrt b - 1) ^ 2 := sq_nonneg _
    linarith
  have hHD : H = D := by
    simpa [H, D, a, b, alpha] using
      sharpResponseSup_scalarMatrix_eq_normalizedDefect_toReal M L U omega
  rw [hHD] at hterm
  let Z : Mat d := alpha • Astar⁻¹ - 1
  have hentry : |Z i i| ≤ Ch02.matrixOperatorNorm Z :=
    Ch02.abs_entry_le_matrixOperatorNorm Z i i
  have hentryEq : (Astar⁻¹ i i - alpha⁻¹) = alpha⁻¹ * Z i i := by
    dsimp only [Z]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      ite_true]
    field_simp [halpha.ne']
  have hsqEntry : |Astar⁻¹ i i - alpha⁻¹| ^ 2 ≤
      alpha⁻¹ ^ 2 * Ch02.matrixOperatorNorm Z ^ 2 := by
    rw [hentryEq, abs_mul, abs_of_nonneg (inv_nonneg.mpr halpha.le), mul_pow]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (abs_nonneg _) (Ch02.matrixOperatorNorm_nonneg Z)).2 hentry)
      (sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hterm (sq_nonneg alpha⁻¹)
  have hrandom : (randomAStarMatrix M L U omega)⁻¹ = Astar⁻¹ := rfl
  rw [hrandom]
  dsimp only [D, alpha] at hsqEntry hscaled ⊢
  nlinarith

/-- The centered inverse-star coordinate has the `C ahom⁻² delta₁`
second moment used in Step 3.  Here the explicit admissible constant inherited
from `sharpCompareJ_matrix_deviations` is `20`. -/
theorem randomAStarInv_entry_sub_ahom_inv_integral_sq_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (Q : TriadicCube d) (hQ : Q.scale = (L : ℤ)) (i : Fin d) :
    ∫ omega,
        ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i i -
          (ahom M L)⁻¹) ^ 2 ∂M.P.toMeasure ≤
      20 * (ahom M L)⁻¹ ^ 2 * delta1 := by
  let U := Ch02.cubeDomain Q
  let D : Sample d → ℝ := fun omega =>
    (normalizedDefect M L U omega).toReal
  let Y : Sample d → ℝ := fun omega =>
    (randomAStarMatrix M L U omega)⁻¹ i i - (ahom M L)⁻¹
  have hD := normalizedDefect_toReal_moment_budgets
    M hxi hS le_rfl hLm0 Q hQ
  have hDmem : MemLp D 2 M.P.toMeasure := by simpa [D, U] using! hD.1
  have hDint : Integrable D M.P.toMeasure := hDmem.integrable one_le_two
  have hDsq : Integrable (fun omega => D omega ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hDmem.aestronglyMeasurable).1 hDmem
  have hYmem : MemLp Y 2 M.P.toMeasure := by
    simpa [Y, U] using! randomAStarInv_entry_sub_ahom_inv_memLp_two M L Q i
  have hYsq : Integrable (fun omega => Y omega ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hYmem.aestronglyMeasurable).1 hYmem
  have hRhs : Integrable (fun omega =>
      10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega)) M.P.toMeasure := by
    have heq : (fun omega =>
        10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega)) =
        fun omega => 10 * (ahom M L)⁻¹ ^ 2 * (D omega + D omega ^ 2) := by
      funext omega
      ring
    rw [heq]
    exact (hDint.add hDsq).const_mul _
  have hpoint : ∀ omega, Y omega ^ 2 ≤
      10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega) := by
    intro omega
    simpa [Y, D, U, sq_abs] using
      sq_abs_randomAStarInv_entry_sub_ahom_inv_le_normalizedDefect
        M L U omega i
  have hraw : ∫ omega, Y omega ^ 2 ∂M.P.toMeasure ≤
      ∫ omega, 10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega)
        ∂M.P.toMeasure := integral_mono hYsq hRhs hpoint
  have hDfirst : ∫ omega, D omega ∂M.P.toMeasure ≤ delta1 := by
    simpa [D, U] using! hD.2.1
  have hDsecond : ∫ omega, D omega ^ 2 ∂M.P.toMeasure ≤ delta1 ^ 2 := by
    simpa [D, U] using! hD.2.2
  have hraw' : ∫ omega, Y omega ^ 2 ∂M.P.toMeasure ≤
      10 * (ahom M L)⁻¹ ^ 2 *
        ((∫ omega, D omega ∂M.P.toMeasure) +
          ∫ omega, D omega ^ 2 ∂M.P.toMeasure) := by
    calc
      ∫ omega, Y omega ^ 2 ∂M.P.toMeasure ≤
          ∫ omega, 10 * (ahom M L)⁻¹ ^ 2 * D omega * (1 + D omega)
            ∂M.P.toMeasure := hraw
      _ = 10 * (ahom M L)⁻¹ ^ 2 *
          ((∫ omega, D omega ∂M.P.toMeasure) +
            ∫ omega, D omega ^ 2 ∂M.P.toMeasure) := by
        simp_rw [show ∀ omega, 10 * (ahom M L)⁻¹ ^ 2 * D omega *
            (1 + D omega) = 10 * (ahom M L)⁻¹ ^ 2 *
              (D omega + D omega ^ 2) by intro; ring]
        rw [integral_const_mul, integral_add hDint hDsq]
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  have hdeltaSq : delta1 ^ 2 ≤ delta1 := by
    nlinarith [hS.2.2.1.le]
  have hinv0 : 0 ≤ (ahom M L)⁻¹ ^ 2 := sq_nonneg _
  dsimp only [Y, U] at hraw' ⊢
  calc
    _ ≤ 10 * (ahom M L)⁻¹ ^ 2 * (delta1 + delta1 ^ 2) := by
      exact hraw'.trans (mul_le_mul_of_nonneg_left
        (add_le_add hDfirst hDsecond) (mul_nonneg (by norm_num) hinv0))
    _ ≤ 20 * (ahom M L)⁻¹ ^ 2 * delta1 := by
      nlinarith

/-! ## Direct extraction from the proved multiscale-response anchor -/

/-- The scale-zero term of the finite-`r = 2` homogenization error contains
the normalized defect, multiplied by the strictly positive geometric
discount. -/
theorem geometricDiscount_mul_normalizedDefect_le_multiscaleError_sq
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ)
    (omega : Sample d) :
    ENNReal.ofReal (Ch02.geometricDiscount (1 / 4 : ℝ) 2) *
        normalizedDefect M L (Ch02.cubeDomain (originCube d (K : ℤ))) omega ≤
      translatedHomogenizationErrorRandom M L K 0 (1 / 4) 2 omega ^ 2 := by
  let Q := originCube d (K : ℤ)
  let a := aCutoffFamily M L omega
  let F : ℕ → ℝ≥0∞ := fun l =>
    ENNReal.ofReal (Ch02.geometricWeight (1 / 4 : ℝ) 2 l) *
      (paperScaleResponseAtScale Q ((K : ℤ) - (l : ℤ)) .infinity a
        (ahom M L)) ^ (2 : ℝ)
  have htranslate : translatePotentialSample (0 : Vec d) omega = omega := by
    funext k
    apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
    intro x
    change omega k (x + 0) = omega k x
    rw [add_zero]
  have hroot :
      (normalizedDefect M L (Ch02.cubeDomain Q) omega) ^ (1 / 2 : ℝ) ≤
        paperScaleResponseAtScale Q (K : ℤ) .infinity a (ahom M L) := by
    rw [paperScaleResponseAtScale_infinity_eq_largeCubeScaleMaximum M L K
      (by simp) omega]
    rw [largeCubeScaleMaximum, dif_pos (by simp)]
    apply le_iSup_of_le
      (⟨Q, by
        rw [show (K : ℤ) = Q.scale by rfl,
          Homogenization.descendantsAtScale_self]
        simp⟩ : {R : TriadicCube d // R ∈ descendantsAtScale Q (K : ℤ)})
    rfl
  have hdefect : normalizedDefect M L (Ch02.cubeDomain Q) omega ≤
      (paperScaleResponseAtScale Q (K : ℤ) .infinity a (ahom M L)) ^
        (2 : ℝ) := by
    calc
      normalizedDefect M L (Ch02.cubeDomain Q) omega =
          ((normalizedDefect M L (Ch02.cubeDomain Q) omega) ^ (1 / 2 : ℝ)) ^
            (2 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow hroot (by norm_num)
  have hzero :
      ENNReal.ofReal (Ch02.geometricDiscount (1 / 4 : ℝ) 2) *
          normalizedDefect M L (Ch02.cubeDomain Q) omega ≤ F 0 := by
    have hweight : Ch02.geometricWeight (1 / 4 : ℝ) 2 0 =
        Ch02.geometricDiscount (1 / 4 : ℝ) 2 := by
      unfold Ch02.geometricWeight
      norm_num [Real.rpow_zero]
    simp only [F, Nat.cast_zero, sub_zero, hweight]
    gcongr
  have hterm : F 0 ≤ ∑' l, F l := ENNReal.le_tsum 0
  have herr : translatedHomogenizationErrorRandom M L K 0 (1 / 4) 2 omega ^ 2 =
      ∑' l, F l := by
    unfold translatedHomogenizationErrorRandom
    rw [htranslate]
    simp only [paperHomogenizationError, paperHomogenizationErrorFinite]
    change ((∑' l, F l) ^ (1 / (2 : ℝ))) ^ (2 : ℕ) = ∑' l, F l
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  exact hzero.trans (hterm.trans_eq herr.symm)

private theorem paperENNRealLpNorm_sq
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p (fun omega => X omega ^ (2 : ℕ)) =
      (paperENNRealLpNorm mu (2 * p) X) ^ (2 : ℕ) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d131_paperENNRealLpNorm_sq (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X)

/-- A multiscale-error `L^xi` bound yields a normalized-defect
`L^(xi/2)` bound. -/
theorem normalizedDefect_halfExponent_lpnorm_le_of_multiscaleError
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ)
    {xi A : ℝ} (hxi : 0 < xi) (hA : 0 ≤ A)
    (hnorm : paperENNRealLpNorm M.P.toMeasure xi
      (translatedHomogenizationErrorRandom M L K 0 (1 / 4) 2) ≤
        ENNReal.ofReal A) :
    paperENNRealLpNorm M.P.toMeasure (xi / 2)
        (normalizedDefect M L (Ch02.cubeDomain (originCube d (K : ℤ)))) ≤
      ENNReal.ofReal
        ((Ch02.geometricDiscount (1 / 4 : ℝ) 2)⁻¹ * A ^ 2) := by
  let g : ℝ := Ch02.geometricDiscount (1 / 4 : ℝ) 2
  let D : Sample d → ℝ≥0∞ :=
    normalizedDefect M L (Ch02.cubeDomain (originCube d (K : ℤ)))
  let E : Sample d → ℝ≥0∞ :=
    translatedHomogenizationErrorRandom M L K 0 (1 / 4) 2
  have hg : 0 < g := Homogenization.geometricDiscount_pos (by norm_num)
  have hgENN0 : ENNReal.ofReal g ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hg)
  have hgENNTop : ENNReal.ofReal g ≠ ∞ := ENNReal.ofReal_ne_top
  have hDmeas : Measurable D :=
    (measurable_normalizedDefect_potentialShellIndexSigma_Iic M L
      (Ch02.cubeDomain (originCube d (K : ℤ)))).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  have hhalf : 0 < xi / 2 := by positivity
  have hpoint : ∀ omega, ENNReal.ofReal g * D omega ≤ E omega ^ (2 : ℕ) := by
    intro omega
    simpa [g, D, E] using
      geometricDiscount_mul_normalizedDefect_le_multiscaleError_sq M L K omega
  have hmono := paperENNRealLpNorm_mono_ae M.P.toMeasure hhalf.le
    (Filter.Eventually.of_forall hpoint)
  rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure hhalf
    (ENNReal.ofReal g) D hDmeas,
    paperENNRealLpNorm_sq M.P.toMeasure hhalf E] at hmono
  have hxiEq : 2 * (xi / 2) = xi := by ring
  rw [hxiEq] at hmono
  have hsq := pow_le_pow_left' hnorm 2
  have hbound : ENNReal.ofReal g *
      paperENNRealLpNorm M.P.toMeasure (xi / 2) D ≤
        (ENNReal.ofReal A) ^ (2 : ℕ) := hmono.trans hsq
  calc
    paperENNRealLpNorm M.P.toMeasure (xi / 2) D =
        (ENNReal.ofReal g)⁻¹ *
          (ENNReal.ofReal g * paperENNRealLpNorm M.P.toMeasure (xi / 2) D) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hgENN0 hgENNTop, one_mul]
    _ ≤ (ENNReal.ofReal g)⁻¹ * (ENNReal.ofReal A) ^ (2 : ℕ) := by
      gcongr
    _ = ENNReal.ofReal (g⁻¹ * A ^ 2) := by
      rw [← ENNReal.ofReal_inv_of_pos hg, ← ENNReal.ofReal_pow hA,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hg.le)]
    _ = _ := rfl

/-- Source-regime normalized-defect budget obtained by applying the proved
large-cube anchor at `s = 1/4`, `r = 2`. -/
theorem normalizedDefect_halfExponent_lpnorm_budget_of_multiscaleResponseLargeCubes
    {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m0 K : ℕ)
        (delta1 xi : ℝ),
        M.delta ^ 2 ≤ delta1 → delta1 < 1 → L ≤ m0 → L ≤ K →
        16 * (d : ℝ) ≤ xi →
        xi ≤ c * (1 / 4 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 xi delta1 →
        paperENNRealLpNorm M.P.toMeasure (xi / 2)
            (normalizedDefect M L
              (Ch02.cubeDomain (originCube d (K : ℤ)))) ≤
          ENNReal.ofReal (C * delta1) := by
  rcases SubdiffusiveProcess.Frozen.Section4.multiscale_response_large_cubes (d := d) with
    ⟨c0, C0, hc0, hC0, hlarge⟩
  let g : ℝ := Ch02.geometricDiscount (1 / 4 : ℝ) 2
  let b : ℝ := C0 * Real.rpow (1 / 4 : ℝ) (-(1 / (2 : ℝ)))
  let C : ℝ := g⁻¹ * b ^ 2
  have hg : 0 < g := Homogenization.geometricDiscount_pos (by norm_num)
  have hb : 0 < b := by
    dsimp only [b]
    exact mul_pos hC0 (Real.rpow_pos_of_pos (by norm_num) _)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨c0, C, hc0, hC, ?_⟩
  intro M L m0 K delta1 xi hdelta hdelta1 hLm0 hLK hxi hupper hS
  have hdelta0 : 0 ≤ delta1 := (sq_nonneg M.delta).trans hdelta
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
  have hxiPos : 0 < xi := by nlinarith [hxi]
  have hdim : 4 * (d : ℝ) * (1 / 4 : ℝ)⁻¹ ≤ xi := by
    convert hxi using 1
    norm_num
    ring
  have hnorm := hlarge M L m0 (1 / 4) delta1 xi
    (by norm_num) (by norm_num) hdelta hdelta1 hLm0 hdim hupper hS
    K hLK 0 (2 : ℕ) (Or.inr rfl)
  let A : ℝ := C0 * Real.rpow (1 / 4 : ℝ) (-(1 / (2 : ℝ))) *
    Real.sqrt delta1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hD := normalizedDefect_halfExponent_lpnorm_le_of_multiscaleError
    M L K hxiPos hA (by simpa [A] using! hnorm)
  refine hD.trans (ENNReal.ofReal_le_ofReal ?_)
  dsimp only [C, b, g, A]
  rw [mul_pow, Real.sq_sqrt hdelta0]
  ring_nf
  exact le_rfl

/-- The unrestricted response-square budget extracted directly from the
proved `l.multiscale.response.large.cubes` anchor. -/
theorem cutoffResponseOnCube_sq_budget_of_multiscaleResponseLargeCubes
    {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m0 K : ℕ)
        (delta1 xi : ℝ),
        M.delta ^ 2 ≤ delta1 → delta1 < 1 → L ≤ m0 → L ≤ K →
        16 * (d : ℝ) ≤ xi →
        xi ≤ c * (1 / 4 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 xi delta1 →
        ∀ p q : Vec d, q = ahom M L • p → vecNormSq q ≤ ahom M L →
          Integrable (fun omega : Sample d =>
            cutoffResponseOnCube M L p q (originCube d (K : ℤ)) omega ^ 2)
              M.P.toMeasure ∧
          ∫ omega, cutoffResponseOnCube M L p q
              (originCube d (K : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤
            C ^ 2 * delta1 ^ 2 := by
  rcases
      normalizedDefect_halfExponent_lpnorm_budget_of_multiscaleResponseLargeCubes
        (d := d) with ⟨c, C, hc, hC, hbudget⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro M L m0 K delta1 xi hdelta hdelta1 hLm0 hLK hxi hupper hS
    p q hq hqNorm
  letI : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  let U := Ch02.cubeDomain (originCube d (K : ℤ))
  let X : Sample d → ℝ≥0∞ := normalizedDefect M L U
  let D : Sample d → ℝ := fun omega => (X omega).toReal
  let Y : Sample d → ℝ := cutoffResponseOnCube M L p q (originCube d (K : ℤ))
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hxi4 : 4 ≤ xi := by linarith [hxi, hd1]
  have hhalfPos : 0 < xi / 2 := by linarith
  have hdelta0 : 0 ≤ delta1 := (sq_nonneg M.delta).trans hdelta
  have hXmeas : Measurable X :=
    (measurable_normalizedDefect_potentialShellIndexSigma_Iic M L U).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  have hXtop : ∀ omega, X omega ≠ ∞ := fun omega => by
    simpa [X, U] using! normalizedDefect_ne_top M L U omega
  have hXhalf : paperENNRealLpNorm M.P.toMeasure (xi / 2) X ≤
      ENNReal.ofReal (C * delta1) := by
    simpa [X, U] using! hbudget M L m0 K delta1 xi hdelta hdelta1
      hLm0 hLK hxi hupper hS
  have hDhalf : eLpNorm D (ENNReal.ofReal (xi / 2)) M.P.toMeasure ≤
      ENNReal.ofReal (C * delta1) := by
    rw [← paperENNRealLpNorm_eq_guarded_eLpNorm_toReal M.P.toMeasure hhalfPos hXtop hXmeas.ennreal_toReal.aestronglyMeasurable]
    exact hXhalf
  have htwoHalf : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (xi / 2) := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hDtwo : eLpNorm D 2 M.P.toMeasure ≤ ENNReal.ofReal (C * delta1) :=
    (eLpNorm_le_eLpNorm_of_exponent_le htwoHalf).trans hDhalf
  have hDmem : MemLp D 2 M.P.toMeasure :=
    hDtwo.trans_lt ENNReal.ofReal_lt_top
  have hYmeas : AEStronglyMeasurable Y M.P.toMeasure :=
    (measurable_cutoffResponseOnCube M L p q
      (originCube d (K : ℤ))).aestronglyMeasurable
  have hYnonneg : ∀ omega, 0 ≤ Y omega := fun omega =>
    Ch02.responseJ_nonneg U
      (aCutoffCoeffOnData M L omega U).toCoeffOn p q
  have hYD : ∀ omega, Y omega ≤ D omega := fun omega => by
    simpa [Y, D, X, U] using
      cutoffResponseOnCube_le_normalizedDefect_toReal_of_headline_load
        M L (originCube d (K : ℤ)) p q hq hqNorm omega
  have hYmem : MemLp Y 2 M.P.toMeasure :=
    hDmem.mono' hYmeas (Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg omega)]
      exact hYD omega)
  have hYnorm : eLpNorm Y 2 M.P.toMeasure ≤ ENNReal.ofReal (C * delta1) :=
    (eLpNorm_mono_ae hYmeas (Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg omega),
        Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact hYD omega)).trans hDtwo
  have hCdelta : 0 ≤ C * delta1 := mul_nonneg hC.le hdelta0
  have hYreal : (eLpNorm Y 2 M.P.toMeasure).toReal ≤ C * delta1 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hYnorm
    simpa [ENNReal.toReal_ofReal hCdelta] using! h
  have hsq : Integrable (fun omega => Y omega ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hYmeas).1 hYmem
  refine ⟨by simpa [Y] using! hsq, ?_⟩
  rw [← Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hYmem]
  calc
    (eLpNorm Y 2 M.P.toMeasure).toReal ^ 2 ≤ (C * delta1) ^ 2 :=
      (sq_le_sq₀ (by positivity) hCdelta).2 hYreal
    _ = C ^ 2 * delta1 ^ 2 := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
