import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.NormalizedCutoffLaw
import SubdiffusiveProcess.Providers.Section2.GeneralCoarseGraining




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- A.e.-symmetric coefficient fields agree a.e. with their transpose. -/
theorem coeffOn_transpose_aeeq_self_of_symmetric
    {U : Ch02.Domain d} {a : Ch02.CoeffOn U} (ha : a.IsSymmetric) :
    Ch02.CoeffOn.AEEq a.transpose a := by
  filter_upwards [ha] with x hx
  exact hx

/-- The constant block matrix of a positive scalar matrix sends the first-block
probe `((sqrt alpha)⁻¹ • v, 0)` to `(sqrt alpha • v, 0)`.  General-`v` form of
the coordinate-probe computation in CoarseGraining. -/
theorem blockMatVecMul_constantBlockMatrix_scalarMatrix_firstBlock
    {alpha : ℝ} (halpha : 0 < alpha) (v : Vec d) :
    blockMatVecMul (Ch02.constantBlockMatrix (scalarMatrix (d := d) alpha))
        ((Real.sqrt alpha)⁻¹ • v, 0) =
      (Real.sqrt alpha • v, 0) := by
  have hsqrt : 0 < Real.sqrt alpha := Real.sqrt_pos.2 halpha
  have hself : Real.sqrt alpha * Real.sqrt alpha = alpha :=
    Real.mul_self_sqrt halpha.le
  have hcoef : alpha * (Real.sqrt alpha)⁻¹ = Real.sqrt alpha := by
    have hstep : alpha * (Real.sqrt alpha)⁻¹ =
        Real.sqrt alpha * Real.sqrt alpha * (Real.sqrt alpha)⁻¹ := by
      rw [hself]
    rw [hstep, mul_assoc, mul_inv_cancel₀ hsqrt.ne', mul_one]
  rw [Ch02.constantBlockMatrix_scalarMatrix halpha]
  ext k
  · simp only [blockMatVecMul, matVecMul_zero, matVecMul_scalarMatrix,
      add_zero, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hcoef]
  · simp [blockMatVecMul, matVecMul, matVecMul_scalarMatrix]

/-- The first-block probe has unit constant-block quadratic form exactly when
`v` is a unit vector. -/
theorem firstBlockProbe_constantBlockQuadratic_eq_one
    {alpha : ℝ} (halpha : 0 < alpha) {v : Vec d} (hv : vecNormSq v = 1) :
    blockVecDot ((Real.sqrt alpha)⁻¹ • v, 0)
        (blockMatVecMul (Ch02.constantBlockMatrix (scalarMatrix (d := d) alpha))
          ((Real.sqrt alpha)⁻¹ • v, 0)) = 1 := by
  have hsqrt : 0 < Real.sqrt alpha := Real.sqrt_pos.2 halpha
  rw [blockMatVecMul_constantBlockMatrix_scalarMatrix_firstBlock halpha v]
  rw [blockVecDot, vecDot_smul_left, vecDot_smul_right]
  have hv' : vecDot v v = 1 := hv
  rw [hv']
  simp [vecDot]
  field_simp

/-- **The first-block embedding.**  The paper's scalar probe is the Chapter 2
doubled probe at the first-block vector, for a.e.-symmetric coefficients. -/
theorem paperScalarProbe_eq_doubledResponseJ_firstBlock
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (ha : (a.coeffOn Q).IsSymmetric) (alpha : ℝ) (v : Vec d) :
    paperScalarProbe Q a alpha v =
      Ch02.doubledResponseJ (Ch02.cubeDomain Q) (a.coeffOn Q)
        ((Real.sqrt alpha)⁻¹ • v, 0) (Real.sqrt alpha • v, 0) := by
  have hsplit :=
    Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum
      (Ch02.cubeDomain Q) (a.coeffOn Q)
      ((Real.sqrt alpha)⁻¹ • v) (0 : Vec d) (0 : Vec d) (Real.sqrt alpha • v)
  have htranspose : Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q).transpose
      ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) =
      Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q)
        ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) :=
    Ch02.responseJ_eq_ofAEEq (coeffOn_transpose_aeeq_self_of_symmetric ha) _ _
  rw [paperScalarProbe]
  rw [hsplit]
  simp only [sub_zero, add_zero, zero_add]
  rw [htranspose]
  show Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q)
      ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) = _
  ring

/-- **P-c, probe level.**  Every paper probe value is dominated by the Chapter 2
normalized block response maximum. -/
theorem paperScalarProbe_le_normalizedBlockResponseMax
    (Q : TriadicCube d) [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (ha : (a.coeffOn Q).IsSymmetric) {alpha : ℝ} (halpha : 0 < alpha)
    {v : Vec d} (hv : vecNormSq v = 1) :
    paperScalarProbe Q a alpha v ≤
      Ch02.normalizedBlockResponseMax Q a (scalarMatrix (d := d) alpha) := by
  rw [paperScalarProbe_eq_doubledResponseJ_firstBlock Q a ha alpha v]
  have hmem0 :=
    Ch02.normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
      (Q := Q) (a := a) (a0 := scalarMatrix (d := d) alpha)
      (lam := alpha) (Lam := alpha) (isEllipticMatrix_scalarMatrix halpha)
      ((Real.sqrt alpha)⁻¹ • v, 0)
      (firstBlockProbe_constantBlockQuadratic_eq_one halpha hv)
  have hmem :
      Ch02.doubledResponseJ (Ch02.cubeDomain Q) (a.coeffOn Q)
          ((Real.sqrt alpha)⁻¹ • v, 0) (Real.sqrt alpha • v, 0) ∈
        Ch02.normalizedBlockResponseValueSet Q a
          (scalarMatrix (d := d) alpha) := by
    simpa [blockMatVecMul_constantBlockMatrix_scalarMatrix_firstBlock
      halpha v] using hmem0
  unfold Ch02.normalizedBlockResponseMax
  exact le_csSup
    (Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (a := a) (Q := Q) (R := Q) (k := Q.scale) (scalarMatrix (d := d) alpha)
      (by simp [descendantsAtScale_self])) hmem

/-- **P-c, probe-maximum level.**  The paper probe maximum is dominated by the
Chapter 2 normalized block response maximum. -/
theorem paperScalarProbeMax_le_ofReal_normalizedBlockResponseMax
    (Q : TriadicCube d) [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (ha : (a.coeffOn Q).IsSymmetric) {alpha : ℝ} (halpha : 0 < alpha) :
    paperScalarProbeMax Q a alpha ≤
      ENNReal.ofReal
        (Ch02.normalizedBlockResponseMax Q a (scalarMatrix (d := d) alpha)) := by
  rw [paperScalarProbeMax]
  refine iSup_le ?_
  rintro ⟨v, hv⟩
  exact ENNReal.ofReal_le_ofReal
    (paperScalarProbe_le_normalizedBlockResponseMax Q a ha halpha hv)

/-- **The two probe maxima agree.**

Combining P-c with the existing reverse comparison
`SubdiffusiveProcess.Providers.Section2.normalizedBlockResponseMax_le_paperScalarProbeMax`:
for a.e.-symmetric coefficients and a positive scalar normalizer, the paper's
scalar probe family and Chapter 2's doubled block probe family have the same
supremum.  The two renderings of Definition `d.mathcal.E` therefore agree at
the level where they were designed to differ. -/
theorem paperScalarProbeMax_eq_ofReal_normalizedBlockResponseMax
    (Q : TriadicCube d) [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (ha : (a.coeffOn Q).IsSymmetric) {alpha : ℝ} (halpha : 0 < alpha) :
    paperScalarProbeMax Q a alpha =
      ENNReal.ofReal
        (Ch02.normalizedBlockResponseMax Q a (scalarMatrix (d := d) alpha)) :=
  le_antisymm
    (paperScalarProbeMax_le_ofReal_normalizedBlockResponseMax Q a ha halpha)
    (SubdiffusiveProcess.Providers.Section2.normalizedBlockResponseMax_le_paperScalarProbeMax
      Q a ha halpha)

/-- **P-c, descendant-maximum level.**  The paper's maximum over descendants at
one scale is dominated by Chapter 2's. -/
theorem paperMaxDescendantProbeAtScale_le_ofReal
    (Q : TriadicCube d) [NeZero d] (k : ℤ) (a : Ch02.TriadicCoeffFamily d)
    (ha : ∀ R : TriadicCube d, (a.coeffOn R).IsSymmetric)
    {alpha : ℝ} (halpha : 0 < alpha) :
    paperMaxDescendantProbeAtScale Q k a alpha ≤
      ENNReal.ofReal
        (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
          (scalarMatrix (d := d) alpha)) := by
  have hbdd : BddAbove
      ((fun R : TriadicCube d =>
        Ch02.normalizedBlockResponseMax R a (scalarMatrix (d := d) alpha)) ''
          ((descendantsAtScale Q k : Finset (TriadicCube d)) : Set (TriadicCube d))) :=
    ((descendantsAtScale Q k).finite_toSet.image _).bddAbove
  rw [paperMaxDescendantProbeAtScale]
  refine iSup_le ?_
  rintro ⟨R, hR⟩
  rw [paperScalarProbeMax_eq_ofReal_normalizedBlockResponseMax R a (ha R) halpha]
  refine ENNReal.ofReal_le_ofReal ?_
  exact le_csSup hbdd ⟨R, hR, rfl⟩

/-- **P-c, scale-response level at `p = infinity`** — the aggregation the
Dirichlet adapter uses. -/
theorem paperScaleResponseAtScale_infinity_le_ofReal
    (Q : TriadicCube d) [NeZero d] {k : ℤ} (hk : k ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d)
    (ha : ∀ R : TriadicCube d, (a.coeffOn R).IsSymmetric)
    {alpha : ℝ} (halpha : 0 < alpha) :
    paperScaleResponseAtScale Q k .infinity a alpha ≤
      ENNReal.ofReal
        (Ch02.scaleResponseAtScale Q k .infinity a
          (scalarMatrix (d := d) alpha)) := by
  have hnonneg : 0 ≤ Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
      (scalarMatrix (d := d) alpha) :=
    Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk a _
  have hbase := paperMaxDescendantProbeAtScale_le_ofReal Q k a ha halpha
  have hrpow := ENNReal.rpow_le_rpow hbase (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [paperScaleResponseAtScale, Ch02.scaleResponseAtScale]
  refine le_trans hrpow (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hnonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rfl

theorem geometricWeight_nonneg_of_nonneg {s q : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q)
    (l : ℕ) : 0 ≤ Ch02.geometricWeight s q l := by
  have hdisc : 0 ≤ Ch02.geometricDiscount s q := by
    rw [Ch02.geometricDiscount, sub_nonneg]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by nlinarith [mul_nonneg hs hq])
  have hpow : 0 ≤ Real.rpow (3 : ℝ) (-s * q * (l : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [Ch02.geometricWeight]
  exact mul_nonneg hdisc hpow

/-- **P-c, carrier level at `p = infinity`, finite `q`.**

The full comparison the Dirichlet adapter needs: the paper homogenization error
is dominated by the Chapter 2 one.  The `Summable` hypothesis is genuine
content, not a defect: the Chapter 2 carrier lives in `ℝ`, where a divergent
series takes the junk value `0`, so the transfer is only valid where the
Chapter 2 quantity is a real sum.  Any concrete supply provides it, since it
bounds that series. -/
theorem paperHomogenizationError_le_ofReal_finite
    (Q : TriadicCube d) [NeZero d] {n : ℤ} (hn : n ≤ Q.scale)
    {s q : ℝ} (hs : 0 ≤ s) (hq : 0 < q)
    (a : Ch02.TriadicCoeffFamily d)
    (ha : ∀ R : TriadicCube d, (a.coeffOn R).IsSymmetric)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hsum : Summable fun l : ℕ =>
      Ch02.geometricWeight s q l *
        Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity a
          (scalarMatrix (d := d) alpha)) q) :
    paperHomogenizationError Q n s .infinity (.finite q) a alpha ≤
      ENNReal.ofReal
        (Ch02.HomogenizationError Q n s .infinity (.finite q) a
          (scalarMatrix (d := d) alpha)) := by
  have hTnonneg : ∀ l : ℕ,
      0 ≤ Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity a
        (scalarMatrix (d := d) alpha) := by
    intro l
    rw [Ch02.scaleResponseAtScale]
    exact Real.rpow_nonneg
      (Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        (by omega : n - (l : ℤ) ≤ Q.scale) a _) _
  have hterm : ∀ l : ℕ,
      0 ≤ Ch02.geometricWeight s q l *
        Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity a
          (scalarMatrix (d := d) alpha)) q := fun l =>
    mul_nonneg (geometricWeight_nonneg_of_nonneg hs hq.le l)
      (Real.rpow_nonneg (hTnonneg l) _)
  have hpointwise : ∀ l : ℕ,
      ENNReal.ofReal (Ch02.geometricWeight s q l) *
          paperScaleResponseAtScale Q (n - (l : ℤ)) .infinity a alpha ^ q ≤
        ENNReal.ofReal (Ch02.geometricWeight s q l *
          Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity a
            (scalarMatrix (d := d) alpha)) q) := by
    intro l
    have hscale := paperScaleResponseAtScale_infinity_le_ofReal Q
      (by omega : n - (l : ℤ) ≤ Q.scale) a ha halpha
    have hpow := ENNReal.rpow_le_rpow hscale hq.le
    have hconv :
        ENNReal.ofReal (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity a
            (scalarMatrix (d := d) alpha)) ^ q =
          ENNReal.ofReal (Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ))
            .infinity a (scalarMatrix (d := d) alpha)) q) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (hTnonneg l) hq.le]
      rfl
    rw [hconv] at hpow
    rw [ENNReal.ofReal_mul (geometricWeight_nonneg_of_nonneg hs hq.le l)]
    gcongr
  have hsumle :
      (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s q l) *
          paperScaleResponseAtScale Q (n - (l : ℤ)) .infinity a alpha ^ q) ≤
        ENNReal.ofReal (∑' l : ℕ, Ch02.geometricWeight s q l *
          Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity a
            (scalarMatrix (d := d) alpha)) q) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hterm hsum]
    exact ENNReal.tsum_le_tsum hpointwise
  have houter := ENNReal.rpow_le_rpow hsumle
    (by positivity : (0 : ℝ) ≤ 1 / q)
  rw [paperHomogenizationError, paperHomogenizationErrorFinite,
    Ch02.HomogenizationError, Ch02.HomogenizationErrorFinite]
  refine le_trans houter (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg hterm)
    (by positivity : (0 : ℝ) ≤ 1 / q)]
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
