import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CarrierComparison
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CoarseResponseMoments

/-!
# Reducing the continuum of probe directions to a finite family

Every estimate on the Chapter 2 carrier has to control
`Ch02.normalizedBlockResponseMax`, a supremum over the **unit sphere** of
`FullBlockVec d`.  Concentration, by contrast, is only available for a *fixed*
probe pair through `cutoffResponseOnCube`.  This file closes that gap for the
GMC cutoff field, with no direction net and no `epsilon`-argument:

* by `cutoffResponseJ_eq_randomMatrixQuadratics` the normalized scalar probe
  `v ↦ J(R; (sqrt alpha)⁻¹ v, sqrt alpha v)` is an exact **quadratic form**
  `v ↦ ∑ i, ∑ j, P i j * (v i * v j)` in `v`, with
  `P = ½ alpha⁻¹ A + ½ alpha (A^*)⁻¹ - 1`;
* the symmetrized entries of `P` are recovered by **polarization** from the
  `d + d^2` probe values at `e i` and `e i + e j`;
* since `Ch02.responseJ` is unconditionally nonnegative, every polarization
  difference is dominated by a positive combination of probe values.

Hence the supremum over the unit sphere is dominated by an explicit finite sum
of `cutoffResponseOnCube` values, which is exactly the shape the union bound of
`UnionBound.lean` and the moment bounds of `CoarseResponseMoments.lean` /
`ResponseStationarity.lean` consume.

Everything here is unconditional: no ellipticity record, no law hypothesis, no
`DRAFT_SORRY` conclusion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The probe form and its matrix -/

/-- The paper's `alpha`-normalized scalar probe of the cutoff response, as a
function of the probe direction. -/
def cutoffProbeForm (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (v : Vec d) : ℝ :=
  cutoffResponseOnCube M L ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) R omega

theorem cutoffProbeForm_eq_paperScalarProbe
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (v : Vec d) :
    cutoffProbeForm M L alpha R omega v =
      paperScalarProbe R (aCutoffFamily M L omega) alpha v := rfl

/-- The probe form is nonnegative: it is a value of `Ch02.responseJ`. -/
theorem cutoffProbeForm_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (alpha : ℝ) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (v : Vec d) :
    0 ≤ cutoffProbeForm M L alpha R omega v :=
  Ch02.responseJ_nonneg _ _ _ _

/-- The matrix of the probe form: `½ alpha⁻¹ A + ½ alpha (A^*)⁻¹ - Id`. -/
def cutoffProbeEntry (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (i j : Fin d) : ℝ :=
  (1 / 2 : ℝ) * alpha⁻¹ * randomAMatrix M L (Ch02.cubeDomain R) omega i j +
      (1 / 2 : ℝ) * alpha *
        ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) i j -
    (if i = j then (1 : ℝ) else 0)

/-! ## Elementary bilinear algebra -/

private theorem vecDot_smul_matVecMul_smul (A : Mat d) (c : ℝ) (v : Vec d) :
    vecDot (c • v) (matVecMul A (c • v)) =
      (c * c) * ∑ i, ∑ j, A i j * (v i * v j) := by
  simp only [vecDot, matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem vecDot_smul_inv_smul {alpha : ℝ} (halpha : 0 < alpha) (v : Vec d) :
    vecDot ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) =
      ∑ i, ∑ j, (if i = j then (1 : ℝ) else 0) * (v i * v j) := by
  have hsqrt : Real.sqrt alpha ≠ 0 := (Real.sqrt_pos.2 halpha).ne'
  have hdiag : ∀ i : Fin d,
      ∑ j, (if i = j then (1 : ℝ) else 0) * (v i * v j) = v i * v i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [hdiag, vecDot, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- **The probe form is an exact quadratic form.** -/
theorem cutoffProbeForm_eq_sum (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {alpha : ℝ} (halpha : 0 < alpha) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (v : Vec d) :
    cutoffProbeForm M L alpha R omega v =
      ∑ i, ∑ j, cutoffProbeEntry M L alpha R omega i j * (v i * v j) := by
  classical
  set U := Ch02.cubeDomain R with hU
  have hsqrt : Real.sqrt alpha ≠ 0 := (Real.sqrt_pos.2 halpha).ne'
  have hinvsq : (Real.sqrt alpha)⁻¹ * (Real.sqrt alpha)⁻¹ = alpha⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt halpha.le]
  have hsq : Real.sqrt alpha * Real.sqrt alpha = alpha :=
    Real.mul_self_sqrt halpha.le
  have hJ : cutoffProbeForm M L alpha R omega v =
      (1 / 2 : ℝ) *
          vecDot ((Real.sqrt alpha)⁻¹ • v)
            (matVecMul (randomAMatrix M L U omega) ((Real.sqrt alpha)⁻¹ • v)) +
        (1 / 2 : ℝ) *
            vecDot (Real.sqrt alpha • v)
              (matVecMul ((randomAStarMatrix M L U omega)⁻¹)
                (Real.sqrt alpha • v)) -
          vecDot ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) := by
    simpa [cutoffProbeForm, cutoffResponseOnCube, aCutoffFamily,
      aCutoffTriadicData, hU] using
      cutoffResponseJ_eq_randomMatrixQuadratics M L U
        ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) omega
  rw [hJ, vecDot_smul_matVecMul_smul, vecDot_smul_matVecMul_smul,
    vecDot_smul_inv_smul halpha, hinvsq, hsq]
  have hrow : ∀ i : Fin d,
      ∑ j, cutoffProbeEntry M L alpha R omega i j * (v i * v j) =
        ((1 / 2 : ℝ) * alpha⁻¹) *
            (∑ j, randomAMatrix M L U omega i j * (v i * v j)) +
          ((1 / 2 : ℝ) * alpha) *
            (∑ j, ((randomAStarMatrix M L U omega)⁻¹) i j * (v i * v j)) -
          ∑ j, (if i = j then (1 : ℝ) else 0) * (v i * v j) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cutoffProbeEntry]
    ring
  simp only [hrow]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-! ## Polarization -/

private theorem sum_mul_single (f : Fin d → ℝ) (i : Fin d) :
    ∑ l, f l * (Pi.single i (1 : ℝ) : Vec d) l = f i := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem sum_mul_single_add (f : Fin d → ℝ) (i j : Fin d) :
    ∑ l, f l *
        (((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) l) =
      f i + f j := by
  classical
  have hsplit : ∀ l : Fin d,
      f l * (((Pi.single i (1 : ℝ) : Vec d) +
          (Pi.single j (1 : ℝ) : Vec d)) l) =
        f l * (Pi.single i (1 : ℝ) : Vec d) l +
          f l * (Pi.single j (1 : ℝ) : Vec d) l := by
    intro l
    simp [mul_add]
  simp only [hsplit, Finset.sum_add_distrib, sum_mul_single]

/-- The probe form at a coordinate direction is the diagonal entry. -/
theorem cutoffProbeForm_single (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {alpha : ℝ} (halpha : 0 < alpha) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (i : Fin d) :
    cutoffProbeForm M L alpha R omega (Pi.single i 1) =
      cutoffProbeEntry M L alpha R omega i i := by
  classical
  rw [cutoffProbeForm_eq_sum M L halpha R omega]
  have hinner : ∀ k : Fin d,
      ∑ l, cutoffProbeEntry M L alpha R omega k l *
          ((Pi.single i (1 : ℝ) : Vec d) k * (Pi.single i (1 : ℝ) : Vec d) l) =
        cutoffProbeEntry M L alpha R omega k i *
          (Pi.single i (1 : ℝ) : Vec d) k := by
    intro k
    have hrw : ∀ l : Fin d, cutoffProbeEntry M L alpha R omega k l *
        ((Pi.single i (1 : ℝ) : Vec d) k * (Pi.single i (1 : ℝ) : Vec d) l) =
        (cutoffProbeEntry M L alpha R omega k l *
          (Pi.single i (1 : ℝ) : Vec d) l) * (Pi.single i (1 : ℝ) : Vec d) k := by
      intro l; ring
    simp only [hrw, ← Finset.sum_mul,
      sum_mul_single (fun l => cutoffProbeEntry M L alpha R omega k l) i]
  simp only [hinner]
  exact sum_mul_single (fun k => cutoffProbeEntry M L alpha R omega k i) i

/-- The probe form at a sum of two coordinate directions. -/
theorem cutoffProbeForm_single_add (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : ℕ) {alpha : ℝ} (halpha : 0 < alpha) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (i j : Fin d) :
    cutoffProbeForm M L alpha R omega (Pi.single i 1 + Pi.single j 1) =
      cutoffProbeEntry M L alpha R omega i i +
        cutoffProbeEntry M L alpha R omega i j +
        cutoffProbeEntry M L alpha R omega j i +
        cutoffProbeEntry M L alpha R omega j j := by
  classical
  rw [cutoffProbeForm_eq_sum M L halpha R omega]
  have hinner : ∀ k : Fin d,
      ∑ l, cutoffProbeEntry M L alpha R omega k l *
          (((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) k *
            ((Pi.single i (1 : ℝ) : Vec d) +
              (Pi.single j (1 : ℝ) : Vec d)) l) =
        (cutoffProbeEntry M L alpha R omega k i +
            cutoffProbeEntry M L alpha R omega k j) *
          ((Pi.single i (1 : ℝ) : Vec d) +
            (Pi.single j (1 : ℝ) : Vec d)) k := by
    intro k
    have hrw : ∀ l : Fin d, cutoffProbeEntry M L alpha R omega k l *
        (((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) k *
          ((Pi.single i (1 : ℝ) : Vec d) +
            (Pi.single j (1 : ℝ) : Vec d)) l) =
        (cutoffProbeEntry M L alpha R omega k l *
            ((Pi.single i (1 : ℝ) : Vec d) +
              (Pi.single j (1 : ℝ) : Vec d)) l) *
          ((Pi.single i (1 : ℝ) : Vec d) +
            (Pi.single j (1 : ℝ) : Vec d)) k := by
      intro l; ring
    simp only [hrw, ← Finset.sum_mul,
      sum_mul_single_add (fun l => cutoffProbeEntry M L alpha R omega k l) i j]
  simp only [hinner]
  rw [sum_mul_single_add (fun k => cutoffProbeEntry M L alpha R omega k i +
    cutoffProbeEntry M L alpha R omega k j) i j]
  ring

/-- **Polarization.**  The symmetrized entries of the probe matrix are positive
combinations of the finitely many probe values. -/
theorem cutoffProbeEntry_add_swap (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : ℕ) {alpha : ℝ} (halpha : 0 < alpha) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (i j : Fin d) :
    cutoffProbeEntry M L alpha R omega i j +
        cutoffProbeEntry M L alpha R omega j i =
      cutoffProbeForm M L alpha R omega (Pi.single i 1 + Pi.single j 1) -
        cutoffProbeForm M L alpha R omega (Pi.single i 1) -
        cutoffProbeForm M L alpha R omega (Pi.single j 1) := by
  rw [cutoffProbeForm_single_add M L halpha R omega i j,
    cutoffProbeForm_single M L halpha R omega i,
    cutoffProbeForm_single M L halpha R omega j]
  ring

/-! ## The finite probe bound -/

/-- The explicit finite probe sum which dominates the whole probe sphere. -/
def finiteProbeSum (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (1 / 2 : ℝ) *
      (cutoffProbeForm M L alpha R omega (Pi.single i 1 + Pi.single j 1) +
        cutoffProbeForm M L alpha R omega (Pi.single i 1) +
        cutoffProbeForm M L alpha R omega (Pi.single j 1))

theorem finiteProbeSum_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (alpha : ℝ) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ finiteProbeSum M L alpha R omega := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have h1 := cutoffProbeForm_nonneg M L alpha R omega (Pi.single i 1 + Pi.single j 1)
  have h2 := cutoffProbeForm_nonneg M L alpha R omega (Pi.single i (1 : ℝ))
  have h3 := cutoffProbeForm_nonneg M L alpha R omega (Pi.single j (1 : ℝ))
  linarith

private theorem abs_coord_le_one {v : Vec d} (hv : vecNormSq v = 1) (i : Fin d) :
    |v i| ≤ 1 := by
  have hsum : v i * v i ≤ ∑ k, v k * v k := by
    refine Finset.single_le_sum (f := fun k => v k * v k) ?_ (Finset.mem_univ i)
    intro k _
    exact mul_self_nonneg _
  have hone : ∑ k, v k * v k = 1 := hv
  rw [hone] at hsum
  exact abs_le_one_iff_mul_self_le_one.2 hsum

/-- **The finite probe reduction.**  Every normalized probe value on the unit
sphere is dominated by the explicit finite probe sum. -/
theorem cutoffProbeForm_le_finiteProbeSum (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : ℕ) {alpha : ℝ} (halpha : 0 < alpha) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {v : Vec d} (hv : vecNormSq v = 1) :
    cutoffProbeForm M L alpha R omega v ≤ finiteProbeSum M L alpha R omega := by
  classical
  set P := cutoffProbeEntry M L alpha R omega with hP
  have hquad := cutoffProbeForm_eq_sum M L halpha R omega v
  -- symmetrize
  have hswap : ∑ i, ∑ j, P i j * (v i * v j) =
      ∑ i, ∑ j, P j i * (v i * v j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsym : ∑ i, ∑ j, P i j * (v i * v j) =
      ∑ i, ∑ j, ((1 / 2 : ℝ) * (P i j + P j i)) * (v i * v j) := by
    have h2 : (1 / 2 : ℝ) * ((∑ i, ∑ j, P i j * (v i * v j)) +
          ∑ i, ∑ j, P j i * (v i * v j)) =
        ∑ i, ∑ j, ((1 / 2 : ℝ) * (P i j + P j i)) * (v i * v j) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [← h2, ← hswap]
    ring
  rw [hquad, hsym]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hbound : ((1 / 2 : ℝ) * (P i j + P j i)) * (v i * v j) ≤
      |(1 / 2 : ℝ) * (P i j + P j i)| := by
    calc ((1 / 2 : ℝ) * (P i j + P j i)) * (v i * v j)
        ≤ |((1 / 2 : ℝ) * (P i j + P j i)) * (v i * v j)| := le_abs_self _
      _ = |(1 / 2 : ℝ) * (P i j + P j i)| * (|v i| * |v j|) := by
          rw [abs_mul ((1 / 2 : ℝ) * (P i j + P j i)) (v i * v j),
            abs_mul (v i) (v j)]
      _ ≤ |(1 / 2 : ℝ) * (P i j + P j i)| * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have h1 := abs_coord_le_one hv i
          have h2 := abs_coord_le_one hv j
          nlinarith [abs_nonneg (v i), abs_nonneg (v j)]
      _ = |(1 / 2 : ℝ) * (P i j + P j i)| := by ring
  refine hbound.trans ?_
  have hpol : P i j + P j i =
      cutoffProbeForm M L alpha R omega (Pi.single i 1 + Pi.single j 1) -
        cutoffProbeForm M L alpha R omega (Pi.single i 1) -
        cutoffProbeForm M L alpha R omega (Pi.single j 1) :=
    cutoffProbeEntry_add_swap M L halpha R omega i j
  have h1 := cutoffProbeForm_nonneg M L alpha R omega (Pi.single i 1 + Pi.single j 1)
  have h2 := cutoffProbeForm_nonneg M L alpha R omega (Pi.single i (1 : ℝ))
  have h3 := cutoffProbeForm_nonneg M L alpha R omega (Pi.single j (1 : ℝ))
  rw [hpol]
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The Chapter 2 carrier bound -/

private theorem aCutoffFamily_coeffOn_isSymmetric
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    Ch02.CoeffOn.IsSymmetric ((aCutoffFamily M L omega).coeffOn Q) := by
  filter_upwards with x
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField, Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [hij, Ne.symm hij]

/-- **The target of this file.**  The Chapter 2 normalized block-response
maximum of the cutoff field, at a scalar normalizer, is dominated by an
explicit finite sum of `cutoffResponseOnCube` values. -/
theorem normalizedBlockResponseMax_aCutoff_le_finiteProbeSum [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Ch02.normalizedBlockResponseMax R (aCutoffFamily M L omega)
        (scalarMatrix (d := d) alpha) ≤
      finiteProbeSum M L alpha R omega := by
  have hmax :=
    SubdiffusiveProcess.Providers.Section2.normalizedBlockResponseMax_le_paperScalarProbeMax
      R (aCutoffFamily M L omega)
      (aCutoffFamily_coeffOn_isSymmetric M L omega R) halpha
  have hsup : paperScalarProbeMax R (aCutoffFamily M L omega) alpha ≤
      ENNReal.ofReal (finiteProbeSum M L alpha R omega) := by
    rw [paperScalarProbeMax]
    refine iSup_le ?_
    rintro ⟨v, hv⟩
    exact ENNReal.ofReal_le_ofReal
      (cutoffProbeForm_le_finiteProbeSum M L halpha R omega hv)
  have hle := hmax.trans hsup
  exact (ENNReal.ofReal_le_ofReal_iff
    (finiteProbeSum_nonneg M L alpha R omega)).1 hle

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
