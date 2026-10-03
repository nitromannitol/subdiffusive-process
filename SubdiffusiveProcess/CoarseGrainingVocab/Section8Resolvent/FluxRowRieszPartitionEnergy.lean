module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPartitionInterface

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ} {Cell : Type*} [DecidableEq Cell]

/-- The local positive test norm obtained by normalizing a cell energy by its
physical cell volume. -/
def FluxRowRieszPartition.localPositiveNorm
    (P : FluxRowRieszPartition d Cell)
    (massWeight : Cell → ℝ≥0∞) (kernel : Homogenization.Vec d ×
      Homogenization.Vec d → ℝ≥0∞)
    (density : Homogenization.Vec d → ℝ≥0∞) (q : Cell) : ℝ :=
  Real.sqrt
    ((fluxRowLocalPositiveEnergy volume (P.cell q) (massWeight q)
      kernel density).toReal / P.cellVolume q)

/-- Normalization makes `cellVolume * localPositiveNorm²` exactly the local
positive energy in real coordinates. -/
theorem FluxRowRieszPartition.cellVolume_mul_localPositiveNorm_sq
    (P : FluxRowRieszPartition d Cell)
    (massWeight : Cell → ℝ≥0∞) (kernel : Homogenization.Vec d ×
      Homogenization.Vec d → ℝ≥0∞)
    (density : Homogenization.Vec d → ℝ≥0∞) (q : Cell) :
    P.cellVolume q * (P.localPositiveNorm massWeight kernel density q) ^ 2 =
      (fluxRowLocalPositiveEnergy volume (P.cell q) (massWeight q)
        kernel density).toReal := by
  rw [FluxRowRieszPartition.localPositiveNorm,
    Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg (P.cellVolume_pos q).le)]
  field_simp [ne_of_gt (P.cellVolume_pos q)]

/-- Finite overlap and the global Fourier-energy comparison identify the sum
of normalized local positive costs with the massive weighted test norm. -/
theorem FluxRowRieszPartition.localTestSumSq_le_weightedNormSq
    (P : FluxRowRieszPartition d Cell) (n : ℕ)
    (massWeight : Cell → ℝ≥0∞) (globalMassWeight : ℝ≥0∞)
    (hweight : ∀ q ∈ P.cells n, massWeight q ≤ globalMassWeight)
    (kernel : Homogenization.Vec d × Homogenization.Vec d → ℝ≥0∞)
    (density : Homogenization.Vec d → ℝ≥0∞)
    (hglobalFinite : fluxRowGlobalPositiveEnergy volume globalMassWeight
      kernel density ≠ ∞)
    (globalTest comparison : ℝ)
    (hfourier :
      (fluxRowGlobalPositiveEnergy volume globalMassWeight kernel density).toReal ≤
        comparison * globalTest ^ 2) :
    fluxRowLocalTestSumSq (P.cells n) P.cellVolume
        (P.localPositiveNorm massWeight kernel density) ≤
      (P.overlapCount : ℝ) * comparison * globalTest ^ 2 := by
  let localEnergy : Cell → ℝ≥0∞ := fun q ↦
    fluxRowLocalPositiveEnergy volume (P.cell q) (massWeight q) kernel density
  let globalEnergy : ℝ≥0∞ :=
    fluxRowGlobalPositiveEnergy volume globalMassWeight kernel density
  have hsum := P.sum_localPositiveEnergy_le n massWeight globalMassWeight
    hweight kernel density
  have hrightFinite : (P.overlapCount : ℝ≥0∞) * globalEnergy ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top P.overlapCount) hglobalFinite
  have hsumFinite : (∑ q ∈ P.cells n, localEnergy q) ≠ ∞ :=
    ne_top_of_le_ne_top hrightFinite hsum
  have hlocalFinite : ∀ q ∈ P.cells n, localEnergy q ≠ ∞ := by
    intro q hq
    apply ne_top_of_le_ne_top hsumFinite
    exact Finset.single_le_sum (fun _ _ ↦ bot_le) hq
  calc
    fluxRowLocalTestSumSq (P.cells n) P.cellVolume
        (P.localPositiveNorm massWeight kernel density) =
        ∑ q ∈ P.cells n, (localEnergy q).toReal := by
      unfold fluxRowLocalTestSumSq
      apply Finset.sum_congr rfl
      intro q _
      exact P.cellVolume_mul_localPositiveNorm_sq massWeight kernel density q
    _ = (∑ q ∈ P.cells n, localEnergy q).toReal := by
      exact (ENNReal.toReal_sum hlocalFinite).symm
    _ ≤ ((P.overlapCount : ℝ≥0∞) * globalEnergy).toReal :=
      (ENNReal.toReal_le_toReal hsumFinite hrightFinite).2 hsum
    _ = (P.overlapCount : ℝ) * globalEnergy.toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ ≤ (P.overlapCount : ℝ) * (comparison * globalTest ^ 2) := by
      exact mul_le_mul_of_nonneg_left hfourier (Nat.cast_nonneg _)
    _ = (P.overlapCount : ℝ) * comparison * globalTest ^ 2 := by ring

/-- A summable family of nonnegative per-cell prices.  Each price dominates
the volume-weighted square of the local negative norm. -/
structure FluxRowRieszCoefficientBudget
    (P : FluxRowRieszPartition d Cell) (localNegative : Fin d → Cell → ℝ)
    (K : ℝ) where
  localNegative_nonneg : ∀ i q, 0 ≤ localNegative i q
  cellPrice : Fin d → Cell → ℝ
  cellPrice_nonneg : ∀ i q, 0 ≤ cellPrice i q
  localNegative_sq_le : ∀ i q,
    P.cellVolume q * localNegative i q ^ 2 ≤ cellPrice i q
  cellPrice_summable : ∀ i, Summable (cellPrice i)

/-- The Riesz coefficient supplied by the total summable cell price. -/
def FluxRowRieszCoefficientBudget.coefficient
    {P : FluxRowRieszPartition d Cell} {localNegative : Fin d → Cell → ℝ}
    {K : ℝ} (B : FluxRowRieszCoefficientBudget P localNegative K)
    (i : Fin d) : ℝ :=
  Real.sqrt (2 * K * ∑' q, B.cellPrice i q)

theorem FluxRowRieszCoefficientBudget.coefficient_nonneg
    {P : FluxRowRieszPartition d Cell} {localNegative : Fin d → Cell → ℝ}
    {K : ℝ} (B : FluxRowRieszCoefficientBudget P localNegative K)
    (i : Fin d) : 0 ≤ B.coefficient i :=
  Real.sqrt_nonneg _

theorem FluxRowRieszCoefficientBudget.coefficient_sq
    {P : FluxRowRieszPartition d Cell} {localNegative : Fin d → Cell → ℝ}
    {K : ℝ} (B : FluxRowRieszCoefficientBudget P localNegative K)
    (hK : 0 ≤ K) (i : Fin d) :
    B.coefficient i ^ 2 = 2 * K * ∑' q, B.cellPrice i q := by
  rw [FluxRowRieszCoefficientBudget.coefficient]
  apply Real.sq_sqrt
  exact mul_nonneg (mul_nonneg (by norm_num) hK)
    (tsum_nonneg fun q ↦ B.cellPrice_nonneg i q)

/-- Per-cell coefficient bounds sum to a uniform bound on every finite
exhaustion. -/
theorem FluxRowRieszCoefficientBudget.two_mul_localNegativeSumSq_le_tsum
    {P : FluxRowRieszPartition d Cell} {localNegative : Fin d → Cell → ℝ}
    {K : ℝ} (B : FluxRowRieszCoefficientBudget P localNegative K)
    (hK : 0 ≤ K) (n : ℕ) (i : Fin d) :
    2 * K *
        fluxRowLocalNegativeSumSq (P.cells n) P.cellVolume (localNegative i) ≤
      2 * K * ∑' q, B.cellPrice i q := by
  have hfinite : (∑ q ∈ P.cells n,
      P.cellVolume q * localNegative i q ^ 2) ≤ ∑' q, B.cellPrice i q := by
    calc
      (∑ q ∈ P.cells n, P.cellVolume q * localNegative i q ^ 2) ≤
          ∑ q ∈ P.cells n, B.cellPrice i q := by
        apply Finset.sum_le_sum
        intro q _
        exact B.localNegative_sq_le i q
      _ ≤ ∑' q, B.cellPrice i q :=
        (B.cellPrice_summable i).sum_le_tsum (P.cells n)
          (fun q _ ↦ B.cellPrice_nonneg i q)
  calc
    2 * K *
        fluxRowLocalNegativeSumSq (P.cells n) P.cellVolume (localNegative i) ≤
        2 * K * ∑' q, B.cellPrice i q := by
      exact mul_le_mul_of_nonneg_left hfinite (mul_nonneg (by norm_num) hK)

/-- Square-root form consumed by the stopping-exhaustion Riesz theorem. -/
theorem FluxRowRieszCoefficientBudget.sqrt_two_mul_localNegativeSumSq_le
    {P : FluxRowRieszPartition d Cell} {localNegative : Fin d → Cell → ℝ}
    {K : ℝ} (B : FluxRowRieszCoefficientBudget P localNegative K)
    (hK : 0 ≤ K) (n : ℕ) (i : Fin d) :
    Real.sqrt
        (2 * K *
          fluxRowLocalNegativeSumSq (P.cells n) P.cellVolume
            (localNegative i)) ≤
      B.coefficient i := by
  have hnegativeSum :
      0 ≤ fluxRowLocalNegativeSumSq (P.cells n) P.cellVolume
        (localNegative i) := by
    unfold fluxRowLocalNegativeSumSq
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg (P.cellVolume_pos q).le (sq_nonneg _)
  have hinside : 0 ≤ 2 * K *
      fluxRowLocalNegativeSumSq (P.cells n) P.cellVolume
        (localNegative i) :=
    mul_nonneg (mul_nonneg (by norm_num) hK) hnegativeSum
  have htotal : 0 ≤ 2 * K * ∑' q, B.cellPrice i q :=
    mul_nonneg (mul_nonneg (by norm_num) hK)
      (tsum_nonneg fun q ↦ B.cellPrice_nonneg i q)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (B.coefficient_nonneg i)).mp
  rw [Real.sq_sqrt hinside, FluxRowRieszCoefficientBudget.coefficient,
    Real.sq_sqrt htotal]
  exact B.two_mul_localNegativeSumSq_le_tsum hK n i

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
