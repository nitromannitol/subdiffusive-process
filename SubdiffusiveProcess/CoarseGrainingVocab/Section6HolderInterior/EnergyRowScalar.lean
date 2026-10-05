module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyRow

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- `√(x + y) ≤ √x + √y`. -/
theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hxy : 0 ≤ Real.sqrt x * Real.sqrt y :=
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-- **The scalar core of the energy-row conversion.**  The Step-6 square-root
budget splits into the two first-order terms of the energy row. -/
theorem sqrt_projectedEnergyBudget_le {d : ℕ} {K sigma s O F nr : ℝ} {n : ℤ}
    (hK : 0 ≤ K) (hsigma : 0 < sigma) (hs : 0 < s) (hO : 0 ≤ O) (hF : 0 ≤ F) :
    Real.sqrt ((81 : ℝ) ^ d *
        (K * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 +
          s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2))) ≤
      Real.sqrt ((81 : ℝ) ^ d * K) *
        (Real.sqrt sigma * (3 : ℝ) ^ (-n) * O +
          s ^ (-6 : ℝ) * (Real.sqrt sigma)⁻¹ * (3 : ℝ) ^ (s * nr) * F) := by
  have hz : ((3 : ℝ) ^ (-n)) ^ 2 = (3 : ℝ) ^ (-(2 * n)) := by
    rw [← zpow_natCast ((3 : ℝ) ^ (-n)) 2, ← zpow_mul]
    ring_nf
  have hs12 : (s ^ (-6 : ℝ)) ^ 2 = s ^ (-12 : ℝ) := by
    rw [← Real.rpow_natCast (s ^ (-6 : ℝ)) 2, ← Real.rpow_mul hs.le (-6) ((2 : ℕ) : ℝ)]
    norm_num
  have h3s : ((3 : ℝ) ^ (s * nr)) ^ 2 = (3 : ℝ) ^ (2 * s * nr) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (s * nr)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast
    ring_nf
  have hsig : (Real.sqrt sigma) ^ 2 = sigma := Real.sq_sqrt hsigma.le
  have hA : sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2
      = (Real.sqrt sigma * (3 : ℝ) ^ (-n) * O) ^ 2 := by
    rw [mul_pow, mul_pow, hsig, hz]
  have hB : s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2
      = (s ^ (-6 : ℝ) * (Real.sqrt sigma)⁻¹ * (3 : ℝ) ^ (s * nr) * F) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hs12, h3s, inv_pow, hsig]
  have hA0 : (0 : ℝ) ≤ sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 := by positivity
  have hB0 : (0 : ℝ) ≤ s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 := by
    positivity
  have hbase : (0 : ℝ) ≤ (81 : ℝ) ^ d * K := by positivity
  calc Real.sqrt ((81 : ℝ) ^ d *
        (K * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 +
          s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2)))
      = Real.sqrt ((81 : ℝ) ^ d * K) *
          Real.sqrt (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 +
            s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2) := by
        rw [← Real.sqrt_mul hbase]
        ring_nf
    _ ≤ Real.sqrt ((81 : ℝ) ^ d * K) *
          (Real.sqrt (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2) +
            Real.sqrt (s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2)) :=
        mul_le_mul_of_nonneg_left (sqrt_add_le_add_sqrt hA0 hB0) (Real.sqrt_nonneg _)
    _ = _ := by
        rw [hA, hB, Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
