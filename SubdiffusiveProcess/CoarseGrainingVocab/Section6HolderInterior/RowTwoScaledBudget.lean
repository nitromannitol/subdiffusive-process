import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoConversion




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- **The row-2 conversion, priced and with a shared total.** -/
theorem interiorRowTwo_of_scaledLegs {d : ℕ}
    {price K Elocal O F A B Total : ℝ} (hprice : 0 ≤ price)
    (hsplit : Elocal ≤ price * (Real.sqrt ((81 : ℝ) ^ d * K) * (O + F)))
    (hO : O ≤ A * Total) (hF : F ≤ B * Total) :
    Elocal ≤ price * Real.sqrt ((81 : ℝ) ^ d * K) * ((A + B) * Total) := by
  have hroot : (0 : ℝ) ≤ Real.sqrt ((81 : ℝ) ^ d * K) := Real.sqrt_nonneg _
  have hsum : O + F ≤ (A + B) * Total := by
    have := add_le_add hO hF
    calc O + F ≤ A * Total + B * Total := this
      _ = (A + B) * Total := by ring
  calc Elocal ≤ price * (Real.sqrt ((81 : ℝ) ^ d * K) * (O + F)) := hsplit
    _ ≤ price * (Real.sqrt ((81 : ℝ) ^ d * K) * ((A + B) * Total)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsum hroot) hprice
    _ = price * Real.sqrt ((81 : ℝ) ^ d * K) * ((A + B) * Total) := by ring

/-- **The row-2 conversion applied to the priced Step-6 square-root budget.** -/
theorem interiorRowTwo_of_scaledBudget {d : ℕ}
    {price K sigma s O F nr A B Total Elocal : ℝ} {n : ℤ}
    (hprice : 0 ≤ price) (hK : 0 ≤ K) (hsigma : 0 < sigma) (hs : 0 < s)
    (hO0 : 0 ≤ O) (hF0 : 0 ≤ F)
    (hbudget : Elocal ≤ price * Real.sqrt ((81 : ℝ) ^ d *
      (K * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 +
        s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2))))
    (hO : Real.sqrt sigma * (3 : ℝ) ^ (-n) * O ≤ A * Total)
    (hF : s ^ (-6 : ℝ) * (Real.sqrt sigma)⁻¹ * (3 : ℝ) ^ (s * nr) * F ≤
      B * Total) :
    Elocal ≤ price * Real.sqrt ((81 : ℝ) ^ d * K) * ((A + B) * Total) := by
  refine interiorRowTwo_of_scaledLegs (d := d) hprice ?_ hO hF
  exact hbudget.trans
    (mul_le_mul_of_nonneg_left (sqrt_projectedEnergyBudget_le hK hsigma hs hO0 hF0)
      hprice)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
