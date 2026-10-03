module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoGateBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EnergyBudgetReadout

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem sqrt_budget_le_four {K Bud A G F H : ℝ}
    (hK : 0 ≤ K)
    (hBudLe : Bud ≤ A ^ 2 + G ^ 2 + F ^ 2 + H ^ 2)
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hF : 0 ≤ F) (hH : 0 ≤ H) :
    Real.sqrt (K * Bud) ≤ Real.sqrt K * (A + G + F + H) := by
  rw [Real.sqrt_mul hK]
  exact mul_le_mul_of_nonneg_left
    ((Real.sqrt_le_sqrt hBudLe).trans (sqrt_four_sq_le_sum hA hG hF hH))
    (Real.sqrt_nonneg K)

/-- The physical four-budget definition, including its conditional boundary
terms, has the expected first-order square-root readout. -/
theorem sqrt_harmonicPhysicalFourBudgets_le_legs {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m n : ℕ)
    (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {s K : ℝ} (hs : 0 < s) (hK : 0 ≤ K)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d) :
    Real.sqrt (K * harmonicPhysicalFourBudgets M L m n z x omega s u h g) ≤
      Real.sqrt K *
        (Real.sqrt (tailAverage M L (n + 2) omega
            (translatedCube d ((n : ℤ) + 2) z)) *
            (3 : ℝ) ^ (-(n : ℤ)) *
            normalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
              (fun q ↦ u.toFun q -
                averageOn (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun) +
          Real.sqrt (tailAverage M L (n + 2) omega
            (translatedCube d ((n : ℤ) + 2) z)) *
            Real.sqrt (vecNormSq
              (averageVecOn (truncatedCube d (m : ℤ) (n : ℤ) x) h.grad)) +
          s ^ (-6 : ℝ) *
            (Real.sqrt (tailAverage M L (n + 2) omega
              (translatedCube d ((n : ℤ) + 2) z)))⁻¹ *
            (3 : ℝ) ^ (s * (n : ℝ)) *
            (fractionalSeminormOn (truncatedCube d (m : ℤ) (n : ℤ) x) s g).toReal +
          Real.sqrt (tailAverage M L (n + 2) omega
            (translatedCube d ((n : ℤ) + 2) z)) * s ^ (-2 : ℝ) *
            (3 : ℝ) ^ (s * (n : ℝ)) *
            (fractionalSeminormOn (truncatedCube d (m : ℤ) (n : ℤ) x)
              s h.grad).toReal) := by
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let O := normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun)
  let A := Real.sqrt sigma * (3 : ℝ) ^ (-(n : ℤ)) * O
  let G := Real.sqrt sigma * Real.sqrt (vecNormSq (averageVecOn U h.grad))
  let F := s ^ (-6 : ℝ) * (Real.sqrt sigma)⁻¹ *
    (3 : ℝ) ^ (s * (n : ℝ)) * (fractionalSeminormOn U s g).toReal
  let H := Real.sqrt sigma * s ^ (-2 : ℝ) *
    (3 : ℝ) ^ (s * (n : ℝ)) * (fractionalSeminormOn U s h.grad).toReal
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hA : 0 ≤ A := by
    dsimp only [A, O]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
      (Section6Iteration.normalizedL2On_nonneg _ _)
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))) (Real.rpow_nonneg (by norm_num) _))
      ENNReal.toReal_nonneg
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hs.le _)) (Real.rpow_nonneg (by norm_num) _))
      ENNReal.toReal_nonneg
  have hz : ((3 : ℝ) ^ (-(n : ℤ))) ^ 2 =
      (3 : ℝ) ^ (-(2 * (n : ℤ))) := by
    rw [← zpow_natCast ((3 : ℝ) ^ (-(n : ℤ))) 2, ← zpow_mul]
    ring_nf
  have hs12 : (s ^ (-6 : ℝ)) ^ 2 = s ^ (-12 : ℝ) := by
    rw [← Real.rpow_natCast (s ^ (-6 : ℝ)) 2,
      ← Real.rpow_mul hs.le (-6) ((2 : ℕ) : ℝ)]
    norm_num
  have hs4 : (s ^ (-2 : ℝ)) ^ 2 = s ^ (-4 : ℝ) := by
    rw [← Real.rpow_natCast (s ^ (-2 : ℝ)) 2,
      ← Real.rpow_mul hs.le (-2) ((2 : ℕ) : ℝ)]
    norm_num
  have h3s : ((3 : ℝ) ^ (s * (n : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * s * (n : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (s * (n : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast
    ring_nf
  have hsig : (Real.sqrt sigma) ^ 2 = sigma := Real.sq_sqrt hsigma.le
  have hparent : sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * O ^ 2 = A ^ 2 := by
    dsimp only [A]
    rw [mul_pow, mul_pow, hsig, hz]
  have haffine : sigma * vecNormSq (averageVecOn U h.grad) = G ^ 2 := by
    dsimp only [G]
    rw [mul_pow, hsig, Real.sq_sqrt (vecNormSq_nonneg _)]
  have hforce : s ^ (-12 : ℝ) * sigma⁻¹ *
      (3 : ℝ) ^ (2 * s * (n : ℝ)) *
      (fractionalSeminormOn U s g).toReal ^ 2 = F ^ 2 := by
    dsimp only [F]
    rw [mul_pow, mul_pow, mul_pow, hs12, h3s, inv_pow, hsig]
  have hboundary : sigma * s ^ (-4 : ℝ) *
      (3 : ℝ) ^ (2 * s * (n : ℝ)) *
      (fractionalSeminormOn U s h.grad).toReal ^ 2 = H ^ 2 := by
    dsimp only [H]
    rw [mul_pow, mul_pow, mul_pow, hsig, hs4, h3s]
  have hBudLe : harmonicPhysicalFourBudgets M L m n z x omega s u h g ≤
      A ^ 2 + G ^ 2 + F ^ 2 + H ^ 2 := by
    change
      sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * O ^ 2 +
          (if BoundaryTouches U (cube d (m : ℤ)) then
            sigma * vecNormSq (averageVecOn U h.grad) else 0) +
          s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
            (fractionalSeminormOn U s g).toReal ^ 2 +
          (if BoundaryTouches U (cube d (m : ℤ)) then
            sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
              (fractionalSeminormOn U s h.grad).toReal ^ 2 else 0) ≤
        A ^ 2 + G ^ 2 + F ^ 2 + H ^ 2
    rw [hparent, hforce]
    by_cases ht : BoundaryTouches U (cube d (m : ℤ))
    · simp only [if_pos ht, haffine, hboundary]
      exact le_rfl
    · simp only [if_neg ht]
      nlinarith only [sq_nonneg G, sq_nonneg H]
  have hout := sqrt_budget_le_four hK hBudLe hA hG hF hH
  simpa only [A, G, F, H, O, U, sigma] using hout

/-- A priced four-budget estimate, together with one bound for each physical
leg, gives a bound against a shared nonnegative total. -/
theorem boundaryRowTwo_of_scaledBudget {d : ℕ}
    {price K Bud A G F H AO AG AF AH Total Elocal : ℝ}
    (hprice : 0 ≤ price) (hK : 0 ≤ K)
    (hBudLe : Bud ≤ A ^ 2 + G ^ 2 + F ^ 2 + H ^ 2)
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (hbudget : Elocal ≤ price * Real.sqrt ((81 : ℝ) ^ d * (K * Bud)))
    (hAO : A ≤ AO * Total) (hAG : G ≤ AG * Total)
    (hAF : F ≤ AF * Total) (hAH : H ≤ AH * Total) :
    Elocal ≤ price * Real.sqrt ((81 : ℝ) ^ d * K) *
      ((AO + AG + AF + AH) * Total) := by
  have h81 : 0 ≤ (81 : ℝ) ^ d := by positivity
  have hroot := sqrt_budget_le_four
    (K := (81 : ℝ) ^ d * K) (mul_nonneg h81 hK) hBudLe hA hG hF hH
  have hsum : A + G + F + H ≤ (AO + AG + AF + AH) * Total := by
    calc
      A + G + F + H ≤ AO * Total + AG * Total + AF * Total + AH * Total :=
        add_le_add (add_le_add (add_le_add hAO hAG) hAF) hAH
      _ = (AO + AG + AF + AH) * Total := by ring
  have hroot' : Real.sqrt ((81 : ℝ) ^ d * (K * Bud)) ≤
      Real.sqrt ((81 : ℝ) ^ d * K) * ((AO + AG + AF + AH) * Total) := by
    rw [show (81 : ℝ) ^ d * (K * Bud) = ((81 : ℝ) ^ d * K) * Bud by ring]
    exact hroot.trans
      (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _))
  refine hbudget.trans ?_
  convert mul_le_mul_of_nonneg_left hroot' hprice using 1
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
