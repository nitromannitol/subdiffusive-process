module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.CoefficientResponse

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- Square-root response sensitivity for probe pairs with nonnegative pairing. -/
theorem sqrt_responseJ_mul_nearOne_le
    {U : Ch02.Domain d} {a t : Vec d → ℝ}
    (haData : ScalarCoeffOnData U a)
    (hatData : ScalarCoeffOnData U (fun x ↦ a x * t x))
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (ha : ∀ x ∈ (U : Set (Vec d)), 0 < a x)
    (ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon)
    (p q : Vec d) (hpq : 0 ≤ vecDot p q) :
    Real.sqrt (J U hatData.toCoeffOn p q) ≤
      Real.sqrt (1 + 16 * epsilon) *
          Real.sqrt (J U haData.toCoeffOn p q) +
        Real.sqrt (15 * epsilon * vecDot p q) := by
  have hJ := responseJ_mul_nearOne_le haData hatData hepsilon hepsilonHalf
    ha ht p q hpq
  have hJ0 : 0 ≤ J U haData.toCoeffOn p q :=
    Ch02.responseJ_nonneg U _ _ _
  have hcoefficient0 : 0 ≤ 1 + 16 * epsilon := by positivity
  have hprobe0 : 0 ≤ 15 * epsilon * vecDot p q := by positivity
  calc
    Real.sqrt (J U hatData.toCoeffOn p q) ≤
        Real.sqrt ((1 + 16 * epsilon) * J U haData.toCoeffOn p q +
          15 * epsilon * vecDot p q) := Real.sqrt_le_sqrt hJ
    _ ≤ Real.sqrt ((1 + 16 * epsilon) * J U haData.toCoeffOn p q) +
          Real.sqrt (15 * epsilon * vecDot p q) :=
      sqrt_add_le_add_sqrt_of_nonneg
        (mul_nonneg hcoefficient0 hJ0) hprobe0
    _ = Real.sqrt (1 + 16 * epsilon) *
          Real.sqrt (J U haData.toCoeffOn p q) +
        Real.sqrt (15 * epsilon * vecDot p q) := by
      rw [Real.sqrt_mul hcoefficient0]

/-- The normalized scalar probe has pairing one, so the additive response
price is independent of the direction and of the scalar normalizer. -/
theorem sqrt_responseJ_normalizedProbe_mul_nearOne_le
    {U : Ch02.Domain d} {a t : Vec d → ℝ}
    (haData : ScalarCoeffOnData U a)
    (hatData : ScalarCoeffOnData U (fun x ↦ a x * t x))
    {epsilon alpha : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) (halpha : 0 < alpha)
    (ha : ∀ x ∈ (U : Set (Vec d)), 0 < a x)
    (ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon)
    (e : Vec d) (he : vecNormSq e = 1) :
    Real.sqrt (J U hatData.toCoeffOn
        ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)) ≤
      Real.sqrt (1 + 16 * epsilon) *
          Real.sqrt (J U haData.toCoeffOn
            ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)) +
        Real.sqrt (15 * epsilon) := by
  have hsqrt : 0 < Real.sqrt alpha := Real.sqrt_pos.2 halpha
  have hdot : vecDot ((Real.sqrt alpha)⁻¹ • e)
      (Real.sqrt alpha • e) = 1 := by
    rw [vecDot_smul_left, vecDot_smul_right]
    change (Real.sqrt alpha)⁻¹ * (Real.sqrt alpha * vecNormSq e) = 1
    rw [he]
    field_simp
  have hmain := sqrt_responseJ_mul_nearOne_le haData hatData hepsilon
    hepsilonHalf ha ht ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)
    (by rw [hdot]; norm_num)
  simpa only [hdot, mul_one] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
