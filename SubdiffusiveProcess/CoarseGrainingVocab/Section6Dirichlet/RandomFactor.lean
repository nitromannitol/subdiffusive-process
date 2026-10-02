import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ParameterBalance
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyFactor

/-!
# Parameter-balanced Dirichlet random factor

This file performs the pointwise arithmetic behind
`e.Dirichlet.random.factor.moment`.  Once the two response errors are written
as `delta` times normalized variables, every scale-dependent coefficient is
bounded by either one or the single ceiling loss `3^s₁`.  The subsequent
probabilistic step therefore sees only a fixed polynomial in the normalized
response errors and the coefficient-only energy envelope.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- Pointwise normal form of the common random factor after the optimizing
scale has been chosen. -/
theorem dirichletRandomFactor_le_normalized
    {C vartheta delta X1 X2 Y : ℝ}
    (hvartheta : 0 < vartheta) (hvarthetaOne : vartheta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hC : 0 ≤ C) (hX1 : 0 ≤ X1) (_hX2 : 0 ≤ X2) (hY : 0 ≤ Y) :
    dirichletRandomFactor C delta vartheta
        (dirichletS1 vartheta) (dirichletS2 vartheta)
        (dirichletBalanceScale vartheta delta)
        (fun _ : Unit ↦ delta * X1) (fun _ : Unit ↦ delta * X2)
        (fun _ : Unit ↦ Y) () ≤
      1 + C *
          (Real.rpow 3 (dirichletS1 vartheta) * X1 * Y + 1 +
            Real.rpow 3 (dirichletS1 vartheta) * X2 ^ (2 : ℕ)) +
        C * (X1 * Y) := by
  let k := dirichletBalanceScale vartheta delta
  let G := Real.rpow 3 (dirichletS1 vartheta)
  let A := Real.rpow delta (-vartheta) *
    (Real.rpow 3 (dirichletS1 vartheta * (k : ℝ)) * delta)
  let B := Real.rpow delta (-vartheta) *
    Real.rpow 3 (-dirichletS2 vartheta * (k : ℝ))
  let D := Real.rpow delta (-vartheta) *
    Real.rpow 3 (-dirichletS2 vartheta * (k : ℝ)) *
    Real.rpow 3 (dirichletS1 vartheta * (k : ℝ)) * delta ^ (2 : ℕ)
  have hA : A ≤ G := by
    simpa [A, G, k] using dirichletBalancedGrowthCoefficient_le
      hvartheta hvarthetaOne hdelta hdeltaOne
  have hB : B ≤ 1 := by
    simpa [B, k] using dirichletBalancedDecayCoefficient_le_one
      hvartheta hvarthetaOne hdelta hdeltaOne
  have hD : D ≤ G := by
    simpa [D, G, k] using dirichletBalancedQuadraticCoefficient_le
      hvartheta hvarthetaOne hdelta hdeltaOne
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (Real.rpow_nonneg hdelta.le _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hdelta.le)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (Real.rpow_nonneg hdelta.le _)
      (Real.rpow_nonneg (by norm_num) _)
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hdelta.le _)
          (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _))
      (sq_nonneg delta)
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact Real.rpow_nonneg (by norm_num) _
  have hlinear : A * X1 * Y ≤ G * X1 * Y := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA hX1) hY
  have hquadratic : D * X2 ^ (2 : ℕ) ≤ G * X2 ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_right hD (sq_nonneg X2)
  have hinside : A * X1 * Y + B + D * X2 ^ (2 : ℕ) ≤
      G * X1 * Y + 1 + G * X2 ^ (2 : ℕ) :=
    add_le_add (add_le_add hlinear hB) hquadratic
  have hinv : Real.rpow delta (-1) = delta⁻¹ := by
    change delta ^ (-1 : ℝ) = delta⁻¹
    rw [Real.rpow_neg_one]
  have hrearrange :
      dirichletRandomFactor C delta vartheta
          (dirichletS1 vartheta) (dirichletS2 vartheta) k
          (fun _ : Unit ↦ delta * X1) (fun _ : Unit ↦ delta * X2)
          (fun _ : Unit ↦ Y) () =
        1 + C * (A * X1 * Y + B + D * X2 ^ (2 : ℕ)) + C * (X1 * Y) := by
    unfold dirichletRandomFactor
    simp only
    rw [hinv]
    dsimp only [A, B, D]
    field_simp
    ring
  rw [show dirichletBalanceScale vartheta delta = k by rfl, hrearrange]
  exact add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hinside hC)) le_rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
