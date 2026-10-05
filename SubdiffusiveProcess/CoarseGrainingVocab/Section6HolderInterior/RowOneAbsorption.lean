module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneShapeMatch

@[expose] public section

/-!
# The joint absorption bound at the ladder's exponent

`interiorRowOne_arithJoint` needs

```text
  exp(Ā) · exponential ≤ Cabs · 3^{(1-α)·gap/4} ,
```

where `Ā` is the gated Campanato exponent and `exponential` the
coefficient-ratio bound.  This module proves it from
`Section6Holder.exists_holderExponentialAbsorption`, by checking that the *sum*
of the two exponents is dominated by the affine form `A₀ + P·λ·(gap+1)` that the
absorption consumes.

Writing `gap = m - ell` and `λ = C₁⁻¹(1-α)`:

```text
  Ā + C_ratio·λ·gap
    = A₀ + λ·( Citer·(k+1)·gap + 3·Citer·Keps·(gap+1) + C_ratio·gap )
    ≤ A₀ + λ·( Citer·(k+1) + 3·Citer·Keps + C_ratio )·(gap+1) ,
```

using only `gap ≤ gap + 1` and nonnegativity of the coefficients.  That last
bracket is the `P` the caller must feed to the absorption.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The ladder exponent plus the coefficient-ratio exponent is dominated by the
affine form the absorption consumes. -/
theorem ladderExponent_le_affine {Citer Keps Cratio lambda gap k : ℝ}
    (hCiter : 0 ≤ Citer) (hCratio : 0 ≤ Cratio)
    (hlambda : 0 ≤ lambda) (hk : 0 ≤ k) :
    (Citer * (k + 1) * (k + 2 + lambda * gap) +
        Citer * (3 * Keps * lambda * (gap + 1))) + Cratio * lambda * gap ≤
      Citer * (k + 1) * (k + 2) +
        (Citer * (k + 1) + 3 * Citer * Keps + Cratio) * lambda * (gap + 1) := by
  have hgap1 : gap ≤ gap + 1 := by linarith
  have h1 : Citer * (k + 1) * (lambda * gap) ≤
      Citer * (k + 1) * (lambda * (gap + 1)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hgap1 hlambda
  have h2 : Cratio * (lambda * gap) ≤ Cratio * (lambda * (gap + 1)) := by
    apply mul_le_mul_of_nonneg_left _ hCratio
    exact mul_le_mul_of_nonneg_left hgap1 hlambda
  nlinarith [h1, h2]

/-- **The joint absorption bound.**  From the proved exponential absorption at
`(A₀, P)`, the product of the ladder exponential and the coefficient-ratio
exponential is at most `Cabs · 3^{(1-α)·gap/4}`. -/
theorem expAbar_mul_ratio_le {Citer Keps Cratio alpha gap k C₁ Cabs : ℝ}
    (hCiter : 0 ≤ Citer) (hCratio : 0 ≤ Cratio)
    (hgap : 0 ≤ gap) (hk : 0 ≤ k)
    (halpha : alpha ∈ Set.Icc (1 / 2 : ℝ) 1) (hC₁ : 0 < C₁)
    (habsorb : ∀ a ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gp : ℝ, 0 ≤ gp →
      Real.exp (Citer * (k + 1) * (k + 2) +
          (Citer * (k + 1) + 3 * Citer * Keps + Cratio) *
            (C₁⁻¹ * (1 - a)) * (gp + 1)) ≤
        Cabs * (3 : ℝ) ^ ((1 - a) * gp / 4)) :
    Real.exp (Citer * (k + 1) * (k + 2 + (C₁⁻¹ * (1 - alpha)) * gap) +
        Citer * (3 * Keps * (C₁⁻¹ * (1 - alpha)) * (gap + 1))) *
      Real.exp (Cratio * (C₁⁻¹ * (1 - alpha)) * gap) ≤
      Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := by
  have hlambda : 0 ≤ C₁⁻¹ * (1 - alpha) :=
    mul_nonneg (inv_nonneg.mpr hC₁.le) (by linarith [halpha.2])
  have hsum := ladderExponent_le_affine (Citer := Citer) (Keps := Keps)
    (Cratio := Cratio) (lambda := C₁⁻¹ * (1 - alpha)) (gap := gap) (k := k)
    hCiter hCratio hlambda hk
  calc Real.exp (Citer * (k + 1) * (k + 2 + (C₁⁻¹ * (1 - alpha)) * gap) +
          Citer * (3 * Keps * (C₁⁻¹ * (1 - alpha)) * (gap + 1))) *
        Real.exp (Cratio * (C₁⁻¹ * (1 - alpha)) * gap)
      = Real.exp ((Citer * (k + 1) * (k + 2 + (C₁⁻¹ * (1 - alpha)) * gap) +
          Citer * (3 * Keps * (C₁⁻¹ * (1 - alpha)) * (gap + 1))) +
          Cratio * (C₁⁻¹ * (1 - alpha)) * gap) := by
        rw [← Real.exp_add]
    _ ≤ Real.exp (Citer * (k + 1) * (k + 2) +
          (Citer * (k + 1) + 3 * Citer * Keps + Cratio) *
            (C₁⁻¹ * (1 - alpha)) * (gap + 1)) := by
        apply Real.exp_le_exp.mpr
        calc _ ≤ Citer * (k + 1) * (k + 2) +
              (Citer * (k + 1) + 3 * Citer * Keps + Cratio) *
                (C₁⁻¹ * (1 - alpha)) * (gap + 1) := by
              have := hsum
              nlinarith [this]
          _ = _ := by ring
    _ ≤ Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := habsorb alpha halpha gap hgap

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
