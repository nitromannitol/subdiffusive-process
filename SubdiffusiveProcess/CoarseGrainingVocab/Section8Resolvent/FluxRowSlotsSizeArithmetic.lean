
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The relative-size arithmetic of the local flux price

The proof  ends with the sentence

> the four powers arising from the energy, source, and massive terms are
> bounded by `(size(Q)/R)^{d+6}` because `size(Q) ≥ R` and `σ < 1`

This file is exactly that sentence:
on a stopping cell the relative size `size(Q)/R` is at least `1`, so every real
power of it with exponent at most `d + 6` is dominated by the printed power
`(size(Q)/R)^{d+6}`, and the `σ`-powers appearing in the price have exponent
`2σ < 2 ≤ d + 6`.

Nothing here is analytic; it is the bookkeeping that lets the four separate
size factors of the energy, source and massive terms be collapsed into the one
factor that the price definition
`SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.fluxRowRieszCellPhysicalScale`
carries.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section

/-- On a stopping cell the relative size is at least one: the partition cells
have side at least `R`. -/
theorem fluxRowSlots_one_le_ratio {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    1 ≤ S / R := (one_le_div hR).mpr hRS

/-- Real powers of a number at least one are monotone in the exponent. -/
theorem fluxRowSlots_rpow_ratio_le_rpow {x e e' : ℝ} (hx : 1 ≤ x) (he : e ≤ e') :
    Real.rpow x e ≤ Real.rpow x e' :=
  Real.rpow_le_rpow_of_exponent_le hx he

/-- **The size arithmetic.**

Any real power with exponent at most `d + 6` of the relative size `S / R` of a
stopping cell (`R ≤ S`) is bounded by the printed power `(S/R)^{d+6}`. -/
theorem fluxRowSlots_rpow_ratio_le_natPow {R S e : ℝ} {d : ℕ}
    (hR : 0 < R) (hRS : R ≤ S) (he : e ≤ (d : ℝ) + 6) :
    Real.rpow (S / R) e ≤ (S / R) ^ (d + 6) := by
  have h1 : 1 ≤ S / R := fluxRowSlots_one_le_ratio hR hRS
  have h2 : Real.rpow (S / R) e ≤ Real.rpow (S / R) ((d : ℝ) + 6) :=
    fluxRowSlots_rpow_ratio_le_rpow h1 he
  have h3 : Real.rpow (S / R) ((d : ℝ) + 6) = (S / R) ^ (d + 6) := by
    rw [← Real.rpow_natCast (S / R) (d + 6)]
    congr 1
    push_cast
    ring
  exact h3 ▸ h2

/-- Natural powers of the relative size are monotone in the exponent. -/
theorem fluxRowSlots_natPow_ratio_le {R S : ℝ} {d k : ℕ}
    (hR : 0 < R) (hRS : R ≤ S) (hk : k ≤ d + 6) :
    (S / R) ^ k ≤ (S / R) ^ (d + 6) :=
  pow_le_pow_right₀ (fluxRowSlots_one_le_ratio hR hRS) hk

/-- **The `σ < 1` half of the same sentence.**

The price's `σ`-powers of the relative size have exponent `2σ < 2 ≤ d + 6`. -/
theorem fluxRowSlots_rpow_two_sigma_ratio_le {R S sigma : ℝ} {d : ℕ}
    (hR : 0 < R) (hRS : R ≤ S) (hsigma : sigma < 1) :
    Real.rpow (S / R) (2 * sigma) ≤ (S / R) ^ (d + 6) := by
  refine fluxRowSlots_rpow_ratio_le_natPow hR hRS ?_
  have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

/-- **The four-power collapse.**

The four size powers arising from the energy, source and massive terms — any
four exponents at most `d + 6` — are each bounded by the printed
`(size(Q)/R)^{d+6}`. -/
theorem fluxRowSlots_four_rpow_ratio_le {R S e₁ e₂ e₃ e₄ : ℝ} {d : ℕ}
    (hR : 0 < R) (hRS : R ≤ S)
    (h₁ : e₁ ≤ (d : ℝ) + 6) (h₂ : e₂ ≤ (d : ℝ) + 6)
    (h₃ : e₃ ≤ (d : ℝ) + 6) (h₄ : e₄ ≤ (d : ℝ) + 6) :
    Real.rpow (S / R) e₁ ≤ (S / R) ^ (d + 6) ∧
      Real.rpow (S / R) e₂ ≤ (S / R) ^ (d + 6) ∧
        Real.rpow (S / R) e₃ ≤ (S / R) ^ (d + 6) ∧
          Real.rpow (S / R) e₄ ≤ (S / R) ^ (d + 6) :=
  ⟨fluxRowSlots_rpow_ratio_le_natPow hR hRS h₁,
    fluxRowSlots_rpow_ratio_le_natPow hR hRS h₂,
    fluxRowSlots_rpow_ratio_le_natPow hR hRS h₃,
    fluxRowSlots_rpow_ratio_le_natPow hR hRS h₄⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
