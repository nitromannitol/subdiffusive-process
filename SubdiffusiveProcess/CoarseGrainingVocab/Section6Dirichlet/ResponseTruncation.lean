module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RandomFactorMoment

@[expose] public section

/-!
# Starting-scale truncation of the Dirichlet response errors

The mesoscopic coarse-graining call starts the response sum `k` scales below
the parent.  This file identifies that sum with a shifted tail of the full
response series and pays exactly the manuscript factor `3^(s k)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

/-- A shifted nonnegative `ENNReal` series is bounded by the complete series. -/
private theorem tsum_nat_add_le (F : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' l : ℕ, F (k + l) ≤ ∑' l : ℕ, F l := by
  exact ENNReal.tsum_comp_le_tsum_of_injective
    (fun _ _ h ↦ Nat.add_left_cancel h) F

/-- Changing the starting scale from `m` to `m-k` takes a shifted tail of the
finite-`q` paper error and costs `3^(s k)`. -/
theorem paperHomogenizationErrorFinite_sub_natCast_le
    {d : ℕ} (Q : TriadicCube d) (m : ℤ) (k : ℕ)
    {s q : ℝ} (hq : 0 < q) (p : Ch02.MultiscaleExponent)
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) :
    paperHomogenizationErrorFinite Q (m - (k : ℤ)) s p q a alpha ≤
      ENNReal.ofReal (Real.rpow 3 (s * (k : ℝ))) *
        paperHomogenizationErrorFinite Q m s p q a alpha := by
  let G : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s * (k : ℝ)))
  let F : ℕ → ℝ≥0∞ := fun l ↦
    ENNReal.ofReal (Ch02.geometricWeight s q l) *
      (paperScaleResponseAtScale Q (m - (l : ℤ)) p a alpha) ^ q
  have hweight : ∀ l : ℕ,
      ENNReal.ofReal (Ch02.geometricWeight s q l) =
        G ^ q * ENNReal.ofReal (Ch02.geometricWeight s q (k + l)) := by
    intro l
    have hshift : Ch02.geometricWeight s q l =
        Real.rpow 3 (s * q * (k : ℝ)) *
          Ch02.geometricWeight s q (k + l) := by
      simp only [Ch02.geometricWeight_eq_old]
      simpa only [Nat.add_comm l k] using
        (Homogenization.geometricWeight_shift (s := s) (q := q) k l)
    calc
      ENNReal.ofReal (Ch02.geometricWeight s q l) =
          ENNReal.ofReal (Real.rpow 3 (s * q * (k : ℝ)) *
            Ch02.geometricWeight s q (k + l)) := congrArg ENNReal.ofReal hshift
      _ = ENNReal.ofReal (Real.rpow 3 (s * q * (k : ℝ))) *
          ENNReal.ofReal (Ch02.geometricWeight s q (k + l)) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)
      _ = G ^ q * ENNReal.ofReal (Ch02.geometricWeight s q (k + l)) := by
        congr 1
        dsimp only [G]
        have hpow : Real.rpow 3 (s * q * (k : ℝ)) =
            Real.rpow (Real.rpow 3 (s * (k : ℝ))) q := by
          calc
            Real.rpow 3 (s * q * (k : ℝ)) =
                Real.rpow 3 ((s * (k : ℝ)) * q) := by congr 1; ring
            _ = Real.rpow (Real.rpow 3 (s * (k : ℝ))) q :=
              Real.rpow_mul (by norm_num) _ _
        rw [hpow]
        exact (ENNReal.ofReal_rpow_of_pos
          (Real.rpow_pos_of_pos (by norm_num) _)).symm
  have hterm : ∀ l : ℕ,
      ENNReal.ofReal (Ch02.geometricWeight s q l) *
          (paperScaleResponseAtScale Q
            ((m - (k : ℤ)) - (l : ℤ)) p a alpha) ^ q =
        G ^ q * F (k + l) := by
    intro l
    rw [hweight]
    dsimp only [F]
    have hscale : (m - (k : ℤ)) - (l : ℤ) = m - ((k + l : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hscale]
    ring
  have hsum :
      (∑' l : ℕ,
        ENNReal.ofReal (Ch02.geometricWeight s q l) *
          (paperScaleResponseAtScale Q
            ((m - (k : ℤ)) - (l : ℤ)) p a alpha) ^ q) ≤
        G ^ q * ∑' l : ℕ, F l := by
    calc
      (∑' l : ℕ,
          ENNReal.ofReal (Ch02.geometricWeight s q l) *
            (paperScaleResponseAtScale Q
              ((m - (k : ℤ)) - (l : ℤ)) p a alpha) ^ q) =
          ∑' l : ℕ, G ^ q * F (k + l) := by
        apply tsum_congr
        exact hterm
      _ = G ^ q * ∑' l : ℕ, F (k + l) := ENNReal.tsum_mul_left
      _ ≤ G ^ q * ∑' l : ℕ, F l :=
        mul_le_mul_right (tsum_nat_add_le F k) _
  unfold paperHomogenizationErrorFinite
  calc
    (∑' l : ℕ,
        ENNReal.ofReal (Ch02.geometricWeight s q l) *
          (paperScaleResponseAtScale Q
            (m - (k : ℤ) - (l : ℤ)) p a alpha) ^ q) ^ (1 / q) ≤
        (G ^ q * ∑' l : ℕ, F l) ^ (1 / q) :=
      ENNReal.rpow_le_rpow hsum (by positivity)
    _ = G * (∑' l : ℕ, F l) ^ (1 / q) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
      have hcancel : q * (1 / q) = 1 := by field_simp
      rw [hcancel, ENNReal.rpow_one]
    _ = ENNReal.ofReal (Real.rpow 3 (s * (k : ℝ))) *
        (∑' l : ℕ,
          ENNReal.ofReal (Ch02.geometricWeight s q l) *
            (paperScaleResponseAtScale Q (m - (l : ℤ)) p a alpha) ^ q) ^
              (1 / q) := rfl

/-- The `q=1` truncation used by the first coarse-graining term. -/
theorem paperHomogenizationError_sub_natCast_infinity_one_le
    {d : ℕ} (Q : TriadicCube d) (m : ℤ) (k : ℕ) {s : ℝ}
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) :
    paperHomogenizationError Q (m - (k : ℤ)) s .infinity (.finite 1) a alpha ≤
      ENNReal.ofReal (Real.rpow 3 (s * (k : ℝ))) *
        paperHomogenizationError Q m s .infinity (.finite 1) a alpha := by
  exact paperHomogenizationErrorFinite_sub_natCast_le Q m k (by norm_num)
    .infinity a alpha

/-- The `q=2` truncation used by the second coarse-graining term. -/
theorem paperHomogenizationError_sub_natCast_infinity_two_le
    {d : ℕ} (Q : TriadicCube d) (m : ℤ) (k : ℕ) {s : ℝ}
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) :
    paperHomogenizationError Q (m - (k : ℤ)) s .infinity (.finite 2) a alpha ≤
      ENNReal.ofReal (Real.rpow 3 (s * (k : ℝ))) *
        paperHomogenizationError Q m s .infinity (.finite 2) a alpha := by
  exact paperHomogenizationErrorFinite_sub_natCast_le Q m k (by norm_num)
    .infinity a alpha

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
