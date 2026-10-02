import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GammaOneArithmetic

/-!
# Assembling the two stopping halves into the frozen Γ₁ bound

The combined stopping scale splits into an accumulated-error depth and a
good-density depth (`measure_measurable(Cutoff)HolderStoppingScale_tail_le_add`).
This module takes the two halves — each already an exponential with its own
rate — and produces the frozen Γ₁ right-hand side, once and for all.

Two elementary observations carry the argument.

* Below the frozen shift, i.e. for `k ≤ C`, the frozen bound is `C ≥ 1` and the
  estimate is free because the layer law is a probability measure.
* Above it, `k > C ≥ step + 6` guarantees both that the deterministic
  `step + 5` margin can be removed and that the remaining threshold is positive,
  so both landed tails apply; each is then at most half the frozen bound by
  `exp_bound_le` and `gammaOne_exponent_le`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The Γ₁ assembly.**  Both halves in their own rate, out comes the frozen
right-hand side. -/
theorem measure_le_gammaOneRHS_of_parts
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {Xs Derr Dgood : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ}
    {C Berr Bgood alpha : ℝ} {step k : ℕ}
    (hCstep : (step : ℝ) + 6 ≤ C)
    (hBerrPos : 0 < Berr) (hBerrC : Berr ≤ C)
    (hBgoodPos : 0 < Bgood) (hBgoodC : Bgood ≤ C)
    (hgammaC : Section6Stopping.holderGammaOneGeometricConst ≤ C / 2)
    (hD : 0 < M.delta ^ 2 * |Real.log M.delta|)
    (hsplit : step + 5 ≤ k → M.P.toMeasure {ω | k < Xs ω} ≤
        M.P.toMeasure {ω | k - (step + 5) < Derr ω} +
          M.P.toMeasure {ω | k - (step + 5) < Dgood ω})
    (herr : ∀ q : ℕ, 0 < q → M.P.toMeasure {ω | q < Derr ω} ≤
        ENNReal.ofReal (Section6Stopping.holderGammaOneGeometricConst *
          Real.exp (-((1 - alpha) ^ 2 * max ((q : ℝ) - 1) 0 /
            (Berr * (M.delta ^ 2 * |Real.log M.delta|))))))
    (hgood : ∀ q : ℕ, M.P.toMeasure {ω | q < Dgood ω} ≤
        ENNReal.ofReal (2 * Real.exp (-((1 - alpha) ^ 2 * (q : ℝ) /
          (Bgood * (M.delta ^ 2 * |Real.log M.delta|)))))) :
    M.P.toMeasure {ω | k < Xs ω} ≤ ENNReal.ofReal (gammaOneRHS M C alpha k) := by
  have hCpos : (0 : ℝ) < C := by linarith
  by_cases hkC : (k : ℝ) ≤ C
  · -- below the frozen shift the bound is `C ≥ 1`
    have hmax : max ((k : ℝ) - C) 0 = 0 := max_eq_right (by linarith)
    have hrhs : gammaOneRHS M C alpha k = C := by
      unfold gammaOneRHS
      rw [hmax]
      simp
    rw [hrhs]
    calc M.P.toMeasure {ω | k < Xs ω} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal C := by
          rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  · push_neg at hkC
    have hk6 : step + 6 ≤ k := by
      have hlt : ((step : ℝ) + 6) < (k : ℝ) := lt_of_le_of_lt hCstep hkC
      have hcast : ((step + 6 : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by push_cast; linarith
      have : (step + 6 : ℕ) < k := by exact_mod_cast hcast
      omega
    have hkstep : step + 5 ≤ k := by omega
    set q : ℕ := k - (step + 5) with hq
    have hqpos : 0 < q := by omega
    -- the two rate comparisons
    have hWerr : max ((k : ℝ) - C) 0 ≤ max ((q : ℝ) - 1) 0 := by
      have hqcast : ((q : ℕ) : ℝ) = (k : ℝ) - ((step : ℝ) + 5) := by
        rw [hq, Nat.cast_sub (by omega)]
        push_cast
        ring
      have : (k : ℝ) - C ≤ (q : ℝ) - 1 := by rw [hqcast]; linarith
      exact max_le_max this le_rfl
    have hWgood : max ((k : ℝ) - C) 0 ≤ (q : ℝ) := by
      have hqcast : ((q : ℕ) : ℝ) = (k : ℝ) - ((step : ℝ) + 5) := by
        rw [hq, Nat.cast_sub (by omega)]
        push_cast
        ring
      apply max_le
      · rw [hqcast]; linarith
      · exact Nat.cast_nonneg q
    have hexpErr : (1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
        (C * (M.delta ^ 2 * |Real.log M.delta|)) ≤
          (1 - alpha) ^ 2 * max ((q : ℝ) - 1) 0 /
            (Berr * (M.delta ^ 2 * |Real.log M.delta|)) :=
      gammaOne_exponent_le hCpos hBerrPos hD hBerrC hWerr
    have hexpGood : (1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
        (C * (M.delta ^ 2 * |Real.log M.delta|)) ≤
          (1 - alpha) ^ 2 * (q : ℝ) /
            (Bgood * (M.delta ^ 2 * |Real.log M.delta|)) :=
      gammaOne_exponent_le hCpos hBgoodPos hD hBgoodC hWgood
    -- each half is at most half the frozen bound
    have hhalfErr : Section6Stopping.holderGammaOneGeometricConst *
        Real.exp (-((1 - alpha) ^ 2 * max ((q : ℝ) - 1) 0 /
          (Berr * (M.delta ^ 2 * |Real.log M.delta|)))) ≤
        C / 2 * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
          (C * (M.delta ^ 2 * |Real.log M.delta|)))) := by
      exact exp_bound_le Section6Stopping.holderGammaOneGeometricConst_pos.le
        hgammaC hexpErr
    have hhalfGood : 2 * Real.exp (-((1 - alpha) ^ 2 * (q : ℝ) /
          (Bgood * (M.delta ^ 2 * |Real.log M.delta|)))) ≤
        C / 2 * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
          (C * (M.delta ^ 2 * |Real.log M.delta|)))) :=
      exp_bound_le (by norm_num) (by linarith) hexpGood
    have hsum : Section6Stopping.holderGammaOneGeometricConst *
          Real.exp (-((1 - alpha) ^ 2 * max ((q : ℝ) - 1) 0 /
            (Berr * (M.delta ^ 2 * |Real.log M.delta|)))) +
        2 * Real.exp (-((1 - alpha) ^ 2 * (q : ℝ) /
          (Bgood * (M.delta ^ 2 * |Real.log M.delta|)))) ≤
          gammaOneRHS M C alpha k := by
      rw [gammaOneRHS_eq]
      have : C / 2 * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
            (C * (M.delta ^ 2 * |Real.log M.delta|)))) +
          C / 2 * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
            (C * (M.delta ^ 2 * |Real.log M.delta|)))) =
          C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
            (C * (M.delta ^ 2 * |Real.log M.delta|)))) := by ring
      linarith
    calc M.P.toMeasure {ω | k < Xs ω}
        ≤ M.P.toMeasure {ω | q < Derr ω} + M.P.toMeasure {ω | q < Dgood ω} :=
          hsplit hkstep
      _ ≤ ENNReal.ofReal (Section6Stopping.holderGammaOneGeometricConst *
            Real.exp (-((1 - alpha) ^ 2 * max ((q : ℝ) - 1) 0 /
              (Berr * (M.delta ^ 2 * |Real.log M.delta|))))) +
          ENNReal.ofReal (2 * Real.exp (-((1 - alpha) ^ 2 * (q : ℝ) /
            (Bgood * (M.delta ^ 2 * |Real.log M.delta|))))) :=
          add_le_add (herr q hqpos) (hgood q)
      _ = ENNReal.ofReal (Section6Stopping.holderGammaOneGeometricConst *
            Real.exp (-((1 - alpha) ^ 2 * max ((q : ℝ) - 1) 0 /
              (Berr * (M.delta ^ 2 * |Real.log M.delta|)))) +
            2 * Real.exp (-((1 - alpha) ^ 2 * (q : ℝ) /
              (Bgood * (M.delta ^ 2 * |Real.log M.delta|))))) := by
          rw [ENNReal.ofReal_add
            (mul_nonneg Section6Stopping.holderGammaOneGeometricConst_pos.le
              (Real.exp_nonneg _)) (by positivity)]
      _ ≤ ENNReal.ofReal (gammaOneRHS M C alpha k) := ENNReal.ofReal_le_ofReal hsum

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
