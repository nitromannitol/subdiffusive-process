import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CombineFinalAssembly

/-!
# Provider for `p.combine.under.S`

The proof assembles the integrated corridor estimate with the cutoff-scale base
case, the finite-gap exponential gate, and the concrete bad-event response
bound. No headline-shaped premise remains.
-/

namespace SubdiffusiveProcess.Providers.Section4

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open MeasureTheory Homogenization.Book
open scoped BigOperators

noncomputable section

/-- Exact provider export for `p.combine.under.S`. -/
theorem combine_under_s {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (xi delta1 : ℝ),
        16 * (d : ℝ) ≤ xi →
        C * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
        inductionHypothesis M L xi delta1 →
        ∀ m : ℕ, 0 < m → L ≤ m →
          C * Real.rpow 3 (-((m - L : ℕ) : ℝ)) ≤ (1 / 4 : ℝ) →
          ∀ p q : Vec d,
            q = ahom M L • p → Homogenization.vecNormSq q ≤ ahom M L →
            expectedJ M L m p q ≤
              C * delta1 *
                  (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ))) +
                C * ∑ n ∈ Finset.Icc L m,
                  Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                    expectedJDifference M L n m p q := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro M
    have hdim := M.shellPrefix.dimension
    omega
  letI : NeZero d := ⟨hd⟩
  obtain ⟨Cvar, hCvar, hvariance⟩ :=
    exists_expectedJ_le_varianceClosedDisplay d
  have hCvarPos : 0 < Cvar := lt_of_lt_of_le zero_lt_one hCvar
  obtain ⟨Cgate, hCgate, hgateBridge⟩ :=
    exists_full_gate_implies_three_quarter_gate Cvar hCvarPos
  obtain ⟨cbad, Cbad, hcbad, hCbad, hbad⟩ :=
    exists_badEvent_previousCube_response_le_delta_sq d
  let C : ℝ := max Cgate (max Cbad (Cvar + 2 * Cbad))
  have hCgateC : Cgate ≤ C := le_max_left _ _
  have hCbadC : Cbad ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCsumC : Cvar + 2 * Cbad ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hCvarC : Cvar ≤ C := by
    calc
      Cvar ≤ Cvar + 2 * Cbad := by linarith [hCbad]
      _ ≤ C := hCsumC
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (hCgate.trans hCgateC)
  refine ⟨cbad, C, hcbad, hC, ?_⟩
  intro M L xi delta1 hdim hdeltaGate hdeltaSmall hS
  have hdTwo : 2 ≤ d := M.shellPrefix.dimension
  have hdCast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdTwo
  have hxiTwo : 2 ≤ xi := by nlinarith
  have hxi0 : 0 ≤ xi := by linarith
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  intro m hm hLm hscale p q hq hqNorm
  by_cases hmL : m = L
  · subst m
    have hbase := expectedJ_base_le_delta_of_inductionHypothesis
      M L hxiTwo hS p q hq hqNorm
    have hsum :
        ∑ n ∈ Finset.Icc L L,
            Real.rpow 3 (-((L - n : ℕ) : ℝ)) *
              expectedJDifference M L n L p q = 0 := by
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.sub_self,
        Nat.cast_zero, neg_zero]
      unfold expectedJDifference
      simp only [sub_self, MeasureTheory.integral_zero, mul_zero]
    have hpowZero : Real.rpow 3 (-((L - L : ℕ) : ℝ)) = 1 := by norm_num
    rw [hsum, mul_zero, add_zero, hpowZero]
    have hforcing0 : 0 ≤ delta1 * (delta1 + 1) := by positivity
    calc
      expectedJ M L L p q ≤ delta1 := hbase
      _ ≤ delta1 * (delta1 + 1) := by nlinarith [sq_nonneg delta1]
      _ ≤ C * delta1 * (delta1 + 1) := by
        calc
          delta1 * (delta1 + 1) = 1 * (delta1 * (delta1 + 1)) := by ring
          _ ≤ C * (delta1 * (delta1 + 1)) :=
            mul_le_mul_of_nonneg_right (hCgate.trans hCgateC) hforcing0
          _ = C * delta1 * (delta1 + 1) := by ring
  · have hLmPrev : L ≤ m - 1 := by omega
    have hgateWeak :
        Cgate * Real.rpow 3 (-((m - L : ℕ) : ℝ)) ≤ 1 / 4 := by
      exact (mul_le_mul_of_nonneg_right hCgateC
        (Real.rpow_nonneg (by norm_num) _)).trans hscale
    have hgateStrongNat := hgateBridge (m - L) hgateWeak
    have hgap :
        ((((m : ℤ) - (L : ℤ) : ℤ) : ℝ)) = ((m - L : ℕ) : ℝ) := by
      congr 1
      omega
    have hgateStrong :
        Cvar * Real.rpow 3
            (-(3 / 4 : ℝ) * (((m : ℤ) - (L : ℤ) : ℤ) : ℝ)) ≤ 1 / 4 := by
      rw [hgap]
      exact hgateStrongNat
    have hraw := hvariance M L m hm hLmPrev hgateStrong hxiTwo hS le_rfl
      p q hq hqNorm
    have hbadGate : Cbad * xi * M.delta ^ 2 ≤ delta1 := by
      calc
        Cbad * xi * M.delta ^ 2 ≤ C * xi * M.delta ^ 2 := by gcongr
        _ ≤ delta1 := hdeltaGate
    have hbadBound := hbad M L m xi delta1 hdim hbadGate hdeltaSmall hS
      hm hLmPrev p q hq hqNorm
    let R : ℝ := delta1 *
      (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ)))
    let D : ℝ := ∑ n ∈ Finset.Icc L m,
      Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
        expectedJDifference M L n m p q
    let B : ℝ := ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d in
      (coarseEllipticityGoodEvent M L m)ᶜ,
        Ch04.restrictionResponseJObservableCubeSet
          (Homogenization.originCube d ((m : ℤ) - 1)) p q
          (aCutoffRegCoeffField M L omega) ∂M.P.toMeasure
    have hraw' : expectedJ M L m p q ≤ Cvar * R + Cvar * D + 2 * B := by
      simpa only [R, D, B, mul_assoc] using hraw
    have hbad' : B ≤ Cbad * delta1 ^ 2 := by
      simpa only [B] using hbadBound
    have hD0 : 0 ≤ D := by
      dsimp only [D]
      apply Finset.sum_nonneg
      intro n hn
      have hdiff : 0 ≤ expectedJDifference M L n m p q := by
        rw [expectedJDifference_eq_sub_unconditional]
        exact sub_nonneg.mpr
          (expectedJ_le_of_scale_le M L n m (Finset.mem_Icc.mp hn).2 p q)
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hdiff
    have hrate0 : 0 ≤ Real.rpow 3 (-((m - L : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hR0 : 0 ≤ R := by dsimp only [R]; positivity
    have hsquareR : delta1 ^ 2 ≤ R := by
      dsimp only [R]
      nlinarith
    calc
      expectedJ M L m p q ≤ Cvar * R + Cvar * D + 2 * B := hraw'
      _ ≤ Cvar * R + Cvar * D + 2 * (Cbad * delta1 ^ 2) := by
        gcongr
      _ ≤ (Cvar + 2 * Cbad) * R + Cvar * D := by
        have hCB0 : 0 ≤ Cbad := le_trans zero_le_one hCbad
        have hscaled := mul_le_mul_of_nonneg_left hsquareR
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCB0)
        ring_nf at hscaled ⊢
        nlinarith
      _ ≤ C * R + C * D := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hCsumC hR0)
          (mul_le_mul_of_nonneg_right hCvarC hD0)
      _ = C * delta1 *
            (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ))) +
          C * ∑ n ∈ Finset.Icc L m,
            Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
              expectedJDifference M L n m p q := by
        dsimp only [R, D]
        ring

end

end SubdiffusiveProcess.Providers.Section4
