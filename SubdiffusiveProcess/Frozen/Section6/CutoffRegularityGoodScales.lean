import SubdiffusiveProcess.Providers.Section6.CutoffRegularityGoodScales

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable


theorem SubdiffusiveProcess.Frozen.Section6.cutoff_regularity_good_scales
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ L : ℕ,
      (∀ s epsilon theta : ℝ, s ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
        theta ∈ Set.Ioc 0 1 →
        C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤ theta →
        ∀ m0 K : ℕ,
          M.P.toMeasure {ω | (∑ m ∈ Finset.Icc m0 (m0 + K),
              if ω ∈ goodEvent M (some L) m 0 epsilon s then (1 : ℝ) else 0) /
                (K + 1) ≤ 1 - theta} ≤
            ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
              (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1)))) ∧
      (∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s → ∀ n m : ℕ, n ≤ m →
          ∀ z : Vec d,
            OGammaLE M.P.toMeasure 2
              (C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| /
                Real.sqrt (m - n + 1))
              (fun ω => (∑ k ∈ Finset.Icc n m,
                accumulatedError M (some L) k z s ω) / (m - n + 1) -
                  C * s ^ (-7 / 2 : ℝ) * M.delta)) ∧
      (∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ lambda ∈ Set.Ioc (0 : ℝ) 1,
          C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| ≤ lambda →
          ∀ m : ℕ, ∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℤ,
            (∀ ω, X ω ∈ Set.Icc (-1 : ℤ) m) ∧
            OGammaLE M.P.toMeasure 1
              (C * s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| * lambda⁻¹ ^ 2)
              (fun ω => max ((((m : ℤ) - X ω).toNat : ℝ) - 1) 0) ∧
            (∀ ω, 0 ≤ (m : ℤ) - X ω ∧
              ∀ n : ℕ, (n : ℤ) ≤ X ω →
                ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
                  ∑ j ∈ Finset.Icc n m, accumulatedError M (some L) j z s ω ≤
                    lambda * ((m : ℝ) - (n : ℝ)))) ∧
      (∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ epsilon ∈ Set.Ioc 0 1, ∀ lambda ∈ Set.Ioc (0 : ℝ) 1,
          C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| ≤ lambda →
          C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta| ≤ lambda →
          ∀ m : ℕ, ∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℤ,
            (∀ ω, X ω ∈ Set.Icc (-1 : ℤ) m) ∧
            OGammaLE M.P.toMeasure 1
              (C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ *
                M.delta ^ 2 * |Real.log M.delta|)
              (fun ω => max ((((m : ℤ) - X ω).toNat : ℝ) - 1) 0) ∧
            (∀ ω, 0 ≤ (m : ℤ) - X ω ∧
              ∀ n : ℕ, (n : ℤ) ≤ X ω →
                ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
                  (∑ j ∈ Finset.Icc n m,
                    (1 - if ω ∈ goodEvent M (some L) j z epsilon s then 1 else 0)) <
                    1 + lambda * ((m : ℝ) - (n : ℝ)))) ∧
      (∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, ∀ z : Vec d,
          ∀ ω,
            indicatorValue (goodEvent M (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s ω) ∧
            indicatorValue (goodEvent M (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon)

:= SubdiffusiveProcess.Providers.Section6.cutoff_regularity_good_scales d
