module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support
public import SubdiffusiveProcess.Providers.Section6.GoodScaleMathcalE

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable


theorem SubdiffusiveProcess.Frozen.Section6.good_scale_mathcal_e
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, m ≤ L → ∀ ω,
        indicatorValue (goodEvent M none m 0 1 s)
            (fun ω' => section6HomogenizationError M s L m ω' 0) ω ≤
          C * sSup {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
              ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
              r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
                Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
                  t = section6Response M n n ω z e})} +
            C * s⁻¹ * M.delta ^ 2 +
            C * sSup {r : ℝ | ∃ j ≤ m,
              r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
                supNormOn (cube d m) (shellBlock m j ω)} +
            C * (3 : ℝ) ^ (-(s / 8) * m) *
              supNormOn (cube d m)
                (fun x => ∑ i ∈ Finset.range (m + 1), ω i x) +
            (C * ∑' j : ℕ, if m ≤ j then
              (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (ω j)) else 0) ∧
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          ω ∈ goodEvent M none m 0 epsilon s →
            section6HomogenizationError M s L m ω 0 ≤ C * epsilon

:= SubdiffusiveProcess.Providers.Section6.good_scale_mathcal_e d
