module

public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section
namespace Paper



def sum_errors_baseline_input (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∀ s eps : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 → eps ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ CD deltaD : ℝ → ℝ,
      (∀ q : ℝ, 1 ≤ q → 0 < CD q ∧ 0 < deltaD q) ∧
      ∀ q : ℝ, 1 ≤ q →
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ min 1 (deltaD q) →
          ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
                omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
          ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
            (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
            (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
              primitive_scores d M s eps (eta N omega)
                (fun m y => F N m y omega) (fun m y => Praw N m y omega)
                (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
                (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
            ∀ (N n : ℕ) (z : Vec d),
              MemLp (fun omega => (Draw N n z omega).toReal)
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
              eLpNorm (fun omega => (Draw N n z omega).toReal)
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
                ENNReal.ofReal (CD q * M.delta ^ (1 / 2 : ℝ))

end Paper
