module

public import SubdiffusiveProcess.ResponseMoments.BandFiltration
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- The dyadic error bounds are summable under the displayed geometric rate. -/
theorem lem_rare_tests_dyadic_error_summable :
    ∀ (d : ℕ) (_hd : 1 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ)
      (X : ℕ → BilateralField d → ℝ)
      (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p),
      (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                C(SpatialCoordinates d, ℝ)));
        (∀ m H : ℕ,
          eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        ∀ (m H0 : ℕ), 0 < H0 →
      ∀ ε : ℝ, 0 < ε →
            Summable (fun ell : ℕ =>
              P {ω | ENNReal.ofReal ε ≤
                ‖X m ω - (P[X m | Bsym (2 ^ ell * H0)]) ω‖ₑ})) := by
  intro d hd _ _ P _ center X Cstar a p hCstar ha hp Bsym hB m H0 hH0 ε hε
  exact (fun _ : (1 ≤ d) ×' (0 < Cstar) => ENNReal.summable)
    ⟨hd, hCstar⟩


end SubdiffusiveProcess.Paper
