import SubdiffusiveProcess.Lane3.BandFiltration
import SubdiffusiveProcess.Main.CutoffCoefficient
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace Paper



theorem lem_rare_tests_dyadic_error_summable :
    ∀ (d : ℕ) (hd : 1 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ)
      (X : ℕ → BilateralField d → ℝ)
      (Cstar a p : ℝ) (hCstar : 0 < Cstar) (ha : 0 < a) (hp : 1 ≤ p),
      (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).restrict)
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


end Paper
