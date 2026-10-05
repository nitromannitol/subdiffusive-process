module

public import SubdiffusiveProcess.ResponseMoments.BandFiltration
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper



theorem lem_rare_tests_dyadic_condExp_ae_limit :
    ∀ (d : ℕ) (_hd : 1 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ)
      (X : ℕ → BilateralField d → ℝ),
      (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                C(SpatialCoordinates d, ℝ)));
        (∀ (m H0 : ℕ), 0 < H0 →
          ∀ ε : ℝ, 0 < ε →
            (∑' ell : ℕ, P {ω | ENNReal.ofReal ε ≤
              ‖X m ω - (P[X m | Bsym (2 ^ ell * H0)]) ω‖ₑ}) ≠ ∞) →
        ∀ (m H0 : ℕ), 0 < H0 →
          ∀ᵐ ω ∂P, Tendsto
            (fun ell : ℕ => (P[X m | Bsym (2 ^ ell * H0)]) ω)
            atTop (𝓝 (X m ω))) := by
  intro d hd _ _ P hP center X
  dsimp only
  intro h m H0 hH0
  have hkey : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᶠ ell in atTop,
      dist ((P[X m | MeasurableSpace.comap
        ((Set.Icc (center - ((2 ^ ell * H0 : ℕ) : ℤ))
          (center + ((2 ^ ell * H0 : ℕ) : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (center - ((2 ^ ell * H0 : ℕ) : ℤ))
            (center + ((2 ^ ell * H0 : ℕ) : ℤ))) →
              C(SpatialCoordinates d, ℝ)))]) ω) (X m ω) <
        (1 : ℝ) / (n + 1) := by
    rw [ae_all_iff]
    intro n
    have hεn : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hbc := ae_eventually_notMem (μ := P)
      (h m H0 hH0 (1 / (n + 1)) hεn)
    filter_upwards [hbc] with ω hω
    exact hω.mono fun ell hle => by
      rw [not_le] at hle
      rw [Real.enorm_eq_ofReal_abs] at hle
      have hlt : |X m ω - (P[X m | MeasurableSpace.comap
          ((Set.Icc (center - ((2 ^ ell * H0 : ℕ) : ℤ))
            (center + ((2 ^ ell * H0 : ℕ) : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (center - ((2 ^ ell * H0 : ℕ) : ℤ))
              (center + ((2 ^ ell * H0 : ℕ) : ℤ))) →
                C(SpatialCoordinates d, ℝ)))]) ω| < 1 / (n + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff hεn).mp hle
      rw [dist_comm, Real.dist_eq]
      exact hlt
  filter_upwards [hkey] with ω hω
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 : ℝ) / (n + 1) < ε := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    rw [div_lt_iff₀ hε] at hN
    nlinarith [hε, hN]
  exact (hω n).mono fun ell he => lt_trans he hn


end SubdiffusiveProcess.Paper
