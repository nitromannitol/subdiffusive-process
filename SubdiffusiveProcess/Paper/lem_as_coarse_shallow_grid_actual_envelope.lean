import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_envelope_exponential
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_numeric_tail
import Homogenization.Book.Ch02.MultiscaleEllipticity

open MeasureTheory
open Homogenization
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The geometric envelope instantiated with the actual finite test set at
each retained depth. The cardinality is derived, not hypothesized. -/
theorem lem_as_coarse_shallow_grid_actual_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d : ℕ)
    (X : ℕ → (((ℕ × TriadicCube d) × Bool) × Fin 4) → Ω → ℝ)
    (p B0 eta rho : ℝ)
    (hp : 0 < p) (hB0 : 0 ≤ B0)
    (heta : eta < rho)
    (hrate : (d : ℝ) < p * (rho - eta))
    (hX : ∀ k i,
      i ∈ aux_lem_as_coarse_shallow_grid_numeric_tail_level d k →
        AEStronglyMeasurable (X k i) P)
    (hLp : ∀ k i,
      i ∈ aux_lem_as_coarse_shallow_grid_numeric_tail_level d k →
        eLpNorm (X k i) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ)))) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, 1 ≤ K ∧
      ∀ k i,
        i ∈ aux_lem_as_coarse_shallow_grid_numeric_tail_level d k →
          |X k i ω| ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  apply lem_as_coarse_shallow_grid_envelope_exponential P
    (aux_lem_as_coarse_shallow_grid_numeric_tail_level d) X
    (d : ℝ) p B0 8 eta rho hp hB0 (by norm_num) heta hrate
  · intro k
    rw [aux_lem_as_coarse_shallow_grid_numeric_tail_level_card]
    have hpow : ((3 ^ d : ℕ) ^ k : ℝ) =
        (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) := by
      calc
        ((3 ^ d : ℕ) ^ k : ℝ) = ((3 : ℝ) ^ d) ^ k := by norm_cast
        _ = ((3 : ℝ) ^ (d : ℝ)) ^ (k : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        _ = (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [Nat.cast_mul, Nat.cast_pow, hpow]
    norm_num
  · exact hX
  · exact hLp

end Paper

