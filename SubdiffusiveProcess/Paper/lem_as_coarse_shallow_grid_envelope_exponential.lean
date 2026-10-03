module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_envelope_rate

@[expose] public section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The retained-grid almost-sure envelope from the paper's explicit
cardinality and exponential moment rates. No summability premise remains. -/
theorem lem_as_coarse_shallow_grid_envelope_exponential
    {Ω α : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : ℕ → Finset α)
    (X : ℕ → α → Ω → ℝ)
    (d p B0 Cg eta rho : ℝ)
    (hp : 0 < p) (hB0 : 0 ≤ B0) (hCg : 0 ≤ Cg)
    (heta : eta < rho) (hrate : d < p * (rho - eta))
    (hcard : ∀ k : ℕ,
      ((G k).card : ℝ) ≤ Cg * (3 : ℝ) ^ (d * (k : ℝ)))
    (hX : ∀ k i, i ∈ G k → AEStronglyMeasurable (X k i) P)
    (hLp : ∀ k i, i ∈ G k →
      eLpNorm (X k i) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ)))) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, 1 ≤ K ∧
      ∀ k i, i ∈ G k →
        |X k i ω| ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  apply lem_as_coarse_shallow_grid_envelope P G X p
    (fun k => B0 * (3 : ℝ) ^ (eta * (k : ℝ)))
    (fun k => (3 : ℝ) ^ (rho * (k : ℝ))) hp
  · intro k
    positivity
  · exact hX
  · exact hLp
  · have hsum := lem_as_coarse_shallow_grid_envelope_rate G
      d p B0 Cg eta rho hp hB0 hCg heta hrate hcard
    convert hsum using 1

end Paper

