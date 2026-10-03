module

public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Paper.lem_finite_trace_holder_beta_bound
public import SubdiffusiveProcess.Paper.lem_finite_trace_holder_finite_net

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess

namespace Paper



theorem lem_finite_trace_holder_precompact
    (d : ℕ) (hd : 2 ≤ d)
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧
      (∀ g : SpatialCoordinates d → ℝ,
        IsCellBoundaryClass alpha 0 1 g → cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
          IsCellBoundaryClass beta 0 1 g ∧ cellBoundaryQuotientNorm beta 0 1 g ≤ C) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∃ Gs : Finset (SpatialCoordinates d → ℝ),
          (∀ h ∈ Gs, IsCellBoundaryClass alpha 0 1 h ∧
            cellBoundaryQuotientNorm alpha 0 1 h ≤ 1) ∧
          (∀ g : SpatialCoordinates d → ℝ,
            IsCellBoundaryClass alpha 0 1 g → cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
              ∃ h ∈ Gs,
                IsCellBoundaryClass beta 0 1 (fun x => g x - h x) ∧
                cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) ≤ epsilon)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    lem_finite_trace_holder_beta_bound d hd beta alpha hbeta hba halpha
  exact ⟨C, hCpos, hC,
    lem_finite_trace_holder_finite_net d hd beta alpha hbeta hba halpha⟩


end Paper
