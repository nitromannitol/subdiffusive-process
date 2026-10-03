module

public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem rem_repair :
  ∀ (Cd : ℝ), 0 < Cd →
  ∀ (errOrig errFold badOrig badFold ratioOrig ratioFold : ℕ → ℝ),
    
    (∀ j, errFold j ≤ Cd * errOrig j) →
    (∀ j, badFold j ≤ Cd * badOrig j) →
    (∀ j, ratioFold j ≤ Cd * ratioOrig j) →
    -- the tolerance of the good events, tightened by the same dimensional factor
    ∀ eps : ℝ, 0 < eps →
      (∀ j, errOrig j ≤ eps / Cd → errFold j ≤ eps) ∧
      (∀ j, badOrig j ≤ eps / Cd → badFold j ≤ eps) ∧
      (∀ j, ratioOrig j ≤ eps / Cd → ratioFold j ≤ eps) := by
  intro Cd hCd errOrig errFold badOrig badFold ratioOrig ratioFold herr hbad hratio eps _heps
  have key : ∀ (u v : ℕ → ℝ), (∀ j, v j ≤ Cd * u j) → ∀ j, u j ≤ eps / Cd → v j ≤ eps := by
    intro u v huv j hj
    refine (huv j).trans ?_
    calc Cd * u j ≤ Cd * (eps / Cd) := by
          exact mul_le_mul_of_nonneg_left hj hCd.le
      _ = eps := by field_simp
  exact ⟨key _ _ herr, key _ _ hbad, key _ _ hratio⟩

end Paper
