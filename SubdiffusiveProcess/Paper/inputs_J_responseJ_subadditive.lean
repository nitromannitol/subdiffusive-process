module

public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_J_responseJ_subadditive (d : ℕ) (hd : 2 ≤ d) :
    (∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.CoeffField d) (lam Lam : ℝ),
      Homogenization.IsEllipticFieldOn lam Lam (U : Set (Homogenization.Vec d)) a →
      ∀ (n : ℕ) (V : Fin n → Set (Homogenization.Vec d)),
        (∀ i, MeasurableSet (V i)) →
        (∀ i, V i ⊆ (U : Set (Homogenization.Vec d))) →
        (∀ i j, i ≠ j → volume (V i ∩ V j) = 0) →
        volume ((U : Set (Homogenization.Vec d)) \ ⋃ i, V i) = 0 →
      ∀ p q : Homogenization.Vec d,
      Homogenization.ResponseJ (U : Set (Homogenization.Vec d)) p q a ≤
        ∑ i : Fin n,
          (volume.real (V i) / volume.real (U : Set (Homogenization.Vec d))) *
            Homogenization.ResponseJ (V i) p q a) := by
  intro U a lam Lam hEll n V hV hsub hdisj hcov p q
  exact aux_in_J_responseJ_subadditive U a lam Lam hEll n V hV hsub hdisj hcov p q

end Paper

