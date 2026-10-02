import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.UpperDensity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped Topology BigOperators

namespace Paper
noncomputable section



def parameter_chain (d H1 : ℕ) (eta0 D theta eps0 alpha eta s0 L Cd pad : ℝ)
    (ratio ratioAt : ℕ → ℝ) (levelOf : ℕ → ℕ)
    (padded : SpatialCoordinates d → ℝ → OddGridIndex d (subdivisionHalfWidth H1) → Prop)
    (density : (ℕ → Prop) → ℝ) : Prop :=
  0 < eta0 ∧ eta0 < 1 / 3 ∧
  8 * (d : ℝ) / eta0 ≤ D ∧ theta ≤ eta0 / 8 ∧ eps0 = eta0 / 8 ∧
  2 * (1 - alpha) + eta < eps0 ∧
  s0 = (d : ℝ) - 2 + 2 * alpha - eta ∧ (d : ℝ) - eps0 < s0 ∧
  0 < H1 ∧ L = (3 : ℝ) ^ H1 ∧ 1 ≤ Cd ∧ 1 ≤ pad ∧
  2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8) ∧
  (∀ n, levelOf n = H1 * n) ∧ (∀ n, ratioAt n = ratio (levelOf n)) ∧
  (∀ z R (hR : 0 < R) i, padded z R i ↔
    Metric.closedBall (oddGridCenter z R (subdivisionHalfWidth H1) i)
      (pad * (R / (2 * (subdivisionHalfWidth H1 : ℝ) + 1)) / 2) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
  (∀ z R (hR : 0 < R),
    (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) // ¬ padded z R i} : ℝ) ≤
      Cd * L ^ ((d : ℝ) - 1)) ∧
  (∀ S : ℕ → Prop, density S = Filter.limsup
    (fun J : ℕ => (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧ S n} : ℝ) / (J : ℝ))
    Filter.atTop) ∧
  (∀ S, density S = SubdiffusiveProcess.Lane3.upperDensity S)

end
end Paper
