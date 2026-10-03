module

public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Lane2.LimitForm
public import Mathlib.Data.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper
noncomputable section



def order_of_parameters
    (d : ℕ)
    (alpha eta t beta s eta0 D theta eps0 zeta gamma : ℝ)
    (chooseL : (Fin 11 → ℝ) → ℝ)
    (chooseOrders : (Fin 11 → ℝ) → ℝ → Finset ℝ)
    (chooseFirst : (Fin 11 → ℝ) → ℝ → Finset ℝ → ℝ × ℝ)
    (chooseImprovement : (Fin 11 → ℝ) → ℝ → Finset ℝ → (ℝ × ℝ) → (ℝ × ℝ × ℝ))
    (chooseFinal : (Fin 11 → ℝ) → ℝ → Finset ℝ → (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℝ)
    (Lused : ℝ → ℝ) (ordersUsed : ℝ → Finset ℝ)
    (firstUsed : ℝ → ℝ × ℝ) (improvementUsed : ℝ → ℝ × ℝ × ℝ)
    (finalUsed : ℝ → ℝ) : Prop :=
  let exponents : Fin 11 → ℝ := ![alpha, eta, t, beta, s, eta0, D, theta, eps0, zeta, gamma]
  let L := chooseL exponents
  let orders := chooseOrders exponents L
  let first := chooseFirst exponents L orders
  let geometry := chooseImprovement exponents L orders first
  let final := chooseFinal exponents L orders first geometry
  1 < L ∧ 0 < first.1 ∧ 1 ≤ first.2 ∧ 0 < geometry.1 ∧ 0 < geometry.2.1 ∧
    0 < geometry.2.2 ∧ 0 < final ∧ final ≤ first.1 ∧
    (∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ first.1 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        in_joint_extracted_candidates d model H Ω P field z r hr S GN GE GF NE NF →
        ∀ᵐ omega ∂P, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            (first.2)⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
              (limitFormEnergy (GF i omega) u).toReal ∧
            (limitFormEnergy (GF i omega) u).toReal ≤
              first.2 * (limitFormEnergy (GE i omega) u).toReal) ∧
    (∀ gap : ℝ, 0 ≤ gap → Lused gap = L ∧ ordersUsed gap = orders ∧
      firstUsed gap = first ∧ improvementUsed gap = geometry ∧ finalUsed gap = final)

end
end Paper
