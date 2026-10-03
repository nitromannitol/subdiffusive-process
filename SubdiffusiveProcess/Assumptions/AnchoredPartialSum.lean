module

public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Frozen.Assumptions.PotentialSample
public import Mathlib.Topology.MetricSpace.UniformConvergence

@[expose] public section

/-!
# Finite anchored potential sums

This module supplies the additive potential-field operations and finite anchored
sums used to state convergence of the logarithmic coefficient.
-/

-- REUSE-CANDIDATE: Algsuperdiff/Section3/Provider/Stream/ShellSum.lean

namespace SubdiffusiveProcess.Frozen.Assumptions

open Filter Homogenization Topology
open scoped BigOperators

noncomputable section

namespace PotentialField

variable {d : ℕ}

/-- Pointwise addition of potential fields and their stored derivatives. -/
-- Adapted from Algsuperdiff/Section3/Provider/Stream/ShellSum.lean
def add (g h : PotentialField d) : PotentialField d :=
  ⟨(g.1.1 + h.1.1, deriv g + deriv h), by
    constructor
    · intro x
      exact (g.hasFDerivAt x).add (h.hasFDerivAt x)
    · intro K hK
      obtain ⟨Cg, hg⟩ := g.2.2 K hK
      obtain ⟨Ch, hh⟩ := h.2.2 K hK
      exact ⟨Cg + Ch, hg.add hh⟩⟩

@[simp]
theorem add_apply (g h : PotentialField d) (x : Vec d) :
    add g h x = g x + h x :=
  rfl

@[simp]
theorem add_deriv (g h : PotentialField d) (x : Vec d) :
    deriv (add g h) x = deriv g x + deriv h x :=
  rfl

/-- Subtract the value at the origin without changing the derivative. -/
def anchor (g : PotentialField d) : PotentialField d :=
  ⟨(⟨fun x ↦ g x - g 0, g.1.1.continuous.sub continuous_const⟩, deriv g), by
    constructor
    · intro x
      exact (g.hasFDerivAt x).sub_const (g 0)
    · exact g.2.2⟩

@[simp]
theorem anchor_apply (g : PotentialField d) (x : Vec d) :
    anchor g x = g x - g 0 :=
  rfl

@[simp]
theorem anchor_deriv (g : PotentialField d) (x : Vec d) :
    deriv (anchor g) x = deriv g x :=
  rfl

@[simp]
theorem anchor_origin (g : PotentialField d) : anchor g 0 = 0 := by
  rw [anchor_apply, sub_self]

end PotentialField

variable {d : ℕ}

/-- The finite anchored logarithmic sum
`S_L(ω,x) = ∑_{k=0}^L (g_k(x) - g_k(0))`. -/
def anchoredPartialSum (omega : PotentialSample d) (L : ℕ) (x : Vec d) : ℝ :=
  ∑ k ∈ Finset.range (L + 1), (omega k x - omega k 0)

/-- The finite anchored sum on the `PotentialField` carrier. -/
def anchoredPartialSumField (omega : PotentialSample d) : ℕ → PotentialField d
  | 0 => PotentialField.anchor (omega 0)
  | L + 1 => PotentialField.add (anchoredPartialSumField omega L)
      (PotentialField.anchor (omega (L + 1)))

@[simp]
theorem anchoredPartialSumField_apply (omega : PotentialSample d) (L : ℕ)
    (x : Vec d) :
    anchoredPartialSumField omega L x = anchoredPartialSum omega L x := by
  induction L with
  | zero =>
      simp only [anchoredPartialSumField, PotentialField.anchor_apply,
        anchoredPartialSum, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add]
  | succ L ih =>
      rw [anchoredPartialSumField, PotentialField.add_apply, ih,
        PotentialField.anchor_apply]
      change
        (∑ k ∈ Finset.range (L + 1), (omega k x - omega k 0)) +
            (omega (L + 1) x - omega (L + 1) 0) =
          ∑ k ∈ Finset.range ((L + 1) + 1), (omega k x - omega k 0)
      exact (Finset.sum_range_succ _ _).symm

/-- Cauchy convergence of a derivative sequence in the Lipschitz seminorm on
one set. -/
def LipschitzSeminormCauchyOn
    (F : ℕ → Vec d → (Vec d →L[ℝ] ℝ)) (K : Set (Vec d)) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    LipschitzOnWith (Real.toNNReal epsilon) (fun x ↦ F m x - F n x) K

end

end SubdiffusiveProcess.Frozen.Assumptions
