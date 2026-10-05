module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic

@[expose] public section

/-! This module establishes window pullback for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- window pullback in the finite stopping construction. -/
theorem window_pullback {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (Θ : Ω → Ω) (hΘ : MeasurePreserving Θ P P)
    (band band' : ℕ+ → MeasurableSpace Ω)
    (hband : ∀ h, band h ≤ mΩ)
    (hΘband : ∀ h, @Measurable Ω Ω (band' h) (band h) Θ)
    (W0 : ℕ+ → Set Ω) (hW0 : ∀ h, MeasurableSet[band h] (W0 h))
    (B : ℝ) (H0 : ℕ)
    (hprob : ∀ h : ℕ+, P (W0 h) ≤ ENNReal.ofReal (Real.exp (-(B * (h : ℝ)))))
    (hempty : ∀ h : ℕ+, (h : ℕ) < H0 → W0 h = ∅)
    (Q : Ω → Prop) (hQ : ∀ᵐ x ∂P, x ∉ ⋃ h : ℕ+, W0 h → Q x) :
    ∃ W : ℕ+ → Set Ω,
      (∀ h, MeasurableSet[band' h] (W h)) ∧
      (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-(B * (h : ℝ))))) ∧
      (∀ h : ℕ+, (h : ℕ) < H0 → W h = ∅) ∧
    (∀ᵐ x ∂P, x ∉ ⋃ h : ℕ+, W h → Q (Θ x)) := by
  refine ⟨fun h => Θ ⁻¹' W0 h, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hΘband h (hW0 h)
  · intro h
    rw [hΘ.measure_preimage (MeasurableSet.nullMeasurableSet (hband h (W0 h) (hW0 h)))]
    exact hprob h
  · intro h hh
    simp only [hempty h hh, preimage_empty]
  · filter_upwards [hΘ.quasiMeasurePreserving.ae hQ] with x hx hnot
    apply hx
    intro hmem
    obtain ⟨h, hh⟩ := Set.mem_iUnion.1 hmem
    exact hnot (Set.mem_iUnion.2 ⟨h, hh⟩)

end SubdiffusiveProcess.FiniteStopping
