import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic

/-! This module establishes window pullback for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
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
