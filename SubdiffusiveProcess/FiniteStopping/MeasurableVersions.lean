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

/-! This module establishes measurable version for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- measurable version in the finite stopping construction. -/
theorem measurable_version {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (hf : ∀ n, AEMeasurable (f n) μ)
    (g : Ω → ℝ) (h : TendstoInMeasure μ f atTop g) :
    ∃ g' : Ω → ℝ, Measurable g' ∧ g' =ᵐ[μ] g := by
  obtain ⟨ns, -, hae⟩ := h.exists_seq_tendsto_ae
  have hg : AEMeasurable g μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hf (ns n)) hae
  exact ⟨hg.mk g, hg.measurable_mk, hg.ae_eq_mk.symm⟩

end SubdiffusiveProcess.FiniteStopping
