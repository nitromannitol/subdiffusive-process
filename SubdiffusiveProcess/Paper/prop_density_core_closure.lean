module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.ResponseMoments.PositiveDensity
public import SubdiffusiveProcess.ResponseMoments.Forms
public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem prop_density_core_closure
    (Hs : Type) [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]
    (X : Type) [MeasurableSpace X]
    (E F : DomainedEnergy Hs X)
    (core : Set Hs) (hcore : core ⊆ (E.dom : Set Hs))
    (Cstar a : ℝ) (hCstar : 0 < Cstar) (ha : 0 < a)
    (hglue : ∀ (u : Hs) (hu : u ∈ core) (eps : ℝ), 0 < eps →
      ∃ (w : Hs) (hw : w ∈ F.dom), ‖w - u‖ ≤ eps ∧
        F.formAt w hw ≤ Cstar * a * E.formAt u (hcore hu) + eps)
    (hclosed : ∀ (u : Hs) (w : ℕ → Hs) (hw : ∀ k, w k ∈ F.dom) (c : ℝ),
      Tendsto w atTop (𝓝 u) → (∀ k, F.formAt (w k) (hw k) ≤ c) →
      ∃ hu : u ∈ F.dom, F.formAt u hu ≤ c)
    (hdense : ∀ (v : Hs) (hv : v ∈ E.dom) (eps : ℝ), 0 < eps →
      ∃ (u : Hs) (hu : u ∈ core), ‖u - v‖ ≤ eps ∧
        E.formAt u (hcore hu) ≤ E.formAt v hv + eps) :
    ∀ (v : Hs) (hv : v ∈ E.dom), ∃ hvF : v ∈ F.dom,
      F.formAt v hvF ≤ Cstar * a * E.formAt v hv :=
  positive_density_comparison Hs X E F core hcore Cstar a hCstar ha hglue hclosed hdense

end SubdiffusiveProcess.Paper
