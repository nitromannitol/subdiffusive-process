module

public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane3.BandFiltration
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess SubdiffusiveProcess.Lane3 MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Paper
noncomputable section



def branch_candidate_setup
    (d : ℕ) (Q : TopologicalSpace.Opens (SpatialCoordinates d))
    (Y : ℤ → Type) [∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [∀ j, IsProbabilityMeasure (laws j)]
    (Idx : Type) [Countable Idx] (Src : Type) [Countable Src]
    (resp : Idx → ℕ → ((j : ℤ) → Y j) → ℝ)
    (respLim : Idx → ((j : ℤ) → Y j) → ℝ)
    (source : Src → DomainL2 Q) (sourceCoord : Src → Idx)
    (G : ((j : ℤ) → Y j) → (DomainL2 Q →L[ℝ] DomainL2 Q))
    (E : ((j : ℤ) → Y j) → DomainL2 Q → EReal)
    (orders : Finset ℝ) (disorder a c : ℝ) : Prop :=
  let P := Measure.infinitePi laws
  (0 < disorder ∧ 0 < a ∧ 0 < c ∧ ∀ p ∈ orders, 1 ≤ p) ∧
  (∀ ω u, E ω u = limitFormEnergy (G ω) u) ∧
  (∀ src ω, respLim (sourceCoord src) ω = inner ℝ (source src) (G ω (source src))) ∧
  (∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ (i : Idx) (p : ℝ), p ∈ orders →
    AEStronglyMeasurable (respLim i) P ∧
    Tendsto (fun N => eLpNorm (fun ω => resp i (phi N) ω - respLim i ω)
      (ENNReal.ofReal p) P) atTop (𝓝 0)) ∧
  (∀ p ∈ orders, ∀ i : Idx, ∃ Cp : ℝ, 0 < Cp ∧ ∀ H N : ℕ, H ≤ N →
    eLpNorm (fun ω => resp i N ω - (P[resp i N | bandSigma Y H]) ω)
      (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * disorder ^ c * (3 : ℝ) ^ (-(a * (H : ℝ)))))

end
end Paper
