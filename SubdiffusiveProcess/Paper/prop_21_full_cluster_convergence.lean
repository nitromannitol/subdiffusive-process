import SubdiffusiveProcess.Paper.prop_21_dual_energy_operator_unique
import SubdiffusiveProcess.Lane2.LimitForm

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



theorem prop_21_full_cluster_convergence
    (T : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hGpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (hclusters : ∀ tau : ℕ → ℕ, StrictMono tau →
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        ∃ F : DomainL2 Q →L[ℝ] DomainL2 Q,
          Tendsto (fun n => T (tau (sigma n))) atTop (𝓝 F) ∧
          (∀ u : DomainL2 Q, limitFormEnergy F u = limitFormEnergy G u) ∧
          (∀ x y : DomainL2 Q, inner ℝ (F x) y = inner ℝ x (F y)) ∧
          (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (F x))) :
    Tendsto T atTop (𝓝 G) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨sigma, hsigma, F, hF, henergy, hFsym, hFpos⟩ := hclusters (ns ∘ φ) hnsφ
  have hFG : F = G := prop_21_dual_energy_operator_unique F G hFsym hGsym hFpos hGpos henergy
  exact ⟨φ ∘ sigma, by simpa [Function.comp, hFG] using hF⟩


end Paper
