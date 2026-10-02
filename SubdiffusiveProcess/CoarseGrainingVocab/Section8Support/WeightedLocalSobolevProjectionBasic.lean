import Homogenization.Besov.Poincare.Projection
import Mathlib.MeasureTheory.Function.LpSpace.Complete
set_option autoImplicit false
open Homogenization MeasureTheory
open scoped ENNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

theorem weightedProjection_residual_memLp {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (j : ℕ) (hu : MemLp u 2 (normalizedCubeMeasure Q)) : MemLp (cubeProjectionResidual Q j u) 2 (normalizedCubeMeasure Q) := by
  unfold cubeProjectionResidual
  exact hu.sub (cubeProjection_memLp Q j 2 u)

theorem weightedProjection_increment_memLp {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (j : ℕ) (p : ℝ≥0∞) : MemLp (cubeIncrement Q (j + 1) u) p (normalizedCubeMeasure Q) := by
  rw [cubeIncrement_succ]
  exact MemLp.sub (cubeProjection_memLp Q (j + 1) p u) (cubeProjection_memLp Q j p u)

theorem weightedProjection_telescope {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (n : ℕ) : (fun x => ∑ j ∈ Finset.range n, cubeIncrement Q (j + 1) u x) = cubeProjectionGap Q 0 n u := by
  have h := sum_cubeIncrement_eq_cubeProjectionGap Q u 0 n
  simpa using h

theorem weightedProjection_gap_ae {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (n : ℕ) : cubeProjectionGap Q 0 n u =ᵐ[normalizedCubeMeasure Q] (fun x => cubeProjection Q n u x - cubeAverage Q u) := by
  have h := cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth (Q:=Q) (R:=Q) (j:=0) u (by simp)
  filter_upwards [h] with x hx
  simp [cubeProjectionGap, hx]

theorem weightedProjection_ae_transfer {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q) (P : Vec d → Prop) (hP : ∀ᵐ x ∂normalizedCubeMeasure Q, P x) : ∀ᵐ x ∂ν, P x := by
  exact hν.ae_le hP

theorem weightedProjection_finite_sum_norm {d : ℕ} (ν : Measure (Vec d)) (v : ℕ → Vec d → ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) (n : ℕ) (hv : ∀ j, AEStronglyMeasurable (v j) ν) : eLpNorm (∑ j ∈ Finset.range n, v j) p ν ≤ ∑ j ∈ Finset.range n, eLpNorm (v j) p ν := by
  exact eLpNorm_sum_le (fun j _ => hv j) hp

theorem weightedProjection_fatou {d : ℕ} (ν : Measure (Vec d)) (v : ℕ → Vec d → ℝ) (u : Vec d → ℝ) (p A : ℝ≥0∞) (hv : ∀ j, AEStronglyMeasurable (v j) ν) (hbound : ∀ j, eLpNorm (v j) p ν ≤ A) (hlim : ∀ᵐ x ∂ν, Filter.Tendsto (fun j => v j x) Filter.atTop (𝓝 (u x))) : eLpNorm u p ν ≤ A := by
  exact Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound) hv hlim

theorem weightedProjection_increment_residual {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (j : ℕ) : cubeIncrement Q (j + 1) u = fun x => cubeProjectionResidual Q j u x - cubeProjectionResidual Q (j + 1) u x := by
  funext x
  simp only [cubeIncrement_succ, cubeProjectionResidual]
  ring

theorem weightedProjection_sum_bound {ι : Type*} (s : Finset ι) (a b : ι → ℝ≥0∞) (h : ∀ i ∈ s, a i ≤ b i) : ∑ i ∈ s, a i ≤ ∑ i ∈ s, b i := by
  exact Finset.sum_le_sum h

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
