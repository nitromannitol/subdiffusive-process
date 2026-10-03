module

public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousApprox
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace DirichletForm.FOTConstruction
variable {X : Type*} [TopologicalSpace X]

/-- A summable bound on successive differences gives a continuous pointwise limit. -/
lemma qc_uniform_limit (fn : ℕ → X → ℝ)
    (hf : ∀ n, Continuous (fn n)) (hb : ∀ n, ∃ C, ∀ x, ‖fn n x‖ ≤ C)
    (N : ℕ) (S : Set X)
    (hgap : ∀ n x, x ∈ S → |fn (n + N + 1) x - fn (n + N) x| ≤ qcRate (n + N)) :
    ContinuousOn (fun x => limUnder atTop (fun n => fn n x)) S ∧
      ∀ x ∈ S, Tendsto (fun n => fn n x) atTop
        (𝓝 (limUnder atTop (fun n => fn n x))) := by
  classical
  choose C hC using hb
  let gn : ℕ → BoundedContinuousFunction S ℝ := fun n => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : S => fn (n + N) x) ((hf _).comp continuous_subtype_val) (C _) (fun x => hC _ x)
  have hdist : ∀ n, dist (gn n) (gn (n + 1)) ≤ qcRate (n + N) := by
    intro n
    apply (BoundedContinuousFunction.dist_le (qcRate_nonneg _)).mpr
    intro x
    change dist (fn (n + N) x) (fn (n + 1 + N) x) ≤ _
    rw [Real.dist_eq, abs_sub_comm]
    simpa only [Nat.add_right_comm n 1 N] using hgap n x x.2
  have hc : CauchySeq gn := cauchySeq_of_dist_le_of_summable _ hdist
    (qcRate_summable.comp_injective (fun n k hh => Nat.add_right_cancel hh))
  let g : BoundedContinuousFunction S ℝ := limUnder atTop gn
  have hg : Tendsto gn atTop (𝓝 g) := hc.tendsto_limUnder
  have hpoint : ∀ x : S, Tendsto (fun n => fn n x) atTop (𝓝 (g x)) := by
    intro x
    have hh : Tendsto (fun n => gn n x) atTop (𝓝 (g x)) :=
      (continuous_eval_const x).tendsto g |>.comp hg
    exact (tendsto_add_atTop_iff_nat N).mp hh
  have heq : ∀ x : S, limUnder atTop (fun n => fn n x) = g x := fun x => (hpoint x).limUnder_eq
  refine ⟨?_, ?_⟩
  · apply continuousOn_iff_continuous_restrict.mpr
    have hh : S.domRestrict (fun x => limUnder atTop (fun n => fn n x)) = g := funext heq
    rw [hh]
    exact g.continuous
  · intro x hx
    rw [heq ⟨x, hx⟩]
    exact hpoint ⟨x, hx⟩

end DirichletForm.FOTConstruction
