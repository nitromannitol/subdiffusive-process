module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

@[expose] public section

open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction

namespace SubdiffusiveProcess

/-- Products of a unital multiplicatively closed separating family determine finite product laws. -/
theorem measure_eq_of_separating_product_integrals
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {k : ℕ}
    (A : Set (X →ᵇ ℝ)) (h1 : (1 : X →ᵇ ℝ) ∈ A)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (μ ν : Measure (Fin k → X)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (heq : ∀ f : Fin k → (X →ᵇ ℝ), (∀ i, f i ∈ A) →
      (∫ x, ∏ i : Fin k, f i (x i) ∂μ) = ∫ x, ∏ i : Fin k, f i (x i) ∂ν) :
    μ = ν := by
  let tensor (f : Fin k → (X →ᵇ ℝ)) : (Fin k → X) →ᵇ ℝ :=
    ∏ i, (f i).compContinuous
      ⟨(fun x : Fin k → X => x i), continuous_apply i⟩
  let T : Submonoid ((Fin k → X) →ᵇ ℝ) := {
    carrier := {g | ∃ f : Fin k → (X →ᵇ ℝ), (∀ i, f i ∈ A) ∧ tensor f = g}
    one_mem' := by
      refine ⟨fun _ => 1, fun i => h1, ?_⟩
      ext x
      simp [tensor]
    mul_mem' := by
      rintro g h ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      refine ⟨fun i => f i * g i, fun i => hmul _ (hf i) _ (hg i), ?_⟩
      ext x
      simp [tensor, Finset.prod_mul_distrib] }
  let B : Subalgebra ℝ ((Fin k → X) →ᵇ ℝ) := Algebra.adjoin ℝ (T : Set _)
  let C : StarSubalgebra ℝ ((Fin k → X) →ᵇ ℝ) := {
    toSubalgebra := B
    star_mem' := by
      intro g hg
      have hstar : star g = g := by
        ext x
        simp only [BoundedContinuousFunction.star_apply, star_trivial]
      simpa only [hstar] using hg }
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
      (A := C)
  · intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    obtain ⟨f, hfA, hf⟩ := hsep (x i) (y i) hi
    let fs : Fin k → (X →ᵇ ℝ) := Function.update (fun _ => 1) i f
    have hfs : ∀ j, fs j ∈ A := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [fs] using hfA
      · simp [fs, hji, h1]
    refine ⟨tensor fs, ?_, ?_⟩
    · refine ⟨(tensor fs).toContinuousMap, ?_, rfl⟩
      refine ⟨tensor fs, ?_, rfl⟩
      change tensor fs ∈ B
      exact Algebra.subset_adjoin ⟨fs, hfs, rfl⟩
    · have htensor (z : Fin k → X) : tensor fs z = f (z i) := by
        simp only [tensor, BoundedContinuousFunction.coe_prod, Finset.prod_apply,
          BoundedContinuousFunction.compContinuous_apply]
        change (∏ j, fs j (z j)) = f (z i)
        have hz : (fun j => fs j (z j)) =
            Function.update (fun _ => (1 : ℝ)) i (f (z i)) := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [fs]
          · simp [fs, hji]
        rw [hz, Finset.prod_update_of_mem (Finset.mem_univ i)]
        simp
      rw [htensor x, htensor y]
      exact hf
  · intro g hg
    change g ∈ B at hg
    have hB : B.toSubmodule = Submodule.span ℝ (T : Set _) := by
      dsimp only [B]
      rw [Algebra.adjoin_eq_span, T.closure_eq]
    have hg' : g ∈ Submodule.span ℝ (T : Set _) := by
      rw [← hB]
      exact hg
    let V : Submodule ℝ ((Fin k → X) →ᵇ ℝ) := {
      carrier := {g | (∫ x, g x ∂μ) = ∫ x, g x ∂ν}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg
        change (∫ x, (f + g) x ∂μ) = ∫ x, (f + g) x ∂ν
        simpa only [BoundedContinuousFunction.coe_add, Pi.add_apply,
          integral_add (BoundedContinuousFunction.integrable _ _)
            (BoundedContinuousFunction.integrable _ _)] using congrArg₂ (· + ·) hf hg
      smul_mem' := by
        intro c f hf
        change (∫ x, (c • f) x ∂μ) = ∫ x, (c • f) x ∂ν
        simpa only [BoundedContinuousFunction.coe_smul, Pi.smul_apply,
          integral_smul] using congrArg (c • ·) hf }
    change g ∈ V
    apply (Submodule.span_le.mpr ?_) hg'
    intro q hq
    obtain ⟨f, hf, rfl⟩ := hq
    change (∫ x, tensor f x ∂μ) = ∫ x, tensor f x ∂ν
    simpa [tensor] using heq f hf

end SubdiffusiveProcess
