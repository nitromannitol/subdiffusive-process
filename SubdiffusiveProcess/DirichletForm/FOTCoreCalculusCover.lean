module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusDomination

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X]

/-- A local integral error bounded by a measure adds over a finite measurable cover. -/
theorem integral_error_on_finite_cover {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : X → ℝ} (hf : Integrable f ν)
    {ι : Type*} (s : Finset ι) (O : ι → Set X) {C : ℝ}
    (hO : ∀ i ∈ s, MeasurableSet (O i))
    (hlocal : ∀ i ∈ s, ∀ B : Set X, MeasurableSet B → B ⊆ O i →
      |(μ B).toReal - ∫ x in B, f x ∂ν| ≤ C * (ν B).toReal)
    {B : Set X} (hB : MeasurableSet B) (hcover : B ⊆ ⋃ i ∈ s, O i) :
    |(μ B).toReal - ∫ x in B, f x ∂ν| ≤ C * (ν B).toReal := by
  classical
  induction s using Finset.induction_on generalizing B with
  | empty =>
    have hBe : B = ∅ := by simpa only [Finset.notMem_empty, iUnion_of_empty,
      iUnion_empty, subset_empty_iff] using hcover
    simp only [hBe, measure_empty, ENNReal.toReal_zero, setIntegral_empty, sub_zero, abs_zero,
      mul_zero, le_refl]
  | insert a s ha ih =>
    have hOa := hO a (Finset.mem_insert_self a s)
    have hOrest : ∀ i ∈ s, MeasurableSet (O i) :=
      fun i hi => hO i (Finset.mem_insert_of_mem hi)
    have hlrest : ∀ i ∈ s, ∀ A : Set X, MeasurableSet A → A ⊆ O i →
        |(μ A).toReal - ∫ x in A, f x ∂ν| ≤ C * (ν A).toReal :=
      fun i hi => hlocal i (Finset.mem_insert_of_mem hi)
    have hrestcover : B \ O a ⊆ ⋃ i ∈ s, O i := by
      intro x hx
      have h := hcover hx.1
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left] at h
      exact h.resolve_left hx.2
    have h1 := hlocal a (Finset.mem_insert_self a s) (B ∩ O a) (hB.inter hOa)
      inter_subset_right
    have h2 := ih hOrest hlrest (hB.diff hOa) hrestcover
    have hdisj : Disjoint (B ∩ O a) (B \ O a) := by
      exact disjoint_left.mpr fun x hx hy => hy.2 hx.2
    have hdecomp : B = (B ∩ O a) ∪ (B \ O a) := (inter_union_diff B (O a)).symm
    have hm : (μ B).toReal = (μ (B ∩ O a)).toReal + (μ (B \ O a)).toReal := by
      conv_lhs => rw [hdecomp]
      rw [measure_union hdisj (hB.diff hOa),
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have hn : (ν B).toReal = (ν (B ∩ O a)).toReal + (ν (B \ O a)).toReal := by
      conv_lhs => rw [hdecomp]
      rw [measure_union hdisj (hB.diff hOa),
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have hi : (∫ x in B, f x ∂ν) = (∫ x in B ∩ O a, f x ∂ν) +
        ∫ x in B \ O a, f x ∂ν := by
      conv_lhs => rw [hdecomp]
      exact setIntegral_union hdisj (hB.diff hOa) hf.integrableOn hf.integrableOn
    rw [hm, hi, hn]
    calc
      _ = |((μ (B ∩ O a)).toReal - ∫ x in B ∩ O a, f x ∂ν) +
          ((μ (B \ O a)).toReal - ∫ x in B \ O a, f x ∂ν)| := by congr 1; ring
      _ ≤ |(μ (B ∩ O a)).toReal - ∫ x in B ∩ O a, f x ∂ν| +
          |(μ (B \ O a)).toReal - ∫ x in B \ O a, f x ∂ν| := abs_add_le _ _
      _ ≤ C * (ν (B ∩ O a)).toReal + C * (ν (B \ O a)).toReal := add_le_add h1 h2
      _ = _ := by ring

end DirichletForm.FOTConstruction
