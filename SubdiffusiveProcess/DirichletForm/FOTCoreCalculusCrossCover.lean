module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusSigned

@[expose] public section

open MeasureTheory Filter Set

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X]

/-- A finitely additive set function satisfying local bounds satisfies the same bound on a cover. -/
theorem additive_error_on_finite_cover {μ : Measure X} [IsFiniteMeasure μ]
    (T : Set X → ℝ) (hT0 : T ∅ = 0)
    (hTadd : ∀ A B : Set X, MeasurableSet A → MeasurableSet B → Disjoint A B →
      T (A ∪ B) = T A + T B) {ι : Type*} (s : Finset ι) (O : ι → Set X) {C : ℝ}
    (hO : ∀ i ∈ s, MeasurableSet (O i))
    (hlocal : ∀ i ∈ s, ∀ B : Set X, MeasurableSet B → B ⊆ O i → |T B| ≤ C * (μ B).toReal)
    {B : Set X} (hB : MeasurableSet B) (hcover : B ⊆ ⋃ i ∈ s, O i) :
    |T B| ≤ C * (μ B).toReal := by
  classical
  induction s using Finset.induction_on generalizing B with
  | empty =>
    have hBe : B = ∅ := by simpa only [Finset.notMem_empty, iUnion_of_empty,
      iUnion_empty, subset_empty_iff] using hcover
    simp only [hBe, hT0, measure_empty, ENNReal.toReal_zero, abs_zero, mul_zero, le_refl]
  | insert a s ha ih =>
    have hOa := hO a (Finset.mem_insert_self a s)
    have hOrest : ∀ i ∈ s, MeasurableSet (O i) :=
      fun i hi => hO i (Finset.mem_insert_of_mem hi)
    have hlrest : ∀ i ∈ s, ∀ A : Set X, MeasurableSet A → A ⊆ O i → |T A| ≤ C * (μ A).toReal :=
      fun i hi => hlocal i (Finset.mem_insert_of_mem hi)
    have hrestcover : B \ O a ⊆ ⋃ i ∈ s, O i := by
      intro x hx
      have h := hcover hx.1
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left] at h
      exact h.resolve_left hx.2
    have h1 := hlocal a (Finset.mem_insert_self a s) (B ∩ O a) (hB.inter hOa)
      inter_subset_right
    have h2 := ih hOrest hlrest (hB.diff hOa) hrestcover
    have hdisj : Disjoint (B ∩ O a) (B \ O a) :=
      disjoint_left.mpr fun x hx hy => hy.2 hx.2
    have hdecomp : B = (B ∩ O a) ∪ (B \ O a) := (inter_union_sdiff B (O a)).symm
    have hm : (μ B).toReal = (μ (B ∩ O a)).toReal + (μ (B \ O a)).toReal := by
      conv_lhs => rw [hdecomp]
      rw [measure_union hdisj (hB.diff hOa),
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have ht : T B = T (B ∩ O a) + T (B \ O a) := by
      conv_lhs => rw [hdecomp]
      exact hTadd _ _ (hB.inter hOa) (hB.diff hOa) hdisj
    rw [ht, hm]
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

theorem signedIntegralOn_inter_carrier (ν : SignedMeasure X) {K B : Set X}
    (_hK : MeasurableSet K) (hB : MeasurableSet B) (hν : ν.totalVariation Kᶜ = 0)
    (f : X → ℝ) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν (B ∩ K) f =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f := by
  have hz : ν.toJordanDecomposition.posPart Kᶜ = 0 ∧
      ν.toJordanDecomposition.negPart Kᶜ = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hν
  have hp : ν.toJordanDecomposition.posPart.restrict K = ν.toJordanDecomposition.posPart :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hz.1)
  have hn : ν.toJordanDecomposition.negPart.restrict K = ν.toJordanDecomposition.negPart :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hz.2)
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn]
  rw [← Measure.restrict_restrict hB, hp, ← Measure.restrict_restrict hB, hn]

theorem signed_apply_inter_carrier (ν : SignedMeasure X) {K B : Set X}
    (hK : MeasurableSet K) (hB : MeasurableSet B) (hν : ν.totalVariation Kᶜ = 0) :
    ν (B ∩ K) = ν B := by
  have hz : ν (B \ K) = 0 := ν.null_of_totalVariation_zero
    ((measure_mono (sdiff_subset_compl B K)).trans_eq hν |>.antisymm bot_le)
  have hd : Disjoint (B ∩ K) (B \ K) := disjoint_left.mpr fun x hx hy => hy.2 hx.2
  have hh := ν.of_union hd (hB.inter hK) (hB.diff hK)
  rw [inter_union_sdiff, hz, add_zero] at hh
  exact hh.symm

end SubdiffusiveProcess.DirichletForm.FOTConstruction
