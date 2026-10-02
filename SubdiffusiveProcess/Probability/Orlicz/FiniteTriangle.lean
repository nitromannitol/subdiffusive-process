import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit

/-! The exact-scale finite Orlicz triangle inequality. -/
open MeasureTheory
noncomputable section
namespace SubdiffusiveProcess.Probability.Orlicz
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma ogammaLE_finset_sum {σ : ℝ} (hσ : 1 ≤ σ) {ι : Type*}
    (I : Finset ι) (hI : I.Nonempty) {X : ι → Ω → ℝ} {a : ι → ℝ}
    (ha : ∀ k ∈ I, 0 < a k) (hXm : ∀ k ∈ I, AEMeasurable (X k) μ)
    (hX : ∀ k ∈ I, SubdiffusiveProcess.OGammaLE μ σ (a k) (X k)) :
    SubdiffusiveProcess.OGammaLE μ σ (∑ k ∈ I, a k) (fun ω => ∑ k ∈ I, X k ω) := by
  classical
  revert hI ha hXm hX
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    intro hI ha hm hX
    by_cases hne : I.Nonempty
    · have ha' : ∀ k ∈ I, 0 < a k := fun k hk => ha k (Finset.mem_insert_of_mem hk)
      have hm' : ∀ k ∈ I, AEMeasurable (X k) μ := fun k hk => hm k (Finset.mem_insert_of_mem hk)
      have hX' : ∀ k ∈ I, SubdiffusiveProcess.OGammaLE μ σ (a k) (X k) := fun k hk => hX k (Finset.mem_insert_of_mem hk)
      have hs : 0 < ∑ k ∈ I, a k := Finset.sum_pos ha' hne
      have hsum : AEMeasurable (fun ω => ∑ k ∈ I, X k ω) μ := by
        convert Finset.aemeasurable_sum I hm' using 1
        ext ω
        simp only [Finset.sum_apply]
      have h := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_add
        (ha i (Finset.mem_insert_self _ _)) hs hσ
        (hm i (Finset.mem_insert_self _ _)) hsum
        (hX i (Finset.mem_insert_self _ _)) (ih hne ha' hm' hX')
      simpa only [Finset.sum_insert hi] using h
    · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst I
      simpa using
        hX i (Finset.mem_insert_self _ _)

end SubdiffusiveProcess.Probability.Orlicz
