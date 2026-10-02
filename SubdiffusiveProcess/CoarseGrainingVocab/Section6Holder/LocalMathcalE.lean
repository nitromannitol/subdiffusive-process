import SubdiffusiveProcess.Frozen.Section6.GoodScaleMathcalE
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

/-!
# Hölder Step 3: translated good-scale homogenization-error cap

The proved `p.good.scale.mathcal.E` is anchored at the origin.  Translation
covariance turns its second clause into the local estimate used in the
Hölder recurrence.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section

/-- The origin-centred proved cap, simultaneously at every translated
centre. -/
theorem exists_section6HomogenizationError_le_of_local_goodEvent (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, m ≤ L → ∀ omega z,
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          omega ∈ goodEvent M none m z epsilon s →
            section6HomogenizationError M s L m omega z ≤ C * epsilon := by
  obtain ⟨C, hC, hcap⟩ := SubdiffusiveProcess.Frozen.Section6.good_scale_mathcal_e d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m hmL omega z epsilon hepsilon hgood
  have hgood0 : translatePotentialSample z omega ∈
      goodEvent M none m 0 epsilon s :=
    (Section6Covariance.mem_goodEvent_translatePotentialSample
      M none m 0 epsilon s z omega).2 (by simpa only [add_zero] using hgood)
  have h := (hcap M s hs L m hmL (translatePotentialSample z omega)).2
    epsilon hepsilon hgood0
  rw [Section6Covariance.section6HomogenizationError_eq_translate_zero]
  exact h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
