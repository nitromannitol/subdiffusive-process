import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.OscillationSubsetReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SandwichNondegeneracy
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

/-- On a positive finite-measure subwindow, centered normalized `L²` is at
most the literal oscillation on any larger set with a bounded pair carrier. -/
theorem normalizedL2On_centered_le_oscillationOn
    {W D : Set (Vec d)} {f : Vec d → ℝ}
    (hWmeas : MeasurableSet W) (hWpos : 0 < (volume W).toReal)
    (hWtop : volume W ≠ ⊤) (hW : W.Nonempty) (hsub : W ⊆ D)
    (hf : IntegrableOn f W) (hf2 : IntegrableOn (fun x ↦ f x ^ 2) W)
    (hbdd : BddAbove {q : ℝ | ∃ x ∈ D, ∃ y ∈ D,
      q = |f x - f y|}) :
    normalizedL2On W
        (fun x ↦ f x - averageOn W f) ≤ oscillationOn D f := by
  obtain ⟨x, hx⟩ := hW
  have hosc0 : 0 ≤ oscillationOn D f := by
    unfold oscillationOn
    exact le_csSup hbdd ⟨x, hsub hx, x, hsub hx, by simp⟩
  have hpoint : ∀ y ∈ W, |f y - f x| ≤ oscillationOn D f := by
    intro y hy
    unfold oscillationOn
    exact le_csSup hbdd ⟨y, hsub hy, x, hsub hx, rfl⟩
  have hmean := Section6Iteration.normalizedL2On_sub_volumeAverage_le
    hWmeas hWpos hWtop hf hf2 (f x)
  have hmem : MemLp (fun y ↦ f y - f x) 2 (volume.restrict W) := by
    have hmeas := hf.aestronglyMeasurable.sub
      (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : Vec d ↦ f x) (volume.restrict W))
    apply (memLp_two_iff_integrable_sq hmeas).2
    have hlinear : IntegrableOn (fun y ↦ 2 * f x * f y) W :=
      hf.const_mul (2 * f x)
    have hconst : IntegrableOn (fun _ : Vec d ↦ (f x) ^ 2) W :=
      integrableOn_const hWtop
    have hid : (fun y ↦ (f y - f x) ^ 2) =
        fun y ↦ f y ^ 2 - 2 * f x * f y + (f x) ^ 2 := by
      funext y
      ring
    change IntegrableOn (fun y ↦ (f y - f x) ^ 2) W
    rw [hid]
    exact (hf2.sub hlinear).add hconst
  have hbound : ∀ᵐ y ∂volume.restrict W,
      |f y - f x| ≤ oscillationOn D f := by
    filter_upwards [ae_restrict_mem hWmeas] with y hy
    exact hpoint y hy
  exact hmean.trans
    (Section6SchauderDatum.normalizedL2On_le_of_ae_abs_le
      hWpos hWtop hosc0 hmem hbound)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
