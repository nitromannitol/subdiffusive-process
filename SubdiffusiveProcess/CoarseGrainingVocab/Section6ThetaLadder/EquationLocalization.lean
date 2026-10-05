module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.LocalizedFamily

@[expose] public section

/-!
# Theta-perturbed cutoff Hölder ladder: equation localization

The multiscale coefficient family uses a measurable extension of the
normalized multiplier outside the collar.  This file verifies that the
extension does not alter the weak equation on any comparison window contained
in that collar.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ}

/-- Weak harmonicity depends only on the coefficient restricted to the
equation domain. -/
theorem isWeaklyHarmonicOn_congr_coeff
    {a a' : Vec d → ℝ} {W : Set (Vec d)} {u : H1Function W}
    (hW : MeasurableSet W) (haa' : ∀ x ∈ W, a x = a' x) :
    IsWeaklyHarmonicOn a W u ↔ IsWeaklyHarmonicOn a' W u := by
  constructor <;> intro hu phi
  · rw [← hu phi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hW] with x hx
    rw [haa' x hx]
  · rw [← hu phi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hW] with x hx
    rw [haa' x hx]

/-- On a window inside the collar, the localized-family equation is exactly
the normalized physical theta equation. -/
theorem isWeaklyHarmonicOn_localizedThetaCutoff_iff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B W : Set (Vec d)} (hW : MeasurableSet W) (hWB : W ⊆ B)
    {b : ℝ} (theta : Vec d → ℝ)
    {u : H1Function W} :
    IsWeaklyHarmonicOn (localizedThetaCutoff M L omega B b theta) W u ↔
      IsWeaklyHarmonicOn (normalizedThetaCutoff M L omega b theta) W u := by
  apply isWeaklyHarmonicOn_congr_coeff hW
  intro x hx
  simp [localizedThetaCutoff, localizedNormalizedMultiplier, hWB hx,
    normalizedThetaCutoff, normalizedMultiplier]

/-- A physical theta-harmonic function is harmonic for the localized
normalized family on every comparison window inside the collar. -/
theorem isWeaklyHarmonicOn_localizedThetaCutoff_of_physical
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B W : Set (Vec d)} (hW : MeasurableSet W) (hWB : W ⊆ B)
    {b : ℝ} (hb : 0 < b)
    (theta : Vec d → ℝ) {u : H1Function W}
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x) W u) :
    IsWeaklyHarmonicOn (localizedThetaCutoff M L omega B b theta) W u := by
  rw [isWeaklyHarmonicOn_localizedThetaCutoff_iff M L omega hW hWB]
  exact (isWeaklyHarmonicOn_iff_normalizedThetaCutoff M L omega hb theta).mp hu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
