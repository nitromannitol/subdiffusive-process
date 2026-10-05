module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.OffGridTriadicWindows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TriadicTargetReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SandwichNondegeneracy

@[expose] public section

/-!
# Theta ladder: off-grid centered rows

This module transfers one centered normalized-`L²` row from a grid cube to
an arbitrary point-centred cube one scale below it.  The mean-minimizing
property is used before the ordinary square-root volume-ratio restriction.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-- A centered normalized-`L²` row restricts from a translated cube to a
nested cube one scale below it with the exact `sqrt (3^d)` price. -/
theorem normalizedL2On_centered_le_sqrt_three_of_subset_succ
    {ell : ℤ} {zInner zOuter : Vec d} {f : Vec d → ℝ}
    (hsub : translatedCube d ell zInner ⊆
      translatedCube d (ell + 1) zOuter)
    (hf : IntegrableOn f (translatedCube d (ell + 1) zOuter))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2)
      (translatedCube d (ell + 1) zOuter)) :
    normalizedL2On (translatedCube d ell zInner)
        (fun x ↦ f x - averageOn (translatedCube d ell zInner) f) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On (translatedCube d (ell + 1) zOuter)
          (fun x ↦ f x -
            averageOn (translatedCube d (ell + 1) zOuter) f) := by
  let W := translatedCube d ell zInner
  let Q := translatedCube d (ell + 1) zOuter
  have hWmeas : MeasurableSet W := by
    dsimp only [W]
    rw [translatedCube_eq_metricBall]
    exact measurableSet_ball
  have hWpos : 0 < (volume W).toReal :=
    volume_translatedCube_toReal_pos ell zInner
  have hWtop : volume W ≠ ⊤ := volume_translatedCube_ne_top ell zInner
  have hfW : IntegrableOn f W := hf.mono_set hsub
  have hf2W : IntegrableOn (fun x ↦ f x ^ 2) W := hf2.mono_set hsub
  have hmean := normalizedL2On_sub_volumeAverage_le hWmeas hWpos hWtop
    hfW hf2W (averageOn Q f)
  have hQpos : 0 < (volume Q).toReal :=
    volume_translatedCube_toReal_pos (ell + 1) zOuter
  have hcenterSq : IntegrableOn
      (fun x ↦ (f x - averageOn Q f) ^ 2) Q := by
    have hlinear : IntegrableOn
        (fun x ↦ 2 * averageOn Q f * f x) Q :=
      hf.const_mul (2 * averageOn Q f)
    have hconst : IntegrableOn
        (fun _ : Vec d ↦ averageOn Q f ^ 2) Q :=
      integrableOn_const (volume_translatedCube_ne_top (ell + 1) zOuter)
    have hid : (fun x ↦ (f x - averageOn Q f) ^ 2) =
        fun x ↦ f x ^ 2 - 2 * averageOn Q f * f x +
          averageOn Q f ^ 2 := by
      funext x
      ring
    rw [hid]
    exact (hf2.sub hlinear).add hconst
  have hrestrict := normalizedL2On_le_of_subset hsub hQpos hWpos hcenterSq
  have hratio : Real.sqrt ((volume Q).toReal / (volume W).toReal) =
      Real.sqrt ((3 : ℝ) ^ d) := by
    dsimp only [Q, W]
    simpa only [add_sub_cancel_right] using
      sqrt_consecutive_translatedCube_volumeRatio_twoCenters
        (d := d) (ell + 1) zInner zOuter
  rw [hratio] at hrestrict
  exact hmean.trans hrestrict

/-- The relative grid-centre construction and the previous restriction
lemma convert any uniform scale-`s+1` grid row into the point-centred
scale-`s` row used by the finite telescope. -/
theorem pointCenteredRow_of_uniformGridSuccRow
    {m s : ℕ} (hsm : s + 3 ≤ m) {z x : Vec d}
    (hx : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {f : Vec d → ℝ} {A : ℝ}
    (hgrid : ∀ q : Vec d, OnTriadicGrid s q → q ∈ cube d (m : ℤ) →
      IntegrableOn f (translatedCube d ((s : ℤ) + 1) (z + q)) ∧
      IntegrableOn (fun y ↦ f y ^ 2)
        (translatedCube d ((s : ℤ) + 1) (z + q)) ∧
      normalizedL2On (translatedCube d ((s : ℤ) + 1) (z + q))
          (fun y ↦ f y - averageOn
            (translatedCube d ((s : ℤ) + 1) (z + q)) f) ≤ A) :
    normalizedL2On (translatedCube d (s : ℤ) x)
        (fun y ↦ f y - averageOn (translatedCube d (s : ℤ) x) f) ≤
      Real.sqrt ((3 : ℝ) ^ d) * A := by
  obtain ⟨q, hqgrid, hqmem, hsub, _htop⟩ :=
    exists_relativeGridCentre_with_campanatoWindows hsm hx
  obtain ⟨hf, hf2, hrow⟩ := hgrid q hqgrid hqmem
  have hrestrict := normalizedL2On_centered_le_sqrt_three_of_subset_succ
    (ell := (s : ℤ)) (zInner := x) (zOuter := z + q) (f := f)
    (by simpa only using hsub) hf hf2
  exact hrestrict.trans
    (mul_le_mul_of_nonneg_left hrow (Real.sqrt_nonneg _))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
