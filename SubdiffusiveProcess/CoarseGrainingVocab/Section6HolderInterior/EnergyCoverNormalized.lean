module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyCoverAdditivity

@[expose] public section

/-!
# The energy cover in the row-2 carriers

`EnergyCoverAdditivity` gives the cover bound for integrals; the rows are
written in `normalizedL2On` / `vectorNormalizedL2On`.  This module converts.

The only subtlety is the degenerate volume: `normalizedL2On` divides by
`(volume U).toReal`, which is `0` both when `U` is null and when `U` has
infinite measure.  Requiring `volume U ≠ ⊤` separates the two, and in the null
case both sides of the conversion vanish.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- `∫_U f² = |U| · ‖f‖²_{L̲²(U)}` on a finite-measure window. -/
theorem setIntegral_sq_eq_volume_mul_normalizedL2On_sq {U : Set (Vec d)}
    {f : Vec d → ℝ} (hfin : volume U ≠ ⊤) :
    ∫ p in U, f p ^ 2 ∂volume = (volume U).toReal * normalizedL2On U f ^ 2 := by
  rw [Section6Iteration.normalizedL2On_sq]
  unfold volumeAverage
  rcases eq_or_ne (volume U) 0 with h0 | h0
  · have hrestrict : volume.restrict U = 0 := by
      rw [Measure.restrict_eq_zero]; exact h0
    rw [hrestrict]
    simp [h0]
  · have htoReal : (volume U).toReal ≠ 0 := by
      simp only [ne_eq, ENNReal.toReal_eq_zero_iff]
      push Not
      exact ⟨h0, hfin⟩
    field_simp

/-- **The energy cover in `normalizedL2On` form.**  A window covered by finitely
many windows of no larger volume, each with seminorm at most `N`, has seminorm
at most `√(card) · N`. -/
theorem normalizedL2On_le_of_cover_finset {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {f : Vec d → ℝ}
    {N : ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y))
    (hint : ∀ y, IntegrableOn (fun p => f p ^ 2) (Wf y) volume)
    (hcover : W ⊆ ⋃ y ∈ S, Wf y)
    (hWpos : 0 < (volume W).toReal)
    (hfin : ∀ y ∈ S, volume (Wf y) ≠ ⊤)
    (hvol : ∀ y ∈ S, (volume (Wf y)).toReal ≤ (volume W).toReal)
    (hN : ∀ y ∈ S, normalizedL2On (Wf y) f ≤ N) (hN0 : 0 ≤ N) :
    normalizedL2On W f ≤ Real.sqrt (S.card : ℝ) * N := by
  have hcard0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  refine Section6Iteration.normalizedL2On_le_of_sq_le (by positivity) ?_
  -- each piece contributes at most |W| · N²
  have hpiece : ∀ y ∈ S,
      ∫ p in Wf y, f p ^ 2 ∂volume ≤ (volume W).toReal * N ^ 2 := by
    intro y hy
    rw [setIntegral_sq_eq_volume_mul_normalizedL2On_sq (hfin y hy)]
    have hsq : normalizedL2On (Wf y) f ^ 2 ≤ N ^ 2 := by
      have h0 := Section6Iteration.normalizedL2On_nonneg (Wf y) f
      nlinarith [hN y hy, h0]
    have hvy : (0 : ℝ) ≤ (volume (Wf y)).toReal := ENNReal.toReal_nonneg
    calc (volume (Wf y)).toReal * normalizedL2On (Wf y) f ^ 2
        ≤ (volume (Wf y)).toReal * N ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hvy
      _ ≤ (volume W).toReal * N ^ 2 :=
          mul_le_mul_of_nonneg_right (hvol y hy) (by positivity)
  -- sum the cover
  have hsum : ∫ p in W, f p ^ 2 ∂volume ≤
      (S.card : ℝ) * ((volume W).toReal * N ^ 2) := by
    refine (setIntegral_le_of_cover_finset hmeas (fun p => sq_nonneg (f p))
      hint hcover).trans ?_
    calc ∑ y ∈ S, ∫ p in Wf y, f p ^ 2 ∂volume
        ≤ ∑ _y ∈ S, (volume W).toReal * N ^ 2 :=
          Finset.sum_le_sum hpiece
      _ = (S.card : ℝ) * ((volume W).toReal * N ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- divide by |W|
  have hsqrt : (Real.sqrt (S.card : ℝ) * N) ^ 2 = (S.card : ℝ) * N ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcard0]
  rw [hsqrt]
  unfold volumeAverage
  rw [inv_mul_le_iff₀ hWpos]
  calc ∫ p in W, f p ^ 2 ∂volume
      ≤ (S.card : ℝ) * ((volume W).toReal * N ^ 2) := hsum
    _ = (volume W).toReal * ((S.card : ℝ) * N ^ 2) := by ring

/-- **The energy cover for a vector field** — the shape row 2's
left-hand side uses.  `vectorNormalizedL2On` is `normalizedL2On` of the
Euclidean norm, so the scalar cover applies verbatim. -/
theorem vectorNormalizedL2On_le_of_cover_finset {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {f : Vec d → Vec d}
    {N : ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y))
    (hint : ∀ y, IntegrableOn
      (fun p => Homogenization.euclideanNorm (f p) ^ 2) (Wf y) volume)
    (hcover : W ⊆ ⋃ y ∈ S, Wf y)
    (hWpos : 0 < (volume W).toReal)
    (hfin : ∀ y ∈ S, volume (Wf y) ≠ ⊤)
    (hvol : ∀ y ∈ S, (volume (Wf y)).toReal ≤ (volume W).toReal)
    (hN : ∀ y ∈ S, vectorNormalizedL2On (Wf y) f ≤ N) (hN0 : 0 ≤ N) :
    vectorNormalizedL2On W f ≤ Real.sqrt (S.card : ℝ) * N :=
  normalizedL2On_le_of_cover_finset hmeas hint hcover hWpos hfin hvol hN hN0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
