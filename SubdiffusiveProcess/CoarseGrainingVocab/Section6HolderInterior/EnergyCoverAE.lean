import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyCoverNormalized

/-!
# The energy cover under an a.e. cover

The concrete grid cover of an off-grid window is only an *a.e.* cover: the
scale-`j` windows are open boxes, so the grid hyperplanes between them are
missed.  That set is null, and `L²` integrals do not see it.

`MeasureTheory.setIntegral_mono_set` already takes its set inclusion in the form
`s ≤ᵐ[μ] t`, so the relaxation costs nothing — the strict-`⊆` statements of
`EnergyCoverAdditivity` / `EnergyCoverNormalized` are the special case obtained
by `Filter.Eventually.of_forall`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- Energy additivity under an a.e. finite cover. -/
theorem setIntegral_le_of_aecover_finset {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {g : Vec d → ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y)) (hg0 : ∀ p, 0 ≤ g p)
    (hint : ∀ y, IntegrableOn g (Wf y) volume)
    (hcover : W ≤ᵐ[volume] ⋃ y ∈ S, Wf y) :
    ∫ p in W, g p ∂volume ≤ ∑ y ∈ S, ∫ p in Wf y, g p ∂volume := by
  have hUint : IntegrableOn g (⋃ y ∈ S, Wf y) volume :=
    integrableOn_finset_iUnion.mpr (fun y _ => hint y)
  have hmono : ∫ p in W, g p ∂volume ≤ ∫ p in ⋃ y ∈ S, Wf y, g p ∂volume :=
    setIntegral_mono_set hUint (Filter.Eventually.of_forall hg0) hcover
  exact hmono.trans (setIntegral_biUnion_le S hmeas hg0 hint)

/-- The `normalizedL2On` cover bound under an a.e. cover. -/
theorem normalizedL2On_le_of_aecover_finset {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {f : Vec d → ℝ}
    {N : ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y))
    (hint : ∀ y, IntegrableOn (fun p => f p ^ 2) (Wf y) volume)
    (hcover : W ≤ᵐ[volume] ⋃ y ∈ S, Wf y)
    (hWpos : 0 < (volume W).toReal)
    (hfin : ∀ y ∈ S, volume (Wf y) ≠ ⊤)
    (hvol : ∀ y ∈ S, (volume (Wf y)).toReal ≤ (volume W).toReal)
    (hN : ∀ y ∈ S, normalizedL2On (Wf y) f ≤ N) (hN0 : 0 ≤ N) :
    normalizedL2On W f ≤ Real.sqrt (S.card : ℝ) * N := by
  have hcard0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  refine Section6Iteration.normalizedL2On_le_of_sq_le (by positivity) ?_
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
  have hsum : ∫ p in W, f p ^ 2 ∂volume ≤
      (S.card : ℝ) * ((volume W).toReal * N ^ 2) := by
    refine (setIntegral_le_of_aecover_finset hmeas (fun p => sq_nonneg (f p))
      hint hcover).trans ?_
    calc ∑ y ∈ S, ∫ p in Wf y, f p ^ 2 ∂volume
        ≤ ∑ _y ∈ S, (volume W).toReal * N ^ 2 := Finset.sum_le_sum hpiece
      _ = (S.card : ℝ) * ((volume W).toReal * N ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsqrt : (Real.sqrt (S.card : ℝ) * N) ^ 2 = (S.card : ℝ) * N ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcard0]
  rw [hsqrt]
  unfold volumeAverage
  rw [inv_mul_le_iff₀ hWpos]
  calc ∫ p in W, f p ^ 2 ∂volume
      ≤ (S.card : ℝ) * ((volume W).toReal * N ^ 2) := hsum
    _ = (volume W).toReal * ((S.card : ℝ) * N ^ 2) := by ring

/-- **The energy cover for a vector field under an a.e. cover** — the form the
concrete grid cover of an off-grid window will supply. -/
theorem vectorNormalizedL2On_le_of_aecover_finset {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {f : Vec d → Vec d}
    {N : ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y))
    (hint : ∀ y, IntegrableOn
      (fun p => Homogenization.euclideanNorm (f p) ^ 2) (Wf y) volume)
    (hcover : W ≤ᵐ[volume] ⋃ y ∈ S, Wf y)
    (hWpos : 0 < (volume W).toReal)
    (hfin : ∀ y ∈ S, volume (Wf y) ≠ ⊤)
    (hvol : ∀ y ∈ S, (volume (Wf y)).toReal ≤ (volume W).toReal)
    (hN : ∀ y ∈ S, vectorNormalizedL2On (Wf y) f ≤ N) (hN0 : 0 ≤ N) :
    vectorNormalizedL2On W f ≤ Real.sqrt (S.card : ℝ) * N :=
  normalizedL2On_le_of_aecover_finset hmeas hint hcover hWpos hfin hvol hN hN0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
