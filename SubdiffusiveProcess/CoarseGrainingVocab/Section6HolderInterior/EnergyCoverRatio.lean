module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GridCover

@[expose] public section

/-!
# The energy cover with a volume ratio

`EnergyCoverAE` assumes each covering piece has volume at most that of the
covered window.  That is **too strong for the concrete grid cover**: the pieces
`U_{m,j}(y)` and the base window `U_{m,j}(x)` are both scale-`j` windows, but
truncation against `□_m` can make a piece larger than the base.  The proved
bounds `volume_toReal_truncatedCube_bounds` only give
`(3^{j-2})^d ≤ |U_{m,j}(·)| ≤ (3^j)^d`, a ratio of `9^d`.

So the cover bound is restated here with an explicit ratio `R`, giving the
constant `√(card · R)`.  For the grid cover this is `√(card · 9^d) = 3^d √card`
— still dimension-only, as required.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-- Same-scale truncated windows have volume ratio at most `9^d`. -/
theorem volume_truncatedCube_le_ratio {m j : ℤ} {x y : Vec d}
    (hx : x ∈ cube d m) (hy : y ∈ cube d m) (hjm : j - 1 ≤ m) :
    (volume (truncatedCube d m j y)).toReal ≤
      ((3 : ℝ) ^ (2 : ℤ)) ^ d * (volume (truncatedCube d m j x)).toReal := by
  have hratio := Section6Holder.volume_ratio_truncatedCube_crossCentre_le
    (m := m) (j := j) (ell := j) hx hy hjm hjm
  have hpos : 0 < (volume (truncatedCube d m j x)).toReal :=
    volume_toReal_truncatedCube_pos x hx hjm
  have hexp : j - j + 2 = (2 : ℤ) := by ring
  rw [hexp] at hratio
  rw [div_le_iff₀ hpos] at hratio
  linarith

/-- **The energy cover with a volume ratio.** -/
theorem normalizedL2On_le_of_aecover_ratio {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {f : Vec d → ℝ}
    {N R : ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y))
    (hint : ∀ y, IntegrableOn (fun p => f p ^ 2) (Wf y) volume)
    (hcover : W ≤ᵐ[volume] ⋃ y ∈ S, Wf y)
    (hWpos : 0 < (volume W).toReal)
    (hfin : ∀ y ∈ S, volume (Wf y) ≠ ⊤)
    (hvol : ∀ y ∈ S, (volume (Wf y)).toReal ≤ R * (volume W).toReal)
    (hR : 0 ≤ R)
    (hN : ∀ y ∈ S, normalizedL2On (Wf y) f ≤ N) (hN0 : 0 ≤ N) :
    normalizedL2On W f ≤ Real.sqrt ((S.card : ℝ) * R) * N := by
  have hcard0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  refine Section6Iteration.normalizedL2On_le_of_sq_le (by positivity) ?_
  have hpiece : ∀ y ∈ S,
      ∫ p in Wf y, f p ^ 2 ∂volume ≤ R * (volume W).toReal * N ^ 2 := by
    intro y hy
    rw [setIntegral_sq_eq_volume_mul_normalizedL2On_sq (hfin y hy)]
    have hsq : normalizedL2On (Wf y) f ^ 2 ≤ N ^ 2 := by
      have h0 := Section6Iteration.normalizedL2On_nonneg (Wf y) f
      nlinarith [hN y hy, h0]
    have hvy : (0 : ℝ) ≤ (volume (Wf y)).toReal := ENNReal.toReal_nonneg
    calc (volume (Wf y)).toReal * normalizedL2On (Wf y) f ^ 2
        ≤ (volume (Wf y)).toReal * N ^ 2 := mul_le_mul_of_nonneg_left hsq hvy
      _ ≤ (R * (volume W).toReal) * N ^ 2 :=
          mul_le_mul_of_nonneg_right (hvol y hy) (by positivity)
      _ = R * (volume W).toReal * N ^ 2 := by ring
  have hsum : ∫ p in W, f p ^ 2 ∂volume ≤
      (S.card : ℝ) * (R * (volume W).toReal * N ^ 2) := by
    refine (setIntegral_le_of_aecover_finset hmeas (fun p => sq_nonneg (f p))
      hint hcover).trans ?_
    calc ∑ y ∈ S, ∫ p in Wf y, f p ^ 2 ∂volume
        ≤ ∑ _y ∈ S, R * (volume W).toReal * N ^ 2 := Finset.sum_le_sum hpiece
      _ = (S.card : ℝ) * (R * (volume W).toReal * N ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsqrt : (Real.sqrt ((S.card : ℝ) * R) * N) ^ 2 =
      (S.card : ℝ) * R * N ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsqrt]
  unfold volumeAverage
  rw [inv_mul_le_iff₀ hWpos]
  calc ∫ p in W, f p ^ 2 ∂volume
      ≤ (S.card : ℝ) * (R * (volume W).toReal * N ^ 2) := hsum
    _ = (volume W).toReal * ((S.card : ℝ) * R * N ^ 2) := by ring

/-- The vector form, which row 2's left-hand side uses. -/
theorem vectorNormalizedL2On_le_of_aecover_ratio {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {f : Vec d → Vec d}
    {N R : ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y))
    (hint : ∀ y, IntegrableOn
      (fun p => Homogenization.euclideanNorm (f p) ^ 2) (Wf y) volume)
    (hcover : W ≤ᵐ[volume] ⋃ y ∈ S, Wf y)
    (hWpos : 0 < (volume W).toReal)
    (hfin : ∀ y ∈ S, volume (Wf y) ≠ ⊤)
    (hvol : ∀ y ∈ S, (volume (Wf y)).toReal ≤ R * (volume W).toReal)
    (hR : 0 ≤ R)
    (hN : ∀ y ∈ S, vectorNormalizedL2On (Wf y) f ≤ N) (hN0 : 0 ≤ N) :
    vectorNormalizedL2On W f ≤ Real.sqrt ((S.card : ℝ) * R) * N :=
  normalizedL2On_le_of_aecover_ratio hmeas hint hcover hWpos hfin hvol hR hN hN0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
