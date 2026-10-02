import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import Homogenization.CoarseGraining.Definitions
import Homogenization.Sobolev.Foundations.DifferenceQuotient

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/NormalizedL2.lean
-- Adapted from Algsuperdiff/Section4/Support/NormalizedL2.lean

/-!
# The volume-normalized `L̲²(W)` seminorm and its `eLpNorm` dictionary

ABK26, §4.3.  The excess of `e.excess.def` is built on the volume-normalized
norm `‖·‖_{L̲²(W)}`, which the manuscript writes as an average:

```
‖f‖_{L̲²(W)} = (⨍_W f²)^{1/2} .
```

This module supplies the seminorm calculus for the frozen
`SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On`, together with the dictionary to the
`ℝ≥0∞`-valued `MeasureTheory.eLpNorm`:

* `normalizedL2On_eq_toReal_eLpNorm_div` --- `‖f‖_{L̲²(W)} = ‖f‖_{L²(volume|_W)} /
  |W|^{1/2}`, with no hypothesis on `W` (at `volume W ∈ {0, ∞}` both sides are `0`);

Everything else here is the seminorm calculus the excess layer consumes.
Minkowski (`normalizedL2On_add_le`) is obtained *through* the dictionary from
mathlib's `eLpNorm_add_le` rather than by a hand-rolled Cauchy--Schwarz on
`volumeAverage`: that is the single reason the dictionary is proved first.

## Why the `ℝ`-valued object at all

The iteration lemma and the discrete Grönwall lemma are inequalities between
*real* numbers, with subtractions and an exponential; the Section-3
harmonic/oscillation layer is real-valued as well.  The frozen Section-4
surface is `ℝ≥0∞`-valued.  Both languages are therefore needed, and this module
is the seam.  The `MemLp` side conditions are the honest "`f ∈ L²(W)`"
hypotheses; they are not needed for well-definedness (the `sqrt` of a
possibly-`0` average is total) but they are needed for the arithmetic, exactly
as in the source.

## Scope

Internal support for the section 6 iteration lemma provider.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

open MeasureTheory
open Homogenization (volumeAverage)

noncomputable section

variable {d : ℕ}

theorem normalizedL2On_nonneg (W : Set (Vec d)) (f : Vec d → ℝ) :
    0 ≤ normalizedL2On W f :=
  Real.sqrt_nonneg _

/-- The volume average of a square is nonnegative.  No measurability of `W` is
needed: the integrand is globally nonnegative. -/
theorem volumeAverage_sq_nonneg (W : Set (Vec d)) (f : Vec d → ℝ) :
    0 ≤ volumeAverage W (fun x => f x ^ 2) := by
  unfold volumeAverage
  exact mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg (f x))

/-- `‖f‖²_{L̲²(W)} = ⨍_W f²`. -/
theorem normalizedL2On_sq (W : Set (Vec d)) (f : Vec d → ℝ) :
    normalizedL2On W f ^ 2 = volumeAverage W (fun x => f x ^ 2) :=
  Real.sq_sqrt (volumeAverage_sq_nonneg W f)

/-- A bound on the average of the square is a bound on the seminorm. -/
theorem normalizedL2On_le_of_sq_le {W : Set (Vec d)} {f : Vec d → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (h : volumeAverage W (fun x => f x ^ 2) ≤ M ^ 2) :
    normalizedL2On W f ≤ M := by
  have h1 : Real.sqrt (volumeAverage W (fun x => f x ^ 2)) ≤ Real.sqrt (M ^ 2) :=
    Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hM] at h1

/-! ### The `eLpNorm` dictionary -/

/-- **The dictionary.**  The volume-normalized `L²(W)` seminorm is the
unnormalized `L²(volume|_W)` norm divided by `|W|^{1/2}`.

No measurability of `W` and no positivity of `|W|` is required: when `volume W`
is `0` or `∞` the real number `(volume W).toReal` is `0` and both sides
degenerate to `0`. -/
theorem normalizedL2On_eq_toReal_eLpNorm_div {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) :
    normalizedL2On W f
      = (eLpNorm f 2 (volume.restrict W)).toReal / Real.sqrt ((volume W).toReal) := by
  have hsq : (eLpNorm f 2 (volume.restrict W)).toReal ^ 2 = ∫ x in W, f x ^ 2 :=
    Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hf
  have hVinv : (0 : ℝ) ≤ ((volume W).toReal)⁻¹ := by positivity
  unfold normalizedL2On volumeAverage
  rw [← hsq, Real.sqrt_mul hVinv, Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_inv,
    inv_mul_eq_div]

/-- The reciprocal form of the dictionary. -/
theorem toReal_eLpNorm_eq_sqrt_volume_mul_normalizedL2On {W : Set (Vec d)}
    {f : Vec d → ℝ} (hWpos : 0 < (volume W).toReal)
    (hf : MemLp f 2 (volume.restrict W)) :
    (eLpNorm f 2 (volume.restrict W)).toReal
      = Real.sqrt ((volume W).toReal) * normalizedL2On W f := by
  have hs : Real.sqrt ((volume W).toReal) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hWpos)
  rw [normalizedL2On_eq_toReal_eLpNorm_div hf, mul_div_cancel₀ _ hs]

/-! ### The seminorm calculus -/

/-- **Minkowski** for `‖·‖_{L̲²(W)}`, obtained through the dictionary from
mathlib's `eLpNorm_add_le`. -/
theorem normalizedL2On_add_le {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) (hg : MemLp g 2 (volume.restrict W)) :
    normalizedL2On W (fun x => f x + g x)
      ≤ normalizedL2On W f + normalizedL2On W g := by
  have hpi : (fun x => f x + g x) = f + g := rfl
  have hfg : MemLp (fun x => f x + g x) 2 (volume.restrict W) := by
    rw [hpi]; exact hf.add hg
  have hle : eLpNorm (fun x => f x + g x) 2 (volume.restrict W)
      ≤ eLpNorm f 2 (volume.restrict W) + eLpNorm g 2 (volume.restrict W) := by
    rw [hpi]
    exact eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable one_le_two
  have hne : eLpNorm f 2 (volume.restrict W) + eLpNorm g 2 (volume.restrict W) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hf.2.ne, hg.2.ne⟩
  have hler : (eLpNorm (fun x => f x + g x) 2 (volume.restrict W)).toReal
      ≤ (eLpNorm f 2 (volume.restrict W)).toReal
        + (eLpNorm g 2 (volume.restrict W)).toReal := by
    rw [← ENNReal.toReal_add hf.2.ne hg.2.ne]
    exact ENNReal.toReal_mono hne hle
  rw [normalizedL2On_eq_toReal_eLpNorm_div hfg, normalizedL2On_eq_toReal_eLpNorm_div hf,
    normalizedL2On_eq_toReal_eLpNorm_div hg, ← add_div, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hler (by positivity)

/-- Absolute homogeneity.  No hypotheses: the scalar pull-out of `volumeAverage`
is unconditional. -/
theorem normalizedL2On_const_mul (W : Set (Vec d)) (t : ℝ) (f : Vec d → ℝ) :
    normalizedL2On W (fun x => t * f x) = |t| * normalizedL2On W f := by
  have hrw : (fun x => (t * f x) ^ 2) = fun x => t ^ 2 * f x ^ 2 := by
    funext x; ring
  have hpull : volumeAverage W (fun x => t ^ 2 * f x ^ 2)
      = t ^ 2 * volumeAverage W (fun x => f x ^ 2) := by
    unfold volumeAverage
    rw [integral_const_mul]
    ring
  unfold normalizedL2On
  rw [hrw, hpull, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

theorem normalizedL2On_neg (W : Set (Vec d)) (f : Vec d → ℝ) :
    normalizedL2On W (fun x => -f x) = normalizedL2On W f := by
  have hrw : (fun x => (-f x) ^ 2) = fun x => f x ^ 2 := by
    funext x; ring
  unfold normalizedL2On
  rw [hrw]

theorem normalizedL2On_sub_comm (W : Set (Vec d)) (f g : Vec d → ℝ) :
    normalizedL2On W (fun x => f x - g x) = normalizedL2On W (fun x => g x - f x) := by
  have hrw : (fun x => g x - f x) = fun x => -(f x - g x) := by
    funext x; ring
  rw [hrw, normalizedL2On_neg]

/-! ### The volume-ratio comparison on nested windows -/

/-- Passing to a subwindow multiplies the average of a nonnegative function by at
most the volume ratio. -/
theorem volumeAverage_le_of_subset {W W' : Set (Vec d)} {f : Vec d → ℝ}
    (hsub : W' ⊆ W) (hW : 0 < (volume W).toReal) (hW' : 0 < (volume W').toReal)
    (hf0 : ∀ x, 0 ≤ f x) (hint : IntegrableOn f W) :
    volumeAverage W' f
      ≤ ((volume W).toReal / (volume W').toReal) * volumeAverage W f := by
  have hmono : ∫ x in W', f x ≤ ∫ x in W, f x :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hf0)
      (HasSubset.Subset.eventuallyLE hsub)
  have hstep : ((volume W').toReal)⁻¹ * ∫ x in W', f x
      ≤ ((volume W').toReal)⁻¹ * ∫ x in W, f x :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  have heq : ((volume W).toReal / (volume W').toReal)
      * (((volume W).toReal)⁻¹ * ∫ x in W, f x)
      = ((volume W').toReal)⁻¹ * ∫ x in W, f x := by
    field_simp
  unfold volumeAverage
  rw [heq]
  exact hstep

/-- **Volume-ratio comparison of the normalized seminorms on nested windows.**
For `W' ⊆ W`, `‖f‖_{L̲²(W')} ≤ (|W|/|W'|)^{1/2} ‖f‖_{L̲²(W)}`.  This is the
geometric engine of excess quasi-monotonicity. -/
theorem normalizedL2On_le_of_subset {W W' : Set (Vec d)} {f : Vec d → ℝ}
    (hsub : W' ⊆ W) (hW : 0 < (volume W).toReal) (hW' : 0 < (volume W').toReal)
    (hint : IntegrableOn (fun x => f x ^ 2) W) :
    normalizedL2On W' f
      ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) * normalizedL2On W f := by
  have h := volumeAverage_le_of_subset hsub hW hW' (fun x => sq_nonneg (f x)) hint
  unfold normalizedL2On
  calc Real.sqrt (volumeAverage W' (fun x => f x ^ 2))
      ≤ Real.sqrt (((volume W).toReal / (volume W').toReal)
          * volumeAverage W (fun x => f x ^ 2)) := Real.sqrt_le_sqrt h
    _ = Real.sqrt ((volume W).toReal / (volume W').toReal)
          * Real.sqrt (volumeAverage W (fun x => f x ^ 2)) :=
        Real.sqrt_mul (by positivity) _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
