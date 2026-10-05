module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5RobustTests

@[expose] public section

/-!
# Step M of the robust good-cube event: the mass field

the two
computations C1 and C2 it rests on.  All of it is pure algebra with explicit constants; nothing
here is probabilistic and nothing uses De Giorgi–Nash–Moser.

* `admissibleMultiplier_bounds` (C1) — `GoodCubeV5AdmissibleMultiplier S ε θ` says
  `|k⁻¹ θ - 1| ≤ ε` on `S` for some `k > 0`, which is exactly the sandwich
  `k(1-ε) ≤ θ ≤ k(1+ε)`.
* `weightedMeasure_mul_le` and `le_weightedMeasure_mul` (C2) — a pointwise bound on the
  multiplier is a scalar bound on the weighted measure of every measurable subset of the window,
  since `weightedMeasure ρ = volume.withDensity (ofReal ∘ ρ)` is monotone and positively
  homogeneous in `ρ`.
* `mass_comparison_of_admissible` (Step M) — a mass comparison between two subsets of the window
  survives multiplication by an admissible multiplier, with the constant
  `massFraction · (1-ε)/(1+ε)`.

The scale `k` cancels in the mass ratio: the upper bound is used on the numerator set and the
lower bound on the denominator set, and the exponent of `k` in the product is `1 - 1 = 0`.  That
is what makes the transferred constant independent of the multiplier's normalization, exactly as
the plan records.
-/

set_option autoImplicit false
open Homogenization hiding Vec
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-- **Computation C1.**  An admissible multiplier is sandwiched between `k(1-ε)` and `k(1+ε)`
on its window: the defining bound `|k⁻¹ θ - 1| ≤ ε` is exactly that, after multiplying by the
positive scale `k`. -/
theorem admissibleMultiplier_bounds {S : Set (Vec d)} {epsilon : ℝ} {theta : Vec d → ℝ}
    (h : GoodCubeV5AdmissibleMultiplier S epsilon theta) :
    ∃ k : ℝ, 0 < k ∧ ∀ x ∈ S, k * (1 - epsilon) ≤ theta x ∧ theta x ≤ k * (1 + epsilon) := by
  obtain ⟨-, -, k, hk, hbound⟩ := h
  refine ⟨k, hk, fun x hx => ?_⟩
  have h1 := abs_le.mp (hbound x hx)
  rw [inv_mul_eq_div] at h1
  obtain ⟨hlo, hhi⟩ := h1
  constructor
  · have : (1 - epsilon) ≤ theta x / k := by linarith
    have h2 := (le_div_iff₀ hk).mp this
    linarith [h2]
  · have : theta x / k ≤ 1 + epsilon := by linarith
    have h2 := (div_le_iff₀ hk).mp this
    linarith [h2]

/-- **Computation C2, upper half.**  A pointwise upper bound on the multiplier is a scalar upper
bound on the weighted measure of every measurable subset of the window. -/
theorem weightedMeasure_mul_le {S E : Set (Vec d)} (hE : MeasurableSet E) (hES : E ⊆ S)
    {a theta : Vec d → ℝ} {u : ℝ} (hu : 0 ≤ u) (ha : ∀ x ∈ S, 0 ≤ a x)
    (hupper : ∀ x ∈ S, theta x ≤ u) :
    weightedMeasure (fun x => a x * theta x) E ≤ ENNReal.ofReal u * weightedMeasure a E := by
  unfold weightedMeasure
  rw [withDensity_apply _ hE, withDensity_apply _ hE, ← lintegral_const_mul']
  · refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hE] with x hx
    have hxS : x ∈ S := hES hx
    rw [← ENNReal.ofReal_mul hu]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [ha x hxS, hupper x hxS])
  · exact ENNReal.ofReal_ne_top

/-- **Computation C2, lower half.** -/
theorem le_weightedMeasure_mul {S E : Set (Vec d)} (hE : MeasurableSet E) (hES : E ⊆ S)
    {a theta : Vec d → ℝ} {l : ℝ} (hl : 0 ≤ l) (ha : ∀ x ∈ S, 0 ≤ a x)
    (hlower : ∀ x ∈ S, l ≤ theta x) :
    ENNReal.ofReal l * weightedMeasure a E ≤ weightedMeasure (fun x => a x * theta x) E := by
  unfold weightedMeasure
  rw [withDensity_apply _ hE, withDensity_apply _ hE, ← lintegral_const_mul']
  · refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hE] with x hx
    have hxS : x ∈ S := hES hx
    rw [← ENNReal.ofReal_mul hl]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [ha x hxS, hlower x hxS])
  · exact ENNReal.ofReal_ne_top

/-- **Step M of the robust-event plan: the mass field.**  A mass comparison between two subsets
of the window survives multiplication by an admissible multiplier, with the sharp constant
`massFraction · (1-ε)/(1+ε)`.  The multiplier's overall scale `k` cancels in the ratio. -/
theorem mass_comparison_of_admissible {S Eq Er : Set (Vec d)}
    (hEq : MeasurableSet Eq) (hEr : MeasurableSet Er) (hqS : Eq ⊆ S) (hrS : Er ⊆ S)
    {a theta : Vec d → ℝ} {epsilon massFraction : ℝ}
    (ha : ∀ x ∈ S, 0 ≤ a x) (hmf : 0 ≤ massFraction)
    (heps0 : 0 ≤ epsilon) (heps1 : epsilon < 1)
    (hadm : GoodCubeV5AdmissibleMultiplier S epsilon theta)
    (hmass : ENNReal.ofReal massFraction * weightedMeasure a Er ≤ weightedMeasure a Eq) :
    ENNReal.ofReal (massFraction * (1 - epsilon) / (1 + epsilon)) *
        weightedMeasure (fun x => a x * theta x) Er ≤
      weightedMeasure (fun x => a x * theta x) Eq := by
  obtain ⟨k, hk, hkb⟩ := admissibleMultiplier_bounds hadm
  have hpos1 : (0:ℝ) < 1 + epsilon := by linarith
  have hnn1 : (0:ℝ) ≤ 1 - epsilon := by linarith
  have hupper : weightedMeasure (fun x => a x * theta x) Er ≤
      ENNReal.ofReal (k * (1 + epsilon)) * weightedMeasure a Er :=
    weightedMeasure_mul_le hEr hrS (by positivity) ha (fun x hx => (hkb x hx).2)
  have hlower : ENNReal.ofReal (k * (1 - epsilon)) * weightedMeasure a Eq ≤
      weightedMeasure (fun x => a x * theta x) Eq :=
    le_weightedMeasure_mul hEq hqS (by positivity) ha (fun x hx => (hkb x hx).1)
  refine le_trans (mul_le_mul_right hupper _) (le_trans ?_ hlower)
  have hprod : massFraction * (1 - epsilon) / (1 + epsilon) * (k * (1 + epsilon)) =
      k * (1 - epsilon) * massFraction := by
    field_simp
  calc ENNReal.ofReal (massFraction * (1 - epsilon) / (1 + epsilon)) *
        (ENNReal.ofReal (k * (1 + epsilon)) * weightedMeasure a Er)
      = ENNReal.ofReal (massFraction * (1 - epsilon) / (1 + epsilon) * (k * (1 + epsilon))) *
          weightedMeasure a Er := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (k * (1 - epsilon)) * (ENNReal.ofReal massFraction *
          weightedMeasure a Er) := by
        rw [hprod, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (k * (1 - epsilon)) * weightedMeasure a Eq :=
        mul_le_mul_right hmass _

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
