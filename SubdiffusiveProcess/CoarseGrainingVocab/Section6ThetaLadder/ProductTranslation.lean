module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductOriginRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TranslationExcess
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationTranslation

@[expose] public section

/-!
# Theta-perturbed ladder: recentering a product-coefficient solution

This file transports the physical equation on a translated cube to the
origin cube used by `productOrigin_excessRecurrence`.  The sample and the
multiplier are translated together, so the coefficient identity is exactly
the landed covariance law for `aCutoff`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ}

private theorem isWeaklyHarmonicOn_castDomain
    {U V : Set (Vec d)} (hUV : U = V) {a : Vec d → ℝ}
    (u : H1Function U) (hu : IsWeaklyHarmonicOn a U u) :
    IsWeaklyHarmonicOn a V
      (Homogenization.Book.Ch03.castH1Domain hUV u) := by
  subst V
  exact hu

def translatedMultiplier (z : Vec d) (theta : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ theta (x + z)

theorem translatedCube_eq_translateSet
    (d : ℕ) (n : ℤ) (z : Vec d) :
    translatedCube d n z = translateSet z (cube d n) := by
  rw [translatedCube, cube,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet]

/-- Recenter a physical product-harmonic function. -/
theorem isWeaklyHarmonicOn_product_untranslate
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (n : ℤ) (z : Vec d) (theta : Vec d → ℝ)
    (u : H1Function (translatedCube d n z))
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (translatedCube d n z) u) :
    IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
          (translatePotentialSample z omega) x * translatedMultiplier z theta x)
      (cube d n)
      (H1Function.untranslate z
        (Homogenization.Book.Ch03.castH1Domain
          (translatedCube_eq_translateSet d n z) u)) := by
  let uT : H1Function (translateSet z (cube d n)) :=
    Homogenization.Book.Ch03.castH1Domain
      (translatedCube_eq_translateSet d n z) u
  have huT : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (translateSet z (cube d n)) uT := by
    exact isWeaklyHarmonicOn_castDomain
      (translatedCube_eq_translateSet d n z) u hu
  have hdiv : IsDivFormWeakSolutionOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (translateSet z (cube d n)) uT (fun _ ↦ (0 : Vec d)) := by
    intro phi
    rw [huT phi]
    simp only [vecDot_zero_left, integral_zero, neg_zero]
  have htr := isDivFormWeakSolutionOn_untranslate z hdiv
  intro phi
  have hphi := htr phi
  simpa only [translatedMultiplier,
    Section6Covariance.aCutoff_translatePotentialSample,
    vecDot_zero_left, integral_zero, neg_zero] using hphi

/-- The translated multiplier inherits continuity on the recentered cube. -/
theorem continuousOn_translatedMultiplier
    {n : ℤ} {z : Vec d} {theta : Vec d → ℝ}
    (htheta : ContinuousOn theta (translatedCube d n z)) :
    ContinuousOn (translatedMultiplier z theta) (cube d n) := by
  refine htheta.comp (continuous_id.add continuous_const).continuousOn ?_
  intro x hx
  rw [translatedCube_eq_translateSet]
  refine ⟨x, hx, ?_⟩
  simp [add_comm]

/-- Pointwise multiplier closeness is unchanged by recentering. -/
theorem translatedMultiplier_near_one
    {n : ℤ} {z : Vec d} {theta : Vec d → ℝ} {b epsilon : ℝ}
    (hnear : ∀ x ∈ translatedCube d n z,
      |b⁻¹ * theta x - 1| ≤ epsilon) :
    ∀ x ∈ cube d n,
      |b⁻¹ * translatedMultiplier z theta x - 1| ≤ epsilon := by
  intro x hx
  apply hnear (x + z)
  rw [translatedCube_eq_translateSet]
  refine ⟨x, hx, ?_⟩
  simp [add_comm]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
