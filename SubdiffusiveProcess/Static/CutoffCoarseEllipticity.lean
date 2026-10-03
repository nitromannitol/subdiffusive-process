module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FullResponseMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentTranslatedEllipticity

@[expose] public section

/-! # Coarse lower ellipticity above a finite cutoff

The large-cube response moments and the all-scale error comparison give a
uniform moment of the normalized inverse coarse ellipticity. The supplier
keeps arbitrary physical centres and places the disorder threshold before
the cutoff and the outer scale.
-/

open MeasureTheory Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- The measurable lower ellipticity inverse, with the local time normalization. -/
def cutoffLowerInv {d : ℕ} [NeZero d] (M : GMCModel d) (L m : ℕ)
    (z : Vec d) (ω : PotentialSample d) : ℝ :=
  ahom M L * fluxRowMomentTranslatedLowerInv M L m z ω

theorem measurable_cutoffLowerInv {d : ℕ} [NeZero d]
    (M : GMCModel d) (L m : ℕ) (z : Vec d) :
    Measurable (cutoffLowerInv M L m z) :=
  measurable_const.mul (measurable_fluxRowMomentTranslatedLowerInv M L m z)

theorem cutoffLowerInv_nonneg {d : ℕ} [NeZero d]
    (M : GMCModel d) (L m : ℕ) (z : Vec d) (ω : PotentialSample d) :
    0 ≤ cutoffLowerInv M L m z ω :=
  mul_nonneg (ahom_pos M L).le (fluxRowMomentTranslatedLowerInv_nonneg M L m z ω)

/-- Identification with the literal coefficient, including arbitrary translations. -/
theorem cutoffLowerInv_ae_eq {d : ℕ} [NeZero d]
    (M : GMCModel d) (L m : ℕ) (z : Vec d) :
    cutoffLowerInv M L m z =ᵐ[M.P.toMeasure] fun ω =>
      ahom M L * (Ch04.lambdaSqCoeffField (originCube d (m : ℤ))
        (1 / 16) (.finite 1) (aCutoffRegCoeffField M L (translatePotentialSample z ω)))⁻¹ := by
  have h := (Section6Covariance.measurePreserving_translatePotentialSample M z).quasiMeasurePreserving.ae_eq_comp (fluxRowMomentLowerInvMeasurable_ae_eq M L m)
  filter_upwards [h] with ω hω
  exact congrArg (fun x : ℝ => ahom M L * x) hω

/-- Translation preserves the full paper response moment. -/
theorem paperResponse_moment_translate {d : ℕ} (M : GMCModel d) (L m : ℕ)
    (z : Vec d) (s p : ℝ) (hp : 0 < p) :
    paperENNRealLpNorm M.P.toMeasure p
      (translatedHomogenizationErrorRandom M L m z s 1) =
    paperENNRealLpNorm M.P.toMeasure p
      (translatedHomogenizationErrorRandom M L m 0 s 1) := by
  have heq : translatedHomogenizationErrorRandom M L m z s 1 =
      translatedHomogenizationErrorRandom M L m 0 s 1 ∘ translatePotentialSample z := by
    funext ω
    unfold translatedHomogenizationErrorRandom
    dsimp only [Function.comp_apply]
    congr 2
    funext k
    apply PotentialField.ext
    intro x
    change ω k (x + z) = ω k ((x + 0) + z)
    rw [add_zero]
  have hF := (Section4Recursion.measurable_translatedHomogenizationErrorRandom_one
    (s := s) M L m 0).aestronglyMeasurable (μ := M.P.toMeasure)
  have hpres := Section6Covariance.measurePreserving_translatePotentialSample M z
  rw [heq, paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable _ hp _
    (hF.comp_measurePreserving hpres),
    paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable _ hp _ hF]
  exact eLpNorm_comp_measurePreserving hF hpres

/-- Uniform inverse coarse ellipticity moments on every cube above the cutoff.
The dimensional lower bound is the order required by the existing response
supplier, and can be met by choosing a larger moment before reducing disorder. -/
theorem exists_uniform_cutoffLowerInv_moment_bound {d : ℕ} [NeZero d]
    (q : ℝ) (hq : 1 ≤ q) (hdq : 64 * (d : ℝ) ≤ q) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 → ∀ L m : ℕ, L ≤ m → ∀ z : Vec d,
        eLpNorm (cutoffLowerInv M L m z) (ENNReal.ofReal q) M.P.toMeasure ≤
          ENNReal.ofReal C := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdim : 4 * (d : ℝ) * ((1 / 16 : ℝ) / 2)⁻¹ ≤ 2 * q := by
    norm_num
    linarith
  obtain ⟨δ0, R, hδ0, hR, hbound⟩ :=
    Section6Dirichlet.exists_dirichletFullResponse_paper_moment_bound
      (s := (1 / 16 : ℝ)) (xi := 2 * q)
      (by norm_num) (by norm_num) (by linarith) hdim
  let C := (1 + Real.sqrt 2 * (R / 2)) ^ 2
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ0, C, hδ0, hC, ?_⟩
  intro M hM L m hLm z
  have hresp : paperENNRealLpNorm M.P.toMeasure (2 * q)
      (translatedHomogenizationErrorRandom M L m z (1 / 16) 1) ≤
        ENNReal.ofReal (R / 2) := by
    rw [paperResponse_moment_translate M L m z _ _ (by positivity)]
    have hraw := (hbound M hM L m hLm).1
    have heq : translatedHomogenizationErrorRandom M L m 0 (1 / 16) 1 =
        fun ω => paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ)
          (1 / 16) .infinity (.finite 1) (aCutoffFamily M L ω) (ahom M L) := by
      funext ω
      simp [translatedHomogenizationErrorRandom]
    rw [heq]
    refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_le_mul_of_nonneg_left M.shellPrefix.delta_le_half hR.le]
  have hf := paperENNRealLpNorm_ahom_mul_fluxRowMomentTranslatedLowerInv_le
    M L m z hq
  have hnorm : paperENNRealLpNorm M.P.toMeasure q
      (fun ω => ENNReal.ofReal (cutoffLowerInv M L m z ω)) ≤ ENNReal.ofReal C := by
    refine hf.trans ((pow_le_pow_left' (add_le_add le_rfl
      (mul_le_mul_right hresp (ENNReal.ofReal (Real.sqrt 2)))) 2).trans_eq ?_)
    dsimp only [C]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
  have hconvert := Section4Recursion.paperENNRealLpNorm_eq_eLpNorm_toReal
    M.P.toMeasure hq0 (fun ω : PotentialSample d =>
      (ENNReal.ofReal_ne_top : ENNReal.ofReal (cutoffLowerInv M L m z ω) ≠ ⊤))
  have heq : (fun ω => (ENNReal.ofReal (cutoffLowerInv M L m z ω)).toReal) =
      cutoffLowerInv M L m z := by
    funext ω
    exact ENNReal.toReal_ofReal (cutoffLowerInv_nonneg M L m z ω)
  rw [heq] at hconvert
  rw [hconvert, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
    (measurable_cutoffLowerInv M L m z).aestronglyMeasurable] at hnorm
  exact hnorm

end SubdiffusiveProcess.Static
