module

public import SubdiffusiveProcess.Section10.PhysicalSobolevBankBounds
public import SubdiffusiveProcess.Frozen.Section4.CoarseGrainedBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentTranslatedEllipticity

@[expose] public section

/-! The constructed Section 4 induction supplier discharges every hypothesis
of the large-reference-cube estimate. Constants precede cutoff, cube scale,
and deterministic translate. No response package is an input to this bank. -/
open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Uniform large-cube error moments at the order used by killed coercivity.
The order is fixed before reducing disorder. -/
theorem physical_large_response_bank {d : ℕ} (hd : 2 ≤ d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ →
        ∀ l m : ℕ, l ≤ m → ∀ z : SpatialCoordinates d,
          paperENNRealLpNorm M.P.toMeasure (2 * q)
            (translatedHomogenizationErrorRandom M l m z (1 / 16) 1) ≤
              ENNReal.ofReal C := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨ci, Ci, hci, hCi, hind⟩ :=
    SubdiffusiveProcess.Providers.Section4.exists_headline_allMomentSecondInduction
      (d := d) SubdiffusiveProcess.Frozen.Section4.homogenization_step
  obtain ⟨ce, Ce, hce, hCe, hlarge⟩ :=
    SubdiffusiveProcess.Frozen.Section4.multiscale_response_large_cubes (d := d)
  let p := max (2 * q) (64 * (d : ℝ))
  have hpq : 2 * q ≤ p := le_max_left _ _
  have hpd : 64 * (d : ℝ) ≤ p := le_max_right _ _
  have hp : 1 ≤ p := by dsimp [p]; exact (by linarith : 1 ≤ 2 * q).trans hpq
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let eps := min (ci / 2) (1 / 2 : ℝ)
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  have heps1 : eps < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hepsci : eps < ci := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let A := Ci * p * Real.log (2 + p)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (mul_pos hCi hp0) (Real.log_pos (by linarith))
  let δ := min (min (Real.sqrt eps) (Real.sqrt (eps / A)))
    (Real.sqrt (ce * (1 / 16 : ℝ) * eps / p))
  have hδ : 0 < δ := lt_min (lt_min (Real.sqrt_pos.mpr heps)
    (Real.sqrt_pos.mpr (div_pos heps hA)))
      (Real.sqrt_pos.mpr (div_pos (by positivity) hp0))
  refine ⟨δ, Ce * (1 / 16 : ℝ)⁻¹ * Real.sqrt eps, hδ, by positivity, ?_⟩
  intro M hM l m hlm z
  have hM0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hdelta : M.delta ^ 2 ≤ eps := by
    have hb := hM.trans ((min_le_left _ _).trans (min_le_left _ _))
    exact (pow_le_pow_left₀ hM0 hb 2).trans_eq (Real.sq_sqrt heps.le)
  have hsmall : A * M.delta ^ 2 ≤ eps := by
    have hb := hM.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hs := (pow_le_pow_left₀ hM0 hb 2).trans_eq
      (Real.sq_sqrt (div_pos heps hA).le)
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hs
  have hIH := hind M p hp (show Ci * p * Real.log (2 + p) * M.delta ^ 2 < ci from
    hsmall.trans_lt hepsci)
  have hS : inductionHypothesis M l p eps := by
    apply inductionHypothesis_of_scale_bounds M l hp heps heps1
    intro n _hn
    exact ((le_iSup (fun r : ℕ =>
      paperENNRealLpNorm M.P.toMeasure p
        (normalizedDefect M r (Ch02.cubeDomain (originCube d (r : ℤ))))) n).trans
      hIH.2.2.2).trans (ENNReal.ofReal_le_ofReal hsmall)
  have hcap : p ≤ ce * (1 / 16 : ℝ) * (M.delta ^ 2)⁻¹ * eps := by
    have hb := hM.trans (min_le_right _ _)
    have hs := (pow_le_pow_left₀ hM0 hb 2).trans_eq
      (Real.sq_sqrt (div_pos (by positivity) hp0).le)
    have ht : p * M.delta ^ 2 ≤ ce * (1 / 16 : ℝ) * eps := by
      simpa only [mul_comm] using (le_div_iff₀ hp0).mp hs
    rw [show ce * (1 / 16 : ℝ) * (M.delta ^ 2)⁻¹ * eps =
      (ce * (1 / 16 : ℝ) * eps) / M.delta ^ 2 by ring]
    exact (le_div_iff₀ (pow_pos M.shellPrefix.delta_pos 2)).mpr ht
  have he := hlarge M l l (1 / 16) eps p (by norm_num) (by norm_num)
    hdelta heps1 le_rfl (by norm_num; linarith [hpd]) hcap hS
    m hlm z 1 (Or.inl rfl)
  have hmono := paperENNRealLpNorm_le_of_exponent_le M.P.toMeasure
    (by linarith : 0 < 2 * q) hpq
    (measurable_fluxRowMoment_translatedHomogenizationErrorRandom M l m z (1 / 16) 1)
  apply hmono.trans
  convert he using 1
  norm_num [Real.rpow_neg, Real.rpow_one]

end SubdiffusiveProcess.Section10
