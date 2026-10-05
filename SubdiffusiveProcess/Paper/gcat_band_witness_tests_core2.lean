module

public import SubdiffusiveProcess.Paper.gcat_band_condexp
public import SubdiffusiveProcess.Paper.gcat_band_witness_tests_core

@[expose] public section

open MeasureTheory Filter Set SubdiffusiveProcess
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The finite-test cover with band approximants supplied by the finite-cutoff band approximation: the test
statistics `Tt` are `L^p`-limits of `Tn`, each within `Cp·η·3^{-aH}/2` of a layer-band-measurable function,
`Tt` is small in `L^p`, and the band approximants of the limits are their conditional expectations. -/
theorem gcat_band_witness_tests_core2
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cband J : ℕ) (hCband : 0 < Cband)
    (beta a lam Cp p : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hCp : 0 < Cp)
    (hp : 2 ≤ p) (hdecay : beta * (Cband : ℝ) < a * p * Real.log 3) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℤ)
        (Tt : Fin J → BilateralField d → ℝ) (Tn : Fin J → ℕ → BilateralField d → ℝ),
      (∀ i, MemLp (Tt i) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
      (∀ i kk, MemLp (Tn i kk) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
      (∀ i, eLpNorm (Tt i) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cp * eta)) →
      (∀ i, Tendsto (fun kk => eLpNorm (Tn i kk - Tt i) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) →
      (∀ i H, 1 ≤ H → ∀ᶠ kk in atTop, ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((Cband * (H + 1) : ℕ) : ℤ))
          (n + ((Cband * (H + 1) : ℕ) : ℤ))] Yn (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => Tn i kk om - Yn om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * eta / 2 * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
      ∃ Sigma : Set (BilateralField d), MeasurableSet Sigma ∧ (chaosSampleLaw M).toMeasure Sigma = 1 ∧
        ∃ Wt : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d (n - (h : ℤ)) (n + 2 * (h : ℤ))]
            (Wt h)) ∧
          (∀ h : ℕ+, (chaosSampleLaw M).toMeasure (Wt h) ≤
            ENNReal.ofReal (Real.exp (-(beta * ((h : ℕ) : ℝ))))) ∧
          Sigma ∩ {om | ∃ i : Fin J, lam ≤ Tt i om} ⊆ ⋃ h : ℕ+, Wt h := by
  classical
  obtain ⟨eta0, heta0, hcore⟩ := gcat_band_witness_tests_core d Cband J hCband beta a lam Cp p ha hlam
    hCp hp hdecay
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hle M n Tt Tn hTtmem hTnmem hTtnorm hTconv hTband
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp]
  let Ttb : Fin J → ℕ → BilateralField d → ℝ := fun i H =>
    (chaosSampleLaw M).toMeasure[Tt i | aux_gcat_band_condexp_Bsig d
      (n - ((Cband * (H + 1) : ℕ) : ℤ)) (n + ((Cband * (H + 1) : ℕ) : ℤ))]
  have hfac : ∀ H : ℕ, 2 * (Cp * eta / 2 * (3 : ℝ) ^ (-(a * (H : ℝ)))) =
      Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))) := by intro H; ring
  refine hcore eta heta hle (chaosSampleLaw M).toMeasure n Tt Ttb hTtmem hTtnorm
    (fun i H _ => stronglyMeasurable_condExp) (fun i H hH => ?_)
  have hev := hTband i H hH
  let Tsel : ℕ → BilateralField d → ℝ := fun kk =>
    if h : ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((Cband * (H + 1) : ℕ) : ℤ))
          (n + ((Cband * (H + 1) : ℕ) : ℤ))] Yn (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => Tn i kk om - Yn om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * eta / 2 * (3 : ℝ) ^ (-(a * (H : ℝ))))
    then Classical.choose h else fun _ => 0
  have hTsel : ∀ᶠ kk in atTop,
      AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((Cband * (H + 1) : ℕ) : ℤ))
        (n + ((Cband * (H + 1) : ℕ) : ℤ))] (Tsel kk) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Tn i kk om - Tsel kk om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cp * eta / 2 * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
    filter_upwards [hev] with kk hkk
    simp only [Tsel, dite_eq_left hkk]
    exact Classical.choose_spec hkk
  have key := (gcat_band_condexp d M (n - ((Cband * (H + 1) : ℕ) : ℤ))
    (n + ((Cband * (H + 1) : ℕ) : ℤ)) hp1 (hTtmem i) (hTnmem i) (hTconv i)
    (hYm := hTsel.mono fun kk hk => hk.1) (hYe := hTsel.mono fun kk hk => hk.2)).2
  refine key.trans (le_of_eq ?_)
  rw [hfac H]

end SubdiffusiveProcess.Paper
