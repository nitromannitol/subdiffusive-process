module

public import SubdiffusiveProcess.Paper.gcat_band_condexp
public import SubdiffusiveProcess.Paper.gcat_band_witness_prefix_core

@[expose] public section

open MeasureTheory Filter Set SubdiffusiveProcess
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The prefix cover with band approximants supplied by the finite-cutoff band approximation: the limit terms
`Y` are `L^p`-limits of sequences `Xn`, each within `Cp·η·3^{-aH}/2` of a layer-band-measurable function, and
the band approximants of the limits are their conditional expectations.  `eta0` precedes the model. -/
theorem gcat_band_witness_prefix_core2
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cband c0 k0 : ℕ) (hCband : 0 < Cband) (hk0 : 1 ≤ k0)
    (beta a lam v Cgeom : ℝ) (hbeta : 0 < beta) (ha : 0 < a) (hlam : 0 < lam)
    (hv : 0 ≤ v) (hCgeom : 1 ≤ Cgeom)
    (p A Ctail Cp : ℝ) (hp : 2 ≤ p) (hCtail : 0 < Ctail) (hCp : 0 < Cp)
    (hA : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ A)
    (hpRate : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ p * a * Real.log 3)
    (hAk0 : Real.log (9 * Cgeom * Ctail) + beta * ((Cband : ℝ) + (c0 : ℝ)) ≤
      (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ)) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℤ)
        (I : ℕ → Type) [∀ D, Fintype (I D)],
      (∀ D, (Fintype.card (I D) : ℝ) ≤ Cgeom * Real.exp (v * (D : ℝ))) →
      ∀ (s : (D : ℕ) → I D → ℕ → ℤ),
      (∀ D i j, j < D → n - (c0 : ℤ) ≤ s D i j ∧ s D i j ≤ n + (c0 : ℤ) + (D : ℤ)) →
      ∀ (Y : (D : ℕ) → I D → ℕ → BilateralField d → ℝ)
        (Xn : (D : ℕ) → I D → ℕ → ℕ → BilateralField d → ℝ),
      (∀ D i j, MemLp (Y D i j) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
      (∀ D i j kk, MemLp (Xn D i j kk) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
      (∀ D i j, Tendsto (fun kk => eLpNorm (Xn D i j kk - Y D i j) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) →
      (∀ D i j H, 1 ≤ H → ∀ᶠ kk in atTop, ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d (s D i j - ((Cband * (H + 1) : ℕ) : ℤ))
          (s D i j + ((Cband * (H + 1) : ℕ) : ℤ))] Yn (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => Xn D i j kk om - Yn om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * eta / 2 * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
      (∀ D, k0 ≤ D → ∀ i : I D,
        (chaosSampleLaw M).toMeasure {om | lam * (D : ℝ) / 4 < ∑ j ∈ Finset.range D, Y D i j om} ≤
          ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ))))) →
      ∃ Sigma : Set (BilateralField d), MeasurableSet Sigma ∧ (chaosSampleLaw M).toMeasure Sigma = 1 ∧
        ∃ W : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d (n - (h : ℤ)) (n + 2 * (h : ℤ))]
            (W h)) ∧
          (∀ h : ℕ+, (chaosSampleLaw M).toMeasure (W h) ≤
            ENNReal.ofReal (Real.exp (-(beta * ((h : ℕ) : ℝ))))) ∧
          Sigma ∩ {om | ∃ D, k0 ≤ D ∧ ∃ i : I D,
            lam * (D : ℝ) ≤ ∑ j ∈ Finset.range D, Y D i j om} ⊆ ⋃ h : ℕ+, W h := by
  classical
  obtain ⟨eta0, heta0, hcore⟩ := gcat_band_witness_prefix_core d Cband c0 k0 hCband hk0
    beta a lam v Cgeom hbeta ha hlam hv hCgeom p A Ctail Cp hp hCtail hCp hA hpRate hAk0
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hle M n I instI hcard s hs Y Xn hYmem hXnmem hYconv hYband htailP
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp]
  let Yb : (D : ℕ) → I D → ℕ → ℕ → BilateralField d → ℝ := fun D i j H =>
    (chaosSampleLaw M).toMeasure[Y D i j | aux_gcat_band_condexp_Bsig d
      (s D i j - ((Cband * (H + 1) : ℕ) : ℤ)) (s D i j + ((Cband * (H + 1) : ℕ) : ℤ))]
  have hfac : ∀ H : ℕ, 2 * (Cp * eta / 2 * (3 : ℝ) ^ (-(a * (H : ℝ)))) =
      Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))) := by intro H; ring
  refine hcore eta heta hle (chaosSampleLaw M).toMeasure n I hcard s hs Y Yb hYmem
    (fun D i j H _ => stronglyMeasurable_condExp) (fun D i j H hH => ?_) htailP
  have hev := hYband D i j H hH
  let Ysel : ℕ → BilateralField d → ℝ := fun kk =>
    if h : ∃ Yn : BilateralField d → ℝ,
        AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d (s D i j - ((Cband * (H + 1) : ℕ) : ℤ))
          (s D i j + ((Cband * (H + 1) : ℕ) : ℤ))] Yn (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => Xn D i j kk om - Yn om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * eta / 2 * (3 : ℝ) ^ (-(a * (H : ℝ))))
    then Classical.choose h else fun _ => 0
  have hYsel : ∀ᶠ kk in atTop,
      AEStronglyMeasurable[aux_gcat_band_condexp_Bsig d (s D i j - ((Cband * (H + 1) : ℕ) : ℤ))
        (s D i j + ((Cband * (H + 1) : ℕ) : ℤ))] (Ysel kk) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Xn D i j kk om - Ysel kk om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cp * eta / 2 * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
    filter_upwards [hev] with kk hkk
    simp only [Ysel, dif_pos hkk]
    exact Classical.choose_spec hkk
  have key := (gcat_band_condexp d M (s D i j - ((Cband * (H + 1) : ℕ) : ℤ))
    (s D i j + ((Cband * (H + 1) : ℕ) : ℤ)) hp1 (hYmem D i j) (hXnmem D i j) (hYconv D i j)
    (hYm := hYsel.mono fun kk hk => hk.1) (hYe := hYsel.mono fun kk hk => hk.2)).2
  refine key.trans (le_of_eq ?_)
  rw [hfac H]

end Paper
