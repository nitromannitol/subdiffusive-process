import SubdiffusiveProcess.Paper.lfgc_infrared_osc
import SubdiffusiveProcess.Lfgc.Window
import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Sub-Gaussian tail of single-layer oscillations

`aux_lfgc_layer_tail_canonEta N ω` is the canonical potential sample of the bilateral field at cutoff `N`
(layer `i` is the rescaled `ω (i - N)`); its law is `M.P`, and its layer `i` depends only on
`ω (i - N)`.  On the event where a given sample `eta` has the canonical formula, a layer
oscillation on a closed cube of side `r ≤ 27` forces one of `57^d` unit-cell observables of
the canonical sample to be large.  Each such observable has the sub-Gaussian tail
`P(t < cellObs) ≤ 2 exp(-(t/σ_M)^2)` from `aux_psf_cell_exp`.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The canonical potential sample at cutoff `N`. -/
noncomputable def aux_lfgc_layer_tail_canonEta (N : ℕ) (omega : BilateralField d) : PotentialSample d :=
  fun i : ℕ => Paper.aux_lem_crossing_unforget
    (SubdiffusiveProcess.layerScaling d (N : ℤ) (omega ((i : ℤ) - (N : ℤ))))

theorem aux_lfgc_layer_tail_measurable_canonEta (N : ℕ) : Measurable (aux_lfgc_layer_tail_canonEta (d := d) N) := by
  refine measurable_pi_iff.mpr fun i =>
    Paper.aux_lem_crossing_measurable_unforget.comp
      ((SubdiffusiveProcess.layerScaling d (N : ℤ)).continuous.measurable.comp
        (measurable_pi_apply ((i : ℤ) - (N : ℤ))))

theorem aux_lfgc_layer_tail_canonEta_eq (N : ℕ) (eta : BilateralField d → PotentialSample d) (omega : BilateralField d)
    (h : ∀ (i : ℕ) (y : Vec d), eta omega i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) :
    eta omega = aux_lfgc_layer_tail_canonEta N omega := by
  funext i
  have hf : SubdiffusiveProcess.layerScaling d (N : ℤ)
      (omega ((i : ℤ) - (N : ℤ))) = Paper.aux_lem_crossing_forget (eta omega i) := by
    apply ContinuousMap.ext
    intro y
    simpa [SubdiffusiveProcess.layerScaling, Paper.aux_lem_crossing_forget] using (h i y).symm
  unfold aux_lfgc_layer_tail_canonEta
  rw [hf, Paper.aux_lem_crossing_unforget_forget]

theorem aux_lfgc_layer_tail_map_canonEta (M : GMCModel d) (N : ℕ) :
    Measure.map (aux_lfgc_layer_tail_canonEta N) (chaosSampleLaw M).toMeasure = M.P.toMeasure :=
  Paper.prefix_relabelled_potential_law M N

/-- Sub-Gaussian tail of a unit-cell observable of the canonical sample. -/
theorem lfgc_layer_tail (M : GMCModel d) (N i : ℕ) (y : Vec d) {t : ℝ} (ht : 0 ≤ t) :
    (chaosSampleLaw M).toMeasure {omega | t < Paper.aux_psf_cellObs i y (aux_lfgc_layer_tail_canonEta N omega)} ≤
      2 * ENNReal.ofReal (Real.exp (-(t / Paper.aux_psf_sigma M) ^ 2)) := by
  have hsig := Paper.aux_psf_sigma_pos M
  set σ := Paper.aux_psf_sigma M
  have hmeas : Measurable fun g : PotentialSample d => Paper.aux_psf_cellObs i y g :=
    Paper.aux_psf_cellObs_measurable i y
  rw [show {omega | t < Paper.aux_psf_cellObs i y (aux_lfgc_layer_tail_canonEta N omega)} =
      aux_lfgc_layer_tail_canonEta N ⁻¹' {g | t < Paper.aux_psf_cellObs i y g} from rfl]
  rw [← Measure.map_apply (aux_lfgc_layer_tail_measurable_canonEta N) (measurableSet_lt measurable_const hmeas),
    aux_lfgc_layer_tail_map_canonEta M N]
  set f : PotentialSample d → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (Real.exp ((Paper.aux_psf_cellObs i y g / σ) ^ (2 : ℕ)))
  have hsub : {g : PotentialSample d | t < Paper.aux_psf_cellObs i y g} ⊆
      {g | ENNReal.ofReal (Real.exp ((t / σ) ^ 2)) ≤ f g} := by
    intro g hg
    simp only [Set.mem_setOf_eq, f] at hg ⊢
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have h1 : t / σ ≤ Paper.aux_psf_cellObs i y g / σ := div_le_div_of_nonneg_right hg.le hsig.le
    have h0 : 0 ≤ t / σ := div_nonneg ht hsig.le
    nlinarith
  have hfm : AEMeasurable f M.P.toMeasure :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hmeas.div_const σ).pow_const 2))).aemeasurable
  have hM := mul_meas_ge_le_lintegral₀ hfm (ENNReal.ofReal (Real.exp ((t / σ) ^ 2)))
  have hint : ∫⁻ g, f g ∂M.P.toMeasure ≤ 2 := Paper.aux_psf_cell_exp M i y
  have hpos : ENNReal.ofReal (Real.exp ((t / σ) ^ 2)) ≠ 0 := by
    simpa using Real.exp_pos _
  have htop : ENNReal.ofReal (Real.exp ((t / σ) ^ 2)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc M.P.toMeasure {g | t < Paper.aux_psf_cellObs i y g}
      ≤ M.P.toMeasure {g | ENNReal.ofReal (Real.exp ((t / σ) ^ 2)) ≤ f g} := measure_mono hsub
    _ ≤ 2 / ENNReal.ofReal (Real.exp ((t / σ) ^ 2)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl htop), mul_comm]
        exact hM.trans hint
    _ = 2 * ENNReal.ofReal (Real.exp (-(t / σ) ^ 2)) := by
        rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]

end Paper
