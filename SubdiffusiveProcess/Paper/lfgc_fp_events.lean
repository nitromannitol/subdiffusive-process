import SubdiffusiveProcess.Paper.lfgc_fp_det
import SubdiffusiveProcess.Paper.lfgc_layer_tail

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Pad-test bank events: layer windows and tails

`aux_lfgc_fp_events_bankEv N i n y t` is the event that the layer-adapted bank of layer `i` of the canonical sample
at cutoff `N` exceeds `t`; it depends only on the bilateral layer `i - N`, and its probability
is at most `#cells · 2 e^{-(t/σ_M)^2}`.  `aux_lfgc_fp_events_amajEv N n j y T` is the event that the
product-window bank exceeds `T`; it depends only on the layers `n-j, …, n+j` (shifted by `-N`)
and its probability is bounded by the `R`-th moment through Markov's inequality.
-/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Layer-bank exceedance event of the canonical sample at cutoff `N`. -/
def aux_lfgc_fp_events_bankEv (N i n : ℕ) (y : Vec d) (t : ℝ) : Set (BilateralField d) :=
  {omega | t < Paper.aux_prefix_praw_bank i n y (aux_lfgc_layer_tail_canonEta N omega)}

/-- Product-window bank exceedance event of the canonical sample at cutoff `N`. -/
def aux_lfgc_fp_events_amajEv (N n j : ℕ) (y : Vec d) (T : ℝ) : Set (BilateralField d) :=
  {omega | ENNReal.ofReal T < Paper.aux_prefix_praw_Amaj n j y (aux_lfgc_layer_tail_canonEta N omega)}

theorem aux_lfgc_fp_events_canonEta_congr (N i : ℕ) {omega omega' : BilateralField d}
    (h : omega ((i : ℤ) - (N : ℤ)) = omega' ((i : ℤ) - (N : ℤ))) :
    aux_lfgc_layer_tail_canonEta N omega i = aux_lfgc_layer_tail_canonEta N omega' i := by
  unfold aux_lfgc_layer_tail_canonEta
  rw [h]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_fp_events_bank_congr (i n : ℕ) (y : Vec d) {g g' : PotentialSample d} (h : g i = g' i) :
    Paper.aux_prefix_praw_bank i n y g = Paper.aux_prefix_praw_bank i n y g' := by
  unfold Paper.aux_prefix_praw_bank Paper.aux_prefix_praw_cellField
  rw [h]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_fp_events_amaj_congr (n j : ℕ) (y : Vec d) {g g' : PotentialSample d}
    (h : ∀ i ∈ Finset.Icc (n - j) (n + j), g i = g' i) :
    Paper.aux_prefix_praw_Amaj n j y g = Paper.aux_prefix_praw_Amaj n j y g' := by
  unfold Paper.aux_prefix_praw_Amaj
  congr 1
  funext k
  congr 2
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold Paper.aux_prefix_praw_cellField
  rw [h i hi]

theorem aux_lfgc_fp_events_measurableSet_bankEv (N i n : ℕ) (y : Vec d) (t : ℝ) (s : Set ℤ)
    (hs : (i : ℤ) - (N : ℤ) ∈ s) :
    MeasurableSet[layerWindow C(SpatialCoordinates d, ℝ) s] (aux_lfgc_fp_events_bankEv N i n y t) := by
  have hm : Measurable (fun omega : BilateralField d =>
      Paper.aux_prefix_praw_bank i n y (aux_lfgc_layer_tail_canonEta N omega)) :=
    (Paper.aux_prefix_praw_bank_measurable i n y).comp (aux_lfgc_layer_tail_measurable_canonEta N)
  refine measurableSet_layerWindow_of_depends (measurableSet_lt measurable_const hm)
    fun ω ω' h => ?_
  have hb := aux_lfgc_fp_events_bank_congr i n y (aux_lfgc_fp_events_canonEta_congr N i (h _ hs))
  simp only [aux_lfgc_fp_events_bankEv, Set.mem_setOf_eq, hb]

theorem aux_lfgc_fp_events_measurableSet_amajEv (N n j : ℕ) (y : Vec d) (T : ℝ) (s : Set ℤ)
    (hs : ∀ i ∈ Finset.Icc (n - j) (n + j), (i : ℤ) - (N : ℤ) ∈ s) :
    MeasurableSet[layerWindow C(SpatialCoordinates d, ℝ) s] (aux_lfgc_fp_events_amajEv N n j y T) := by
  have hm : Measurable (fun omega : BilateralField d =>
      Paper.aux_prefix_praw_Amaj n j y (aux_lfgc_layer_tail_canonEta N omega)) :=
    (Paper.aux_prefix_praw_Amaj_measurable n j y).comp (aux_lfgc_layer_tail_measurable_canonEta N)
  refine measurableSet_layerWindow_of_depends (measurableSet_lt measurable_const hm)
    fun ω ω' h => ?_
  have hb := aux_lfgc_fp_events_amaj_congr n j y (fun i hi => aux_lfgc_fp_events_canonEta_congr N i (h _ (hs i hi)))
  simp only [aux_lfgc_fp_events_amajEv, Set.mem_setOf_eq, hb]

/-- Transport of a sample event through the canonical sample. -/
theorem aux_lfgc_fp_events_prob_canonEta (M : GMCModel d) (N : ℕ) {S : Set (PotentialSample d)}
    (hS : MeasurableSet S) :
    (chaosSampleLaw M).toMeasure (aux_lfgc_layer_tail_canonEta N ⁻¹' S) = M.P.toMeasure S := by
  rw [← Measure.map_apply (aux_lfgc_layer_tail_measurable_canonEta N) hS, aux_lfgc_layer_tail_map_canonEta M N]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Chernoff bound from a linear exponential moment. -/
theorem aux_lfgc_fp_events_chernoff_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X : Ω → ℝ}
    (hX : Measurable X) {lam t : ℝ} (hlam : 0 ≤ lam) {B : ℝ≥0∞}
    (hB : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ ≤ B) :
    μ {ω | t < X ω} ≤ B * ENNReal.ofReal (Real.exp (-(lam * t))) := by
  set c := ENNReal.ofReal (Real.exp (lam * t))
  have hsub : {ω | t < X ω} ⊆ {ω | c ≤ ENNReal.ofReal (Real.exp (lam * X ω))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.le hlam))
  have hfm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (lam * X ω))) μ :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hX.const_mul lam))).aemeasurable
  have hM := mul_meas_ge_le_lintegral₀ hfm c
  have hc0 : c ≠ 0 := by simpa [c] using Real.exp_pos (lam * t)
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  calc μ {ω | t < X ω} ≤ μ {ω | c ≤ ENNReal.ofReal (Real.exp (lam * X ω))} := measure_mono hsub
    _ ≤ B / c := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct), mul_comm]
        exact hM.trans hB
    _ = B * ENNReal.ofReal (Real.exp (-(lam * t))) := by
        rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]

/-- Sub-Gaussian tail of a layer-bank event. -/
theorem lfgc_fp_events (M : GMCModel d) (N i n : ℕ) (y : Vec d) {t : ℝ} (ht : 0 ≤ t) :
    (chaosSampleLaw M).toMeasure (aux_lfgc_fp_events_bankEv N i n y t) ≤
      ((Paper.aux_psf_cells d (n - i)).card : ℝ≥0∞) * 2 *
        ENNReal.ofReal (Real.exp (-(t / Paper.aux_psf_sigma M) ^ 2)) := by
  have hσ := Paper.aux_psf_sigma_pos M
  have hm := Paper.aux_prefix_praw_bank_measurable (d := d) i n y
  rw [show aux_lfgc_fp_events_bankEv N i n y t = aux_lfgc_layer_tail_canonEta N ⁻¹' {g | t < Paper.aux_prefix_praw_bank i n y g} from rfl,
    aux_lfgc_fp_events_prob_canonEta M N (measurableSet_lt measurable_const hm)]
  have hlam : 0 ≤ 2 * t / Paper.aux_psf_sigma M ^ 2 := by positivity
  refine (aux_lfgc_fp_events_chernoff_le M.P.toMeasure hm hlam
    (Paper.aux_prefix_praw_bank_exp_lin M i n y (2 * t / Paper.aux_psf_sigma M ^ 2))).trans
    (le_of_eq ?_)
  have hAB : ENNReal.ofReal (Real.exp ((2 * t / Paper.aux_psf_sigma M ^ 2) ^ 2 *
        Paper.aux_psf_sigma M ^ 2 / 4)) *
      ENNReal.ofReal (Real.exp (-(2 * t / Paper.aux_psf_sigma M ^ 2 * t))) =
      ENNReal.ofReal (Real.exp (-(t / Paper.aux_psf_sigma M) ^ 2)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [← hAB]
  ring

/-- Markov tail of a product-window bank event through its `R`-th moment. -/
theorem aux_lfgc_fp_events_amajEv_prob (M : GMCModel d) (N n j : ℕ) (y : Vec d) {T R : ℝ} (hT : 0 < T)
    (hR : 0 < R) :
    (chaosSampleLaw M).toMeasure (aux_lfgc_fp_events_amajEv N n j y T) ≤
      ((Paper.aux_psf_cells d (n + 1 + j - (n - j))).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (R ^ 2 * Paper.aux_psf_sigma M ^ 2 / 4)) * 2) ^
          ((Finset.Icc (n - j) (n + j)).card) / ENNReal.ofReal T ^ R := by
  have hm := Paper.aux_prefix_praw_Amaj_measurable (d := d) n j y
  rw [show aux_lfgc_fp_events_amajEv N n j y T = aux_lfgc_layer_tail_canonEta N ⁻¹' {g | ENNReal.ofReal T <
      Paper.aux_prefix_praw_Amaj n j y g} from rfl,
    aux_lfgc_fp_events_prob_canonEta M N (measurableSet_lt measurable_const hm)]
  set c := ENNReal.ofReal T ^ R
  have hsub : {g : PotentialSample d | ENNReal.ofReal T < Paper.aux_prefix_praw_Amaj n j y g} ⊆
      {g | c ≤ (Paper.aux_prefix_praw_Amaj n j y g) ^ R} := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    exact ENNReal.rpow_le_rpow hg.le hR.le
  have hfm : AEMeasurable (fun g => (Paper.aux_prefix_praw_Amaj n j y g) ^ R) M.P.toMeasure :=
    (hm.pow_const R).aemeasurable
  have hMk := mul_meas_ge_le_lintegral₀ hfm c
  have hc0 : c ≠ 0 := by
    simp only [c]
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hT) ENNReal.ofReal_ne_top).ne'
  have hct : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hR.le ENNReal.ofReal_ne_top
  calc M.P.toMeasure {g | ENNReal.ofReal T < Paper.aux_prefix_praw_Amaj n j y g}
      ≤ M.P.toMeasure {g | c ≤ (Paper.aux_prefix_praw_Amaj n j y g) ^ R} := measure_mono hsub
    _ ≤ _ := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct), mul_comm]
        exact hMk.trans (Paper.aux_prefix_praw_Amaj_rpow_lintegral M n j y R)

end Paper
