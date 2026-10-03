module

public import SubdiffusiveProcess.Paper.product_threshold_good_scale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowMean
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.CampanatoWindowGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness

@[expose] public section

/-! On the threshold-12 good event, the tail coefficient `b_{L,m}` oscillates by at most the factor
`12^{1/4}` on the window `□_m(y0)`, and its window average is comparable to its value at `y0`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- Finite partial products of real factors `≥ 1` are dominated by the infinite product. -/
theorem aux_lem_as_regularity_tail_reference_prod_le_tprod {f : ℕ → ℝ} (hf1 : ∀ i, 1 ≤ f i)
    (hm : Multipliable f) (s : Finset ℕ) : ∏ i ∈ s, f i ≤ ∏' i, f i := by
  refine ge_of_tendsto hm.hasProd ?_
  filter_upwards [Filter.eventually_ge_atTop s] with t hts
  rw [← Finset.prod_sdiff hts]
  have h1 : 1 ≤ ∏ i ∈ t \ s, f i := by
    calc (1 : ℝ) = ∏ i ∈ t \ s, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => hf1 i)
  have hs : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hf1 i))
  nlinarith

/-- The tail coefficient is `ahom_m` times the exponential of the layers `m+1..L`. -/
theorem aux_lem_as_regularity_tail_reference_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {L m : ℕ} (hmL : m ≤ L) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    tailCoefficient M L m ω x = ahom M m *
      Real.exp (∑ i ∈ Finset.Ico (m + 1) (L + 1),
        (ω i x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
  unfold tailCoefficient SubdiffusiveProcess.Frozen.Assumptions.aCutoff
  rw [min_eq_left hmL, ← Real.exp_sub]
  congr 2
  rw [← Finset.sum_range_add_sum_Ico _ (show m + 1 ≤ L + 1 by omega)]
  ring

/-- The finite tail sum of the oscillations of the layers is at most `log 12 / 4`. -/
theorem aux_lem_as_regularity_tail_reference_osc {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {L m : ℕ} (hmL : m ≤ L) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y0 : Vec d)
    (cutoff : Option ℕ) (e s : ℝ)
    (h12 : ω ∈ Paper.product_threshold_good_scale d M 12 cutoff m y0 e s)
    (x : Vec d) (hx : x ∈ translatedCube d (m : ℤ) y0) :
    ∑ i ∈ Finset.Ico (m + 1) (L + 1), |ω i x - ω i y0| ≤ Real.log 12 / 4 := by
  obtain ⟨_, _, _, _, _, _, hP, _⟩ := h12
  obtain ⟨hmul, hbdd, hsup⟩ := hP 0
  have hxT : x ∈ translatedCube d ((m : ℤ) + 1 + ((0 : ℕ) : ℤ)) y0 := by
    have := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.translatedCube_subset_translatedCube_sameCenter
      (d := d) (ell := (m : ℤ)) (top := (m : ℤ) + 1 + ((0 : ℕ) : ℤ)) (by simp) y0 hx
    exact this
  set f : ℕ → ℝ := fun i => if m + 0 ≤ i then Real.exp (4 * |ω i x - ω i y0|) else 1 with hf
  have hfm : Multipliable f := hmul x hxT
  have hf1 : ∀ i, 1 ≤ f i := by
    intro i
    simp only [hf]
    split_ifs
    · exact Real.one_le_exp (by positivity)
    · exact le_rfl
  have hprod : ∏ i ∈ Finset.Ico (m + 1) (L + 1), Real.exp (4 * |ω i x - ω i y0|) ≤ ∏' i, f i := by
    have h1 : ∏ i ∈ Finset.Ico (m + 1) (L + 1), Real.exp (4 * |ω i x - ω i y0|) =
        ∏ i ∈ Finset.Ico (m + 1) (L + 1), f i := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have : m + 0 ≤ i := by have := (Finset.mem_Ico.1 hi).1; omega
      simp only [hf, if_pos this]
    rw [h1]
    exact aux_lem_as_regularity_tail_reference_prod_le_tprod hf1 hfm _
  -- the pointwise value of the P-function is at most 12
  set g : ℝ := (∏ i ∈ Finset.Icc (m - 0) (m + 0), Real.exp |ω i x|) + ∏' i, f i with hg
  have hgle : g ≤ 12 * (3 : ℝ) ^ (s * ((0 : ℕ) : ℝ) / 8) := by
    have h1 : g ≤ |g| := le_abs_self _
    have h2 : |g| ≤ supNormOn (translatedCube d ((m : ℤ) + 1 + ((0 : ℕ) : ℤ)) y0) (fun x =>
        (∏ i ∈ Finset.Icc (m - 0) (m + 0), Real.exp |ω i x|) +
          ∏' i : ℕ, if m + 0 ≤ i then Real.exp (4 * |ω i x - ω i y0|) else 1) := by
      unfold supNormOn
      refine le_csSup ?_ ⟨x, hxT, rfl⟩
      convert hbdd using 1
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨x', hx', rfl⟩; exact ⟨x', hx', rfl⟩
      · rintro ⟨x', hx', rfl⟩; exact ⟨x', hx', rfl⟩
    exact h1.trans (h2.trans hsup)
  have hg0 : (1 : ℝ) ≤ ∏ i ∈ Finset.Icc (m - 0) (m + 0), Real.exp |ω i x| := by
    calc (1 : ℝ) = ∏ i ∈ Finset.Icc (m - 0) (m + 0), (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
        (fun i _ => Real.one_le_exp (abs_nonneg _))
  simp only [Nat.cast_zero, mul_zero, zero_div, Real.rpow_zero, mul_one] at hgle
  have hpt : ∏' i, f i ≤ 12 := by linarith
  have hexp : Real.exp (4 * ∑ i ∈ Finset.Ico (m + 1) (L + 1), |ω i x - ω i y0|) ≤ 12 := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact hprod.trans hpt
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  linarith

/-- Two-sided oscillation bound for the tail coefficient on the window. -/
theorem aux_lem_as_regularity_tail_reference_bounds {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {L m : ℕ} (hmL : m ≤ L) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y0 : Vec d)
    (cutoff : Option ℕ) (e s : ℝ)
    (h12 : ω ∈ Paper.product_threshold_good_scale d M 12 cutoff m y0 e s)
    (x : Vec d) (hx : x ∈ translatedCube d (m : ℤ) y0) :
    (12 : ℝ) ^ (-(1 / 4 : ℝ)) * tailCoefficient M L m ω y0 ≤ tailCoefficient M L m ω x ∧
      tailCoefficient M L m ω x ≤ (12 : ℝ) ^ (1 / 4 : ℝ) * tailCoefficient M L m ω y0 := by
  have hosc := aux_lem_as_regularity_tail_reference_osc M hmL ω y0 cutoff e s h12 x hx
  rw [aux_lem_as_regularity_tail_reference_eq M hmL, aux_lem_as_regularity_tail_reference_eq M hmL]
  have hah : 0 < ahom M m := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m
  have hdiff : ∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω i x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      (∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω i y0 - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) +
        ∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω i x - ω i y0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have habs : |∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω i x - ω i y0)| ≤ Real.log 12 / 4 :=
    (Finset.abs_sum_le_sum_abs _ _).trans hosc
  have h12pos : (0 : ℝ) < 12 := by norm_num
  have hlow : -(Real.log 12 / 4) ≤ ∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω i x - ω i y0) :=
    (abs_le.1 habs).1
  have hup : ∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω i x - ω i y0) ≤ Real.log 12 / 4 :=
    (abs_le.1 habs).2
  have e1 : (12 : ℝ) ^ (1 / 4 : ℝ) = Real.exp (Real.log 12 / 4) := by
    rw [Real.rpow_def_of_pos h12pos]; congr 1; ring
  have e2 : (12 : ℝ) ^ (-(1 / 4 : ℝ)) = Real.exp (-(Real.log 12 / 4)) := by
    rw [Real.rpow_def_of_pos h12pos]; congr 1; ring
  rw [hdiff, Real.exp_add, e1, e2]
  set E := Real.exp (∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω i y0 - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
  set D := Real.exp (∑ i ∈ Finset.Ico (m + 1) (L + 1), (ω i x - ω i y0))
  have hE : 0 < E := Real.exp_pos _
  have hD1 : Real.exp (-(Real.log 12 / 4)) ≤ D := Real.exp_le_exp.2 hlow
  have hD2 : D ≤ Real.exp (Real.log 12 / 4) := Real.exp_le_exp.2 hup
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hD1 (mul_pos hah hE).le]
  · nlinarith [mul_le_mul_of_nonneg_left hD2 (mul_pos hah hE).le]

/-- On the threshold-12 good event the window average of the tail coefficient is comparable to its
value at the centre. -/
theorem lem_as_regularity_tail_reference {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y0 : Vec d)
    (cutoff : Option ℕ) (e s : ℝ)
    (h12 : ω ∈ Paper.product_threshold_good_scale d M 12 cutoff m y0 e s) :
    (12 : ℝ) ^ (-(1 / 4 : ℝ)) * tailCoefficient M L m ω y0 ≤
      tailAverage M L m ω (translatedCube d (m : ℤ) y0) := by
  have hb := fun x hx => aux_lem_as_regularity_tail_reference_bounds M hmL ω y0 cutoff e s h12 x hx
  have hWm : MeasurableSet (translatedCube d (m : ℤ) y0) :=
    (isOpenBoundedConvexDomain_translatedCube (m : ℤ) y0).isOpen.measurableSet
  have hvol := Section6BoundedMultiplier.volume_translatedCube_toReal_pos (d := d) (m : ℤ) y0
  have hfin := Section6BoundedMultiplier.volume_translatedCube_ne_top (d := d) (m : ℤ) y0
  have hcont := continuous_tailCoefficient M L m ω
  have hint : IntegrableOn (tailCoefficient M L m ω) (translatedCube d (m : ℤ) y0) := by
    refine Measure.integrableOn_of_bounded (M := (12 : ℝ) ^ (1 / 4 : ℝ) * tailCoefficient M L m ω y0)
      hfin hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hWm] with x hx
    have h := hb x hx
    have hpos : 0 < tailCoefficient M L m ω x := by
      have h1 : 0 < (12 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
      have h2 : 0 < tailCoefficient M L m ω y0 :=
        tailCoefficient_pos_of_ahom_pos M L m ω
          (by rw [min_eq_left hmL]; exact SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m) y0
      exact lt_of_lt_of_le (mul_pos h1 h2) h.1
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact h.2
  have hmono : ∫ x in translatedCube d (m : ℤ) y0,
      (12 : ℝ) ^ (-(1 / 4 : ℝ)) * tailCoefficient M L m ω y0 ≤
      ∫ x in translatedCube d (m : ℤ) y0, tailCoefficient M L m ω x :=
    setIntegral_mono_on (integrableOn_const hfin) hint hWm (fun x hx => (hb x hx).1)
  unfold tailAverage volumeAverage
  rw [setIntegral_const, smul_eq_mul] at hmono
  have hvol0 : 0 < (volume (translatedCube d (m : ℤ) y0)).toReal := hvol
  rw [le_inv_mul_iff₀ hvol0]
  simpa [mul_comm, Measure.real] using hmono

end Paper
