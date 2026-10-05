module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.rem_resolved_microscopic
public import SubdiffusiveProcess.Paper.prop_growth_common_moment_bank
public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
public import SubdiffusiveProcess.Paper.prop_growth_holder_micro_campanato
public import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Choose a natural `n` large enough so that `n ≥ 2`, `n > 2*d/(d-t)`, and `n > d/(1-alpha)`.
    Then set `p1 := (n : ℝ)` and verify the three inequalities. -/
theorem aux_prop_growth_holder_assembly_p1_choice (d : ℕ) (hd : 2 ≤ d) (t alpha : ℝ)
    (ht_low : (d : ℝ) - 1 < t) (ht_high : t < (d : ℝ))
    (_halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1) :
    ∃ p1 : ℝ, 2 ≤ p1 ∧ t < (d : ℝ) - 2 * (d : ℝ) / p1 ∧ alpha < 1 - (d : ℝ) / p1 := by
  -- The two deficits are strictly positive
  have h_deficit_t : 0 < (d : ℝ) - t := by linarith
  have h_deficit_alpha : 0 < 1 - alpha := by linarith
  -- The dimension is at least 2, so d ≥ 2 as a real
  have hd_pos_real : 0 < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact mod_cast (show 1 ≤ d from by omega)
    linarith
  -- Upper bounds for the two quotients
  set q1 : ℝ := (2 * (d : ℝ)) / ((d : ℝ) - t) with hq1_def
  set q2 : ℝ := (d : ℝ) / (1 - alpha) with hq2_def
  have hq1_pos : 0 < q1 := by
    rw [hq1_def]
    exact div_pos (by nlinarith) h_deficit_t
  have hq2_pos : 0 < q2 := by
    rw [hq2_def]
    exact div_pos hd_pos_real h_deficit_alpha
  -- By the Archimedean property, there exist naturals strictly above each bound
  obtain ⟨n1, hn1⟩ : ∃ n : ℕ, q1 < (n : ℝ) := exists_nat_gt q1
  obtain ⟨n2, hn2⟩ : ∃ n : ℕ, q2 < (n : ℝ) := exists_nat_gt q2
  -- Take n = max 2 (max n1 n2) as the witness
  let n : ℕ := max 2 (max n1 n2)
  have hn_ge_two : 2 ≤ n := le_max_left _ _
  have hn_pos_real : 0 < (n : ℝ) := by
    have : (0 : ℝ) < 2 := by norm_num
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact mod_cast hn_ge_two
    linarith
  have hn_gt_q1 : q1 < (n : ℝ) := by
    have hn1_le_max : (n1 : ℝ) ≤ (max n1 n2 : ℝ) := by exact mod_cast le_max_left _ _
    have hmax_le_n : (max n1 n2 : ℝ) ≤ (n : ℝ) := by exact mod_cast le_max_right _ _
    linarith [hn1, hn1_le_max, hmax_le_n]
  have hn_gt_q2 : q2 < (n : ℝ) := by
    have hn2_le_max : (n2 : ℝ) ≤ (max n1 n2 : ℝ) := by exact mod_cast le_max_right _ _
    have hmax_le_n : (max n1 n2 : ℝ) ≤ (n : ℝ) := by exact mod_cast le_max_right _ _
    linarith [hn2, hn2_le_max, hmax_le_n]
  -- Set p1 := (n : ℝ) and verify the three conjuncts
  refine ⟨(n : ℝ), by exact mod_cast hn_ge_two, ?_, ?_⟩
  · -- t < d - 2*d/n
    rw [hq1_def] at hn_gt_q1
    -- hn_gt_q1: (2*d)/(d-t) < n
    -- Multiply by (d-t) > 0: 2*d < n*(d-t)
    have hineq : (2 * (d : ℝ)) < (n : ℝ) * ((d : ℝ) - t) :=
      (div_lt_iff₀ h_deficit_t).mp hn_gt_q1
    -- Goal: t < d - 2*d/n  ↔  t*n < d*n - 2*d
    field_simp [hn_pos_real.ne.symm]
    nlinarith
  · -- alpha < 1 - d/n
    rw [hq2_def] at hn_gt_q2
    -- hn_gt_q2: d/(1-alpha) < n
    -- Multiply by (1-alpha) > 0: d < n*(1-alpha)
    have hineq : (d : ℝ) < (n : ℝ) * (1 - alpha) :=
      (div_lt_iff₀ h_deficit_alpha).mp hn_gt_q2
    -- Goal: alpha < 1 - d/n  ↔  alpha*n < n - d
    field_simp [hn_pos_real.ne.symm]
    nlinarith

/-- Jointly choose the microscopic integrability order, intermediate energy
exponent, and a positive rate below all three cutoff-decay thresholds. -/
theorem aux_prop_growth_holder_assembly_param_choice
    (d : ℕ) (hd : 2 ≤ d) (t alpha : ℝ)
    (ht_low : (d : ℝ) - 1 < t) (ht_high : t < (d : ℝ))
    (halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1) :
    ∃ (p1 t1 aRate : ℝ),
      2 ≤ p1 ∧
      t < (d : ℝ) - 2 * (d : ℝ) / p1 ∧
      alpha < 1 - (d : ℝ) / p1 ∧
      t < t1 ∧
      t1 < (d : ℝ) ∧
      0 < aRate ∧
      aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := by
  obtain ⟨p1, hp1_ge_two, hp1_t, hp1_alpha⟩ :=
    aux_prop_growth_holder_assembly_p1_choice d hd t alpha ht_low ht_high
      halpha_pos halpha_lt_one
  set t1 : ℝ := (t + (d : ℝ)) / 2 with ht1_def
  have ht_lt_t1 : t < t1 := by
    dsimp [t1]
    linarith
  have ht1_lt_d : t1 < (d : ℝ) := by
    dsimp [t1]
    linarith
  set pos_rate : ℝ :=
    min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3
      with hpos_rate_def
  have h_log3_pos : 0 < Real.log 3 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have h_pos_rate_pos : 0 < pos_rate := by
    rw [hpos_rate_def]
    refine mul_pos ?_ h_log3_pos
    refine lt_min_iff.mpr ⟨?_, ?_⟩
    · linarith
    · refine lt_min_iff.mpr ⟨?_, ?_⟩ <;> linarith
  set aRate : ℝ := pos_rate / 2 with haRate_def
  have haRate_pos : 0 < aRate := by
    dsimp [aRate]
    exact half_pos h_pos_rate_pos
  have haRate_lt_pos_rate : aRate < pos_rate := by
    dsimp [aRate]
    nlinarith
  refine ⟨p1, t1, aRate, hp1_ge_two, hp1_t, hp1_alpha,
    ht_lt_t1, ht1_lt_d, haRate_pos, ?_⟩
  rw [haRate_def, hpos_rate_def]
  exact haRate_lt_pos_rate

/-- Two points of the closed cube of side `r ≤ 1` are at Euclidean distance at most `√d`. -/
theorem aux_prop_growth_holder_assembly_euclid_le {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {x y : SpatialCoordinates d}
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)))
    (hy : y ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d := by
  apply Real.sqrt_le_sqrt
  have hx' : dist x z ≤ r / 2 := hx
  have hy' : dist y z ≤ r / 2 := hy
  have hxy : dist x y ≤ 1 := by
    calc dist x y ≤ dist x z + dist y z := dist_triangle_right x y z
      _ ≤ r / 2 + r / 2 := add_le_add hx' hy'
      _ ≤ 1 := by linarith
  have hcoord : ∀ j : Fin d, (x j - y j) ^ 2 ≤ 1 := by
    intro j
    have hj : dist (x j) (y j) ≤ 1 := (dist_le_pi_dist x y j).trans hxy
    rw [Real.dist_eq] at hj
    have h0 : 0 ≤ |x j - y j| := abs_nonneg _
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ h0 hj 2
      _ = 1 := one_pow 2
  calc (∑ j : Fin d, (x j - y j) ^ 2) ≤ ∑ _j : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => hcoord j
    _ = d := by simp

/-- `e ^ alpha ≤ 1 + e` for `0 ≤ e` and `0 < alpha ≤ 1`. -/
theorem aux_prop_growth_holder_assembly_rpow_le {e alpha : ℝ} (he : 0 ≤ e)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) : e ^ alpha ≤ 1 + e := by
  rcases le_total e 1 with h | h
  · have := Real.rpow_le_one he h ha0.le
    linarith
  · have : e ^ alpha ≤ e ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h ha1
    rw [Real.rpow_one] at this
    linarith

/-- The Hölder seminorm is nonnegative. -/
theorem aux_prop_growth_holder_assembly_seminorm_nonneg {d : ℕ} (alpha : ℝ)
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) :
    0 ≤ holderSeminorm alpha S U := by
  apply Real.sSup_nonneg
  rintro v ⟨x, _, y, _, _, rfl⟩
  exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- Pointwise Hölder increment on the closed cube of side `r ≤ 1`. -/
theorem aux_prop_growth_holder_assembly_increment {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {U : SpatialCoordinates d → ℝ}
    (hH : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U)
    {x y : SpatialCoordinates d}
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)))
    (hy : y ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    |U x - U y| ≤
      (1 + Real.sqrt d) * holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U := by
  set S := holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U with hS
  have hS0 : 0 ≤ S := aux_prop_growth_holder_assembly_seminorm_nonneg _ _ _
  have hsd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero]
    positivity
  · set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he
    have he0 : 0 < e := by
      rw [he, Real.sqrt_pos]
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra h
        push Not at h
        exact hxy (funext h)
      have hjpos : 0 < (x j - y j) ^ 2 := by
        have : x j - y j ≠ 0 := sub_ne_zero.mpr hj
        positivity
      exact lt_of_lt_of_le hjpos
        (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ j))
    have hea : 0 < e ^ alpha := Real.rpow_pos_of_pos he0 _
    have hratio : |U x - U y| / e ^ alpha ≤ S := by
      apply le_csSup hH
      exact ⟨x, hx, y, hy, hxy, rfl⟩
    have hele : e ≤ Real.sqrt d := aux_prop_growth_holder_assembly_euclid_le z hr hr1 hx hy
    have hpow : e ^ alpha ≤ 1 + Real.sqrt d :=
      (aux_prop_growth_holder_assembly_rpow_le he0.le ha0 ha1).trans (by linarith)
    calc |U x - U y| = |U x - U y| / e ^ alpha * e ^ alpha := by
          field_simp
      _ ≤ S * e ^ alpha := mul_le_mul_of_nonneg_right hratio hea.le
      _ ≤ S * (1 + Real.sqrt d) := mul_le_mul_of_nonneg_left hpow hS0
      _ = (1 + Real.sqrt d) * S := mul_comm _ _

/-- Supremum part of `cAlphaNorm`: a Hölder representative is bounded on the closed cube by
the cube average plus `(1 + √d)` times its seminorm. -/
theorem aux_prop_growth_holder_assembly_abs_le {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {U : SpatialCoordinates d → ℝ} (hU : Continuous U)
    (hH : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U)
    (u : DomainL2 (centeredCube z r hr))
    (hae : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    {x : SpatialCoordinates d} (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    |U x| ≤ |setAverage (centeredCube z r hr : Set (SpatialCoordinates d)) u| +
      (1 + Real.sqrt d) * holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  set B := (1 + Real.sqrt d) *
    holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U with hB
  set μ : Measure (SpatialCoordinates d) := volume.restrict Q with hμ
  have hvol : volume.real Q = r ^ d := centeredCube_volume_real z hr
  have hvolpos : 0 < volume.real Q := centeredCube_volume_pos z hr
  have hμuniv : μ.real univ = volume.real Q := by
    rw [hμ, measureReal_restrict_apply_univ]
  -- the average of `u` is the average of `U`
  have hint : ∫ y in Q, (u : SpatialCoordinates d → ℝ) y ∂μ = ∫ y, U y ∂μ := by
    rw [hμ, Measure.restrict_restrict (centeredCube z r hr).isOpen.measurableSet,
      Set.inter_self]
    exact integral_congr_ae hae
  have hUint : Integrable U μ := by
    have hK : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
      (closedCube z r hr).isCompact
    have hon : IntegrableOn U (closedCube z r hr : Set (SpatialCoordinates d)) volume :=
      hU.continuousOn.integrableOn_compact hK
    exact hon.mono_set (centeredCube_subset_closedCube z hr)
  have havg : setAverage Q u = (volume.real Q)⁻¹ * ∫ y, U y ∂μ := by
    unfold setAverage
    rw [hint]
  have hdiff : ∀ᵐ y ∂μ, ‖U x - U y‖ ≤ B := by
    rw [hμ]
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact aux_prop_growth_holder_assembly_increment z hr hr1 ha0 ha1 hH hx
      (centeredCube_subset_closedCube z hr hy)
  have hbound : ‖∫ y, (U x - U y) ∂μ‖ ≤ B * μ.real univ :=
    norm_integral_le_of_norm_le_const hdiff
  have hsplit : ∫ y, (U x - U y) ∂μ = U x * volume.real Q - ∫ y, U y ∂μ := by
    rw [integral_sub (integrable_const _) hUint, integral_const, hμuniv, smul_eq_mul, mul_comm]
  have hmain : |U x - setAverage Q u| ≤ B := by
    rw [havg]
    have heq : U x - (volume.real Q)⁻¹ * ∫ y, U y ∂μ =
        (volume.real Q)⁻¹ * ∫ y, (U x - U y) ∂μ := by
      rw [hsplit]
      field_simp
    rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hvolpos)]
    rw [Real.norm_eq_abs, hμuniv] at hbound
    calc (volume.real Q)⁻¹ * |∫ y, (U x - U y) ∂μ|
        ≤ (volume.real Q)⁻¹ * (B * volume.real Q) :=
          mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hvolpos.le)
      _ = B := by field_simp
  calc |U x| = |setAverage Q u + (U x - setAverage Q u)| := by ring_nf
    _ ≤ |setAverage Q u| + |U x - setAverage Q u| := abs_add_le _ _
    _ ≤ |setAverage Q u| + B := by linarith

/-- `1 + c (f + g)` keeps finite `L^p` moments, with an explicit numerical bound. -/
theorem aux_prop_growth_holder_assembly_moment {Sample : Type*} [MeasurableSpace Sample]
    (P : Measure Sample) [IsProbabilityMeasure P] {p : ℝ} (hp : 1 ≤ p)
    (f g : Sample → ℝ) {c Cf Cg : ℝ} (hc : 0 ≤ c)
    (hf : MemLp f (ENNReal.ofReal p) P) (hg : MemLp g (ENNReal.ofReal p) P)
    (hfB : eLpNorm f (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cf)
    (hgB : eLpNorm g (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cg) :
    MemLp (fun sample => 1 + c * (f sample + g sample)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun sample => 1 + c * (f sample + g sample)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (1 + c * (max Cf 0 + max Cg 0)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hfg : MemLp (fun sample => f sample + g sample) (ENNReal.ofReal p) P := hf.add hg
  have hcfg : MemLp (fun sample => c * (f sample + g sample)) (ENNReal.ofReal p) P := hfg.const_mul c
  have hone : MemLp (fun _ : Sample => (1 : ℝ)) (ENNReal.ofReal p) P := memLp_const 1
  refine ⟨hone.add hcfg, ?_⟩
  have hsum : eLpNorm (fun sample => f sample + g sample) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (max Cf 0 + max Cg 0) := by
    calc eLpNorm (fun sample => f sample + g sample) (ENNReal.ofReal p) P
        ≤ eLpNorm f (ENNReal.ofReal p) P + eLpNorm g (ENNReal.ofReal p) P :=
          eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (max Cf 0) + ENNReal.ofReal (max Cg 0) :=
          add_le_add (hfB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
            (hgB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      _ = ENNReal.ofReal (max Cf 0 + max Cg 0) :=
          (ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)).symm
  have hconst : eLpNorm (fun _ : Sample => (1 : ℝ)) (ENNReal.ofReal p) P ≤ ENNReal.ofReal 1 := by
    have h := eLpNorm_le_of_ae_bound (μ := P) (p := ENNReal.ofReal p)
      (f := fun _ : Sample => (1 : ℝ)) (C := 1) aestronglyMeasurable_const (Filter.Eventually.of_forall fun _ => by simp)
    simpa [measure_univ] using h
  have hmul : eLpNorm (fun sample => c * (f sample + g sample)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (c * (max Cf 0 + max Cg 0)) := by
    have heq : (fun sample => c * (f sample + g sample)) =
        c • (fun sample => f sample + g sample) := by
      funext sample; simp [smul_eq_mul]
    rw [heq, eLpNorm_const_smul]
    have hcn : ‖c‖ₑ = ENNReal.ofReal c := by
      rw [Real.enorm_eq_ofReal hc]
    rw [hcn, ENNReal.ofReal_mul hc]
    gcongr
  have hS0 : 0 ≤ c * (max Cf 0 + max Cg 0) :=
    mul_nonneg hc (add_nonneg (le_max_right _ _) (le_max_right _ _))
  calc eLpNorm (fun sample => 1 + c * (f sample + g sample)) (ENNReal.ofReal p) P
      ≤ eLpNorm (fun _ : Sample => (1 : ℝ)) (ENNReal.ofReal p) P +
          eLpNorm (fun sample => c * (f sample + g sample)) (ENNReal.ofReal p) P :=
        eLpNorm_add_le hp1
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (c * (max Cf 0 + max Cg 0)) := add_le_add hconst hmul
    _ = ENNReal.ofReal (1 + c * (max Cf 0 + max Cg 0)) :=
        (ENNReal.ofReal_add zero_le_one hS0).symm

/-- Child 1 : Campanato decay above the wavelength. -/
def aux_prop_growth_holder_assembly_MacroCampanato : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E) (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ r →
            ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1) ^ 2
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))

/-- Child 2 : Campanato decay below the wavelength. -/
def aux_prop_growth_holder_assembly_MicroCampanato : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E) (_X : in_extension d hd E)
    (_W : SmallPerturbationInput d) (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad →
            rad < (3 : ℝ) ^ (-(N : ℤ)) → rad ≤ r →
            ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1) ^ 2
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))

/-- Child 3 (the Dirichlet condition `u_N = φ` on `∂Q`): a continuous function
which agrees a.e. on the open cube with an element of the killed graph vanishes on the
boundary of the cube.  Deterministic. -/
def aux_prop_growth_holder_assembly_KilledTrace : Prop :=
  ∀ (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (w : SobolevData (centeredCube z r hr)),
    w ∈ killedSobolevGraph (centeredCube z r hr) →
    ∀ V : SpatialCoordinates d → ℝ, Continuous V →
      (w.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V →
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) → V x = 0

/-- A boundary point of the closed cube, in positive dimension. -/
theorem aux_prop_growth_holder_assembly_boundary_point {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ x0 : SpatialCoordinates d, x0 ∈ (closedCube z r hr : Set (SpatialCoordinates d)) ∧
      x0 ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have i0 : Fin d := ⟨0, by omega⟩
  refine ⟨Function.update z i0 (z i0 + r / 2), ?_, ?_⟩
  · change dist _ z ≤ r / 2
    refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
    by_cases hj : j = i0
    · subst hj
      simp [abs_of_pos hr]
    · simp [Function.update_of_ne hj, (half_pos hr).le]
  · change ¬ (dist _ z < r / 2)
    intro h
    have hc := (dist_le_pi_dist (Function.update z i0 (z i0 + r / 2)) z i0).trans_lt h
    simp [abs_of_pos hr] at hc

/-- The value of a `C²` function on the closed cube is bounded by its `c2Norm`. -/
theorem aux_prop_growth_holder_assembly_abs_le_c2Norm {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) {phi : SpatialCoordinates d → ℝ} (hphi : Continuous phi)
    {x : SpatialCoordinates d} (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    |phi x| ≤ c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi := by
  unfold c2Norm
  have hbdd : BddAbove {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = |phi x|} := by
    obtain ⟨B, hB⟩ := ((closedCube z r hr).isCompact.image
      (continuous_abs.comp hphi)).isBounded.bddAbove
    exact ⟨B, fun v ⟨y, hy, hv⟩ => hB ⟨y, hy, hv.symm⟩⟩
  have h1 : |phi x| ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = |phi x|} := le_csSup hbdd ⟨x, hx, rfl⟩
  have h2 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ phi x‖} := by
    apply Real.sSup_nonneg; rintro v ⟨y, -, rfl⟩; positivity
  have h3 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ (fderiv ℝ phi) x‖} := by
    apply Real.sSup_nonneg; rintro v ⟨y, -, rfl⟩; positivity
  linarith

/-- `c2Norm` is nonnegative. -/
theorem aux_prop_growth_holder_assembly_c2Norm_nonneg {d : ℕ} (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : 0 ≤ c2Norm S f := by
  unfold c2Norm
  refine add_nonneg (add_nonneg ?_ ?_) ?_ <;> apply Real.sSup_nonneg <;>
    rintro v ⟨x, -, rfl⟩ <;> positivity

/-- Whole-norm bound on one cube from the Campanato data and the boundary value. -/
theorem aux_prop_growth_holder_assembly_whole_norm {d : ℕ} (hd : 2 ≤ d)
    (Cp : CampanatoInput d) (htr : aux_prop_growth_holder_assembly_KilledTrace)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hbu : ((u : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr))) ∈
      killedSobolevGraph (centeredCube z r hr))
    {phi : SpatialCoordinates d → ℝ} (hphi : Continuous phi)
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    {Kc Kf Cphi : ℝ} (hKc : 0 ≤ Kc) (hKf : 0 ≤ Kf)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (hcamp : ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
      ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
          ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
            (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (u : SobolevData (centeredCube z r hr)).1) ^ 2
          ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        (Kc * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
          volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        (1 + (2 + Real.sqrt d) * Cp.C alpha * Kc) * (Kf + Cphi) := by
  have hCphi0 : 0 ≤ Cphi := (aux_prop_growth_holder_assembly_c2Norm_nonneg _ _).trans hCphi
  have hKK : 0 ≤ Kc * (Kf + Cphi) := mul_nonneg hKc (add_nonneg hKf hCphi0)
  have hCa : 0 < Cp.C alpha := Cp.C_pos alpha ha0 ha1
  obtain ⟨U, hUc, hUae, hUH, hUsem⟩ :=
    Cp.holder_of_campanato alpha ha0 ha1 z r hr hr1
      (u : SobolevData (centeredCube z r hr)).1 (Kc * (Kf + Cphi)) hKK hcamp
  refine ⟨U, hUc, hUae, hUH, ?_⟩
  set Sem := holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U with hSem
  -- boundary value `U = phi` on the boundary
  have hdiff_ae : (((u : SobolevData (centeredCube z r hr)) -
      (b : SobolevData (centeredCube z r hr))).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => U x - phi x := by
    have hsub := Lp.coeFn_sub (u : SobolevData (centeredCube z r hr)).1
      (b : SobolevData (centeredCube z r hr)).1
    filter_upwards [hsub, hUae, hb] with x h1 h2 h3
    rw [Prod.fst_sub, h1, Pi.sub_apply, h2, h3]
  obtain ⟨x0, hx0c, hx0o⟩ := aux_prop_growth_holder_assembly_boundary_point hd z hr
  have hbdry : U x0 - phi x0 = 0 :=
    htr d z r hr _ hbu (fun x => U x - phi x) (hUc.sub hphi) hdiff_ae x0 hx0c hx0o
  have hUx0 : |U x0| ≤ Cphi := by
    rw [show U x0 = phi x0 by linarith]
    exact (aux_prop_growth_holder_assembly_abs_le_c2Norm z hr hphi hx0c).trans hCphi
  -- supremum part
  have hsup : sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = |U x|} ≤ Cphi + (1 + Real.sqrt d) * Sem := by
    apply csSup_le
    · exact ⟨|U x0|, x0, hx0c, rfl⟩
    rintro v ⟨x, hx, rfl⟩
    have hinc := aux_prop_growth_holder_assembly_increment z hr hr1 ha0 ha1.le hUH hx hx0c
    calc |U x| = |U x0 + (U x - U x0)| := by ring_nf
      _ ≤ |U x0| + |U x - U x0| := abs_add_le _ _
      _ ≤ Cphi + (1 + Real.sqrt d) * Sem := add_le_add hUx0 hinc
  have hsd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hSem' : Sem ≤ Cp.C alpha * (Kc * (Kf + Cphi)) := hUsem
  unfold cAlphaNorm
  rw [← hSem]
  calc sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |U x|} + Sem
      ≤ Cphi + (1 + Real.sqrt d) * Sem + Sem := by linarith
    _ = Cphi + (2 + Real.sqrt d) * Sem := by ring
    _ ≤ Cphi + (2 + Real.sqrt d) * (Cp.C alpha * (Kc * (Kf + Cphi))) := by
        have h2 : 0 ≤ 2 + Real.sqrt d := by linarith
        linarith [mul_le_mul_of_nonneg_left hSem' h2]
    _ ≤ (1 + (2 + Real.sqrt d) * Cp.C alpha * Kc) * (Kf + Cphi) := by
        have heq : (1 + (2 + Real.sqrt d) * Cp.C alpha * Kc) * (Kf + Cphi) =
            (Kf + Cphi) + (2 + Real.sqrt d) * (Cp.C alpha * (Kc * (Kf + Cphi))) := by ring
        rw [heq]
        linarith

/-- The frozen Hölder assembly from its three typed children. -/
theorem aux_prop_growth_holder_assembly_of_children
    (hmac : aux_prop_growth_holder_assembly_MacroCampanato)
    (hmic : aux_prop_growth_holder_assembly_MicroCampanato)
    (htr : aux_prop_growth_holder_assembly_KilledTrace) :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  intro d hd _ _ E P X W Cp S t alpha k ps _ht _htd ha0 ha1 hps
  obtain ⟨delta1, hdelta1, hmac'⟩ := hmac d hd E P X S alpha k ps ha0 ha1 hps
  obtain ⟨delta2, hdelta2, hmic'⟩ := hmic d hd E P X W Cp S alpha k ps ha0 ha1 hps
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm Sreg It H hH hdelta z r hr hr1
  obtain ⟨Kmac, Cmac, hKmac0, hKmacL, hKmacB, hmacE⟩ :=
    hmac' M Rm Sreg It H hH (hdelta.trans (min_le_left _ _)) z r hr hr1
  obtain ⟨Kmic, Cmic, hKmic0, hKmicL, hKmicB, hmicE⟩ :=
    hmic' M Rm Sreg It H hH (hdelta.trans (min_le_right _ _)) z r hr hr1
  have hCa : 0 < Cp.C alpha := Cp.C_pos alpha ha0 ha1
  have hsd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (2 + Real.sqrt d) * Cp.C alpha := ⟨_, rfl⟩
  have hc : 0 ≤ c := by
    rw [hcdef]; exact mul_nonneg (by positivity) hCa.le
  refine ⟨fun N om => 1 + c * (Kmac N om + Kmic N om),
    fun i => 1 + c * (max (Cmac i) 0 + max (Cmic i) 0), ?_, ?_, ?_, ?_⟩
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Kmac N) (Kmic N) hc
      (hKmacL i N) (hKmicL i N) (hKmacB i N) (hKmicB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Kmac N) (Kmic N) hc
      (hKmacL i N) (hKmicL i N) (hKmacB i N) (hKmicB i N)).2
  · refine Filter.Eventually.of_forall fun om N => ?_
    show 1 ≤ 1 + c * (Kmac N om + Kmic N om)
    have := mul_nonneg hc (add_nonneg (hKmac0 N om) (hKmic0 N om))
    linarith
  · filter_upwards [hmacE, hmicE] with om hom1 hom2
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have hCphi0 : 0 ≤ Cphi :=
      (aux_prop_growth_holder_assembly_c2Norm_nonneg _ _).trans hCphi
    have hKfC : 0 ≤ Kf + Cphi := add_nonneg hKf hCphi0
    have hKc : 0 ≤ Kmac N om + Kmic N om := add_nonneg (hKmac0 N om) (hKmic0 N om)
    have hcamp : ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
        ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
            ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
              (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
              (u : SobolevData (centeredCube z r hr)).1) ^ 2
            ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
          ((Kmac N om + Kmic N om) * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
            volume.real (Metric.ball x rad ∩
              (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      intro x hx rad hrad hradr
      by_cases hN : (3 : ℝ) ^ (-(N : ℤ)) ≤ rad
      · have h1 := hom1 N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x hx rad hN hradr
        have hsq : (Kmac N om * (Kf + Cphi)) ^ 2 ≤ ((Kmac N om + Kmic N om) * (Kf + Cphi)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (hKmac0 N om) hKfC)
            (mul_le_mul_of_nonneg_right (by linarith [hKmic0 N om]) hKfC) 2
        calc _ ≤ (Kmac N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
              volume.real (Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d))) := h1
          _ ≤ _ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hrad.le _)) measureReal_nonneg
      · have hN' : rad < (3 : ℝ) ^ (-(N : ℤ)) := lt_of_not_ge hN
        have h2 := hom2 N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x hx rad hrad
          hN' hradr
        have hsq : (Kmic N om * (Kf + Cphi)) ^ 2 ≤ ((Kmac N om + Kmic N om) * (Kf + Cphi)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (hKmic0 N om) hKfC)
            (mul_le_mul_of_nonneg_right (by linarith [hKmac0 N om]) hKfC) 2
        calc _ ≤ (Kmic N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
              volume.real (Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d))) := h2
          _ ≤ _ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hrad.le _)) measureReal_nonneg
    obtain ⟨U, hUc, hUae, hUH, hUn⟩ :=
      aux_prop_growth_holder_assembly_whole_norm hd Cp htr z hr hr1 ha0 ha1 b u hsolve.1
        (hphi.continuous) hb hKc hKf hCphi hcamp
    refine ⟨U, hUc, hUae, hUH, hUn.trans (le_of_eq ?_)⟩
    simp only [hcdef]

/-- Source restoration of the Holder half of mfd:prop-growth.
- in_J/in_poincare/in_extension/in_responses/in_6_16/in_iteration are the
  original coefficient and published regularity inputs.
- The coefficient is exactly cutoffPositiveCoefficient M H om N z hr.
- SmallPerturbationInput and CampanatoInput remain the published inputs;
  local logarithmic oscillation is derived from the model and infrared control,
  not postulated for an arbitrary PositiveCoefficient.
- The growth majorant K is constructed, has all prescribed moments, and
  is at least one on a common event before every cutoff/source/datum.
- Continuous representative, actual Holder membership and the complete
  cAlphaNorm bound (including the supremum) are all conclusions.
- prop_growth_macro_energy, rem_resolved_microscopic and
  prop_growth_common_moment_bank are proof suppliers. The former generic
  energy-only assembly did not contain the macro oscillation information.
- lem_extremes is a proof supplier: it produces the coefficient envelope `D, mlow, mhigh`
  on `closedCube z r hr` with the log-Lipschitz constant `D N om * 3^N` and
  the moment bounds `Cp*sqrt(1+N)` / `Cp*exp((Cd*delta + Cp*delta^2)*N)`,
  which is exactly the `DN, mN, MN` input that `rem_resolved_microscopic`
  consumes.  It is a supplier, not a carried conclusion: nothing of the
  Holder conclusion below is assumed through it.
- p1,t1 are chosen inside the proof; p1>d follows from
  0<alpha<1-d/p1. Their exclusion of p1≤d was correct, not a contradiction.
No conclusion is carried as an input. The proof combines the macro and microscopic
Campanato children with the deterministic boundary trace child. -/
theorem prop_growth_holder_assembly :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  exact aux_prop_growth_holder_assembly_of_children prop_growth_holder_macro_campanato
    prop_growth_holder_micro_campanato killed_continuous_boundary_zero

end SubdiffusiveProcess.Paper
