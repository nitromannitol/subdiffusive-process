module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.coefficient_physical_identity
public import SubdiffusiveProcess.Paper.astar_removing_H
public import SubdiffusiveProcess.Paper.cells_above_wavelength
public import SubdiffusiveProcess.Paper.cell_maximum_moment
public import SubdiffusiveProcess.Paper.weighted_cell_summation
public import SubdiffusiveProcess.Paper.lambda_inv_cell_moment
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import SubdiffusiveProcess.Probability.GeometricSeriesLp
public import SubdiffusiveProcess.Main.InfraredAdmissible


@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lambda_inv_moments_Y_nonneg {d : ℕ} (k : ℤ)
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    0 ≤ Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (Homogenization.originCube d 0) k a := by
  unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
  exact Homogenization.Book.Ch02.finsetSupReal_nonneg _ _
    (fun R _ => Homogenization.Book.Ch02.matrixNorm_nonneg _)

theorem aux_lambda_inv_moments_tail_exponent (a X n : ℝ) (hn : 0 ≤ n) (h : a ≤ -X) :
    a * n + (n + 1) * X ≤ X := by
  nlinarith [mul_le_mul_of_nonneg_right h hn]

theorem aux_lambda_inv_moments_condA_helper (K Z t : ℝ) (hK : 0 ≤ K) (_hZ : 0 ≤ Z)
    (ht0 : 0 ≤ t) (ht : t ≤ Z / (4 * K + 4)) : K * t ≤ Z / 4 := by
  have hden : 0 < 4 * K + 4 := by linarith
  rw [le_div_iff₀ hden] at ht
  nlinarith

theorem aux_lambda_inv_moments_condB_helper (K Z t : ℝ) (hK : 0 ≤ K) (_hZ : 0 ≤ Z)
    (ht1 : t ≤ 1) (ht0 : 0 ≤ t) (ht2 : t ≤ Z / (2 * K + 1)) : K * t * (1 + t) ≤ Z := by
  have hden : 0 < 2 * K + 1 := by linarith
  rw [le_div_iff₀ hden] at ht2
  nlinarith [mul_nonneg hK ht0]

theorem aux_lambda_inv_moments_ratio_pos (s : ℝ) :
    0 < (3 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _

theorem aux_lambda_inv_moments_ratio_lt_one (s : ℝ) (hs0 : 0 < s) :
    (3 : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem aux_lambda_inv_moments_discount_eq (s : ℝ) :
    Homogenization.Book.Ch02.geometricDiscount s 1 = 1 - (3 : ℝ) ^ (-s) := by
  unfold Homogenization.Book.Ch02.geometricDiscount
  norm_num

theorem aux_lambda_inv_moments_weight_eq (s : ℝ) (n : ℕ) :
    Homogenization.Book.Ch02.geometricWeight s 1 n =
      Homogenization.Book.Ch02.geometricDiscount s 1 * ((3 : ℝ) ^ (-s)) ^ n := by
  show Homogenization.Book.Ch02.geometricDiscount s 1 * (3 : ℝ) ^ (-s * 1 * (n : ℝ)) =
      Homogenization.Book.Ch02.geometricDiscount s 1 * ((3 : ℝ) ^ (-s)) ^ n
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s)) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 2
  ring

theorem aux_lambda_inv_moments_weight_sum (s : ℝ) (hs0 : 0 < s) :
    (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n) = 1 ∧
      Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s 1 n) ∧
      (∀ n, 0 ≤ Homogenization.Book.Ch02.geometricWeight s 1 n) := by
  have hρ0 := aux_lambda_inv_moments_ratio_pos s
  have hρ1 := aux_lambda_inv_moments_ratio_lt_one s hs0
  have heq : ∀ n, Homogenization.Book.Ch02.geometricWeight s 1 n =
      Homogenization.Book.Ch02.geometricDiscount s 1 * ((3 : ℝ) ^ (-s)) ^ n :=
    aux_lambda_inv_moments_weight_eq s
  have hdisc : Homogenization.Book.Ch02.geometricDiscount s 1 = 1 - (3 : ℝ) ^ (-s) :=
    aux_lambda_inv_moments_discount_eq s
  have hsumm : Summable (fun n : ℕ => ((3 : ℝ) ^ (-s)) ^ n) :=
    summable_geometric_of_lt_one hρ0.le hρ1
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [heq]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1, hdisc]
    have hne : (1 : ℝ) - (3 : ℝ) ^ (-s) ≠ 0 := by linarith
    field_simp
  · simp_rw [heq]; exact hsumm.mul_left _
  · intro n
    rw [heq n, hdisc]
    exact mul_nonneg (by linarith) (pow_nonneg hρ0.le n)

theorem aux_lambda_inv_moments_lam_inv_eq {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ Ssum : ℝ, 0 ≤ Ssum ∧
      Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s 1 n *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ)) (E.chart z r hr a z r)) (1 / 2)) ∧
      Ssum = ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ)) (E.chart z r hr a z r)) (1 / 2) ∧
      (E.lam z r hr a z r s 1)⁻¹ = Ssum ^ 2 := by
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := le_refl _
  have hsIoc : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have heq := E.lam_eq z r hr a z r hr hsub s hsIoc 1 (le_refl (1 : ℝ≥0∞))
  rw [ite_eq_right ENNReal.one_ne_top, ENNReal.toReal_one,
      Homogenization.Book.Ch02.lambdaSq_finite] at heq
  unfold Homogenization.Book.Ch02.lambdaSqFinite at heq
  have hscale0 : ∀ n : ℕ, (Homogenization.originCube d 0).scale - (n : ℤ) = -(n : ℤ) := by
    intro n
    show (0 : ℤ) - (n : ℤ) = -(n : ℤ)
    ring
  simp_rw [hscale0] at heq
  set Ssum0 : ℝ := ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n *
      Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ)) (E.chart z r hr a z r)) (1 / 2) with hSsum0_def
  have hYnn : ∀ n : ℕ, 0 ≤ Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (Homogenization.originCube d 0) (-(n : ℤ)) (E.chart z r hr a z r) :=
    fun n => aux_lambda_inv_moments_Y_nonneg (-(n : ℤ)) _
  have hlam_eq : E.lam z r hr a z r s 1 = Ssum0 ^ (-(2 / 1) : ℝ) := heq
  have hSsum0_nonneg : 0 ≤ Ssum0 := by
    rw [hSsum0_def]
    apply tsum_nonneg
    intro n
    have hw : 0 ≤ Homogenization.Book.Ch02.geometricWeight s 1 n :=
      (aux_lambda_inv_moments_weight_sum s hs0).2.2 n
    exact mul_nonneg hw (Real.rpow_nonneg (hYnn n) _)
  have hlam_pos : 0 < E.lam z r hr a z r s 1 := E.lam_pos _ _ _ _ _ _ _ _
  have hSsum0_ne : Ssum0 ≠ 0 := by
    intro h0
    rw [hlam_eq, h0] at hlam_pos
    norm_num at hlam_pos
  have hSsum0_pos : 0 < Ssum0 := lt_of_le_of_ne hSsum0_nonneg (Ne.symm hSsum0_ne)
  have hsummable : Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s 1 n *
      Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ)) (E.chart z r hr a z r)) (1 / 2)) := by
    by_contra hns
    exact hSsum0_ne (hSsum0_def ▸ tsum_eq_zero_of_not_summable hns)
  refine ⟨Ssum0, hSsum0_nonneg, hsummable, hSsum0_def, ?_⟩
  have hstep : Ssum0 ^ (-(2 / 1) : ℝ) = (Ssum0 ^ (2 : ℝ))⁻¹ := by
    rw [show (-(2 / 1) : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hSsum0_nonneg]
  have hstep2 : Ssum0 ^ (2 : ℝ) = Ssum0 ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hlam_eq, hstep, hstep2, inv_inv]

theorem aux_lambda_inv_moments_Ssum_meas {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : ℝ) (Y : ℕ → Ω → ℝ) (hYmeas : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hsqrt_summable : ∀ om : Ω, Summable (fun n : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2))) :
    AEStronglyMeasurable (fun om => ∑' n : ℕ,
      Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2)) μ := by
  have hterm_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun om => Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2)) μ :=
    fun n => (((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/2)).comp_aestronglyMeasurable
      (hYmeas n))).const_mul _
  have hsum_fn_eq : ∀ M' : ℕ,
      (∑ n ∈ Finset.range M', fun om =>
        Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2)) =
        (fun om => ∑ n ∈ Finset.range M',
          Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2)) := by
    intro M'; funext om; rw [Finset.sum_apply]
  have hpart_meas : ∀ M' : ℕ, AEStronglyMeasurable
      (fun om => ∑ n ∈ Finset.range M',
        Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2)) μ := by
    intro M'
    rw [← hsum_fn_eq]
    exact Finset.aestronglyMeasurable_sum (Finset.range M') (fun n _ => hterm_meas n)
  have htendsto : ∀ om : Ω, Filter.Tendsto
      (fun M' => ∑ n ∈ Finset.range M',
        Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2))
      Filter.atTop (nhds (∑' n : ℕ,
        Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2))) :=
    fun om => (hsqrt_summable om).hasSum.tendsto_sum_nat
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hpart_meas
    (Filter.Eventually.of_forall htendsto)

theorem aux_lambda_inv_moments_cs {s : ℝ} (hs0 : 0 < s) (H0 : ℕ)
    (Y : ℕ → ℝ) (hY : ∀ n, 0 ≤ Y n)
    (hsqrt_summable : Summable (fun n : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n) (1 / 2)))
    (htail_summable : Summable (fun n : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s 1 (n + H0) * Y (n + H0))) :
    (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n) (1 / 2)) ^ 2 ≤
      (∑ n ∈ Finset.range H0, Homogenization.Book.Ch02.geometricWeight s 1 n * Y n) +
        ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 (n + H0) * Y (n + H0) := by
  obtain ⟨hwsum1, hwsummable, hwnn⟩ := aux_lambda_inv_moments_weight_sum s hs0
  set w : ℕ → ℝ := Homogenization.Book.Ch02.geometricWeight s 1 with hw_def
  set RHS : ℝ := (∑ n ∈ Finset.range H0, w n * Y n) + ∑' n : ℕ, w (n + H0) * Y (n + H0) with hRHS_def
  have hfg : ∀ n : ℕ, Real.sqrt (w n) * Real.sqrt (w n * Y n) =
      w n * Real.rpow (Y n) (1 / 2) := by
    intro n
    rw [Real.sqrt_mul (hwnn n), ← mul_assoc, Real.mul_self_sqrt (hwnn n), Real.sqrt_eq_rpow]
    rfl
  have hbound : ∀ M : ℕ, H0 ≤ M →
      (∑ n ∈ Finset.range M, w n * Real.rpow (Y n) (1 / 2)) ^ 2 ≤ RHS := by
    intro M hM
    obtain ⟨K, hK⟩ := Nat.le.dest hM
    have hsplit : (∑ n ∈ Finset.range M, w n * Y n) =
        (∑ n ∈ Finset.range H0, w n * Y n) + ∑ n ∈ Finset.range K, w (H0 + n) * Y (H0 + n) := by
      rw [← hK]
      exact Finset.sum_range_add (fun n => w n * Y n) H0 K
    have hcs : (∑ n ∈ Finset.range M, w n * Real.rpow (Y n) (1 / 2)) ^ 2 ≤
        (∑ n ∈ Finset.range M, w n) * (∑ n ∈ Finset.range M, w n * Y n) := by
      calc (∑ n ∈ Finset.range M, w n * Real.rpow (Y n) (1 / 2)) ^ 2
          = (∑ n ∈ Finset.range M, Real.sqrt (w n) * Real.sqrt (w n * Y n)) ^ 2 := by
            simp_rw [← hfg]
        _ ≤ (∑ n ∈ Finset.range M, (Real.sqrt (w n)) ^ 2) *
              (∑ n ∈ Finset.range M, (Real.sqrt (w n * Y n)) ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = (∑ n ∈ Finset.range M, w n) * (∑ n ∈ Finset.range M, w n * Y n) := by
            congr 1
            · apply Finset.sum_congr rfl; intro n _; exact Real.sq_sqrt (hwnn n)
            · apply Finset.sum_congr rfl; intro n _
              exact Real.sq_sqrt (mul_nonneg (hwnn n) (hY n))
    have hwM1 : (∑ n ∈ Finset.range M, w n) ≤ 1 := by
      rw [← hwsum1]; exact hwsummable.sum_le_tsum _ (fun n _ => hwnn n)
    have hsum_nonneg : 0 ≤ ∑ n ∈ Finset.range M, w n * Y n :=
      Finset.sum_nonneg (fun n _ => mul_nonneg (hwnn n) (hY n))
    have hstep1 : (∑ n ∈ Finset.range M, w n) * (∑ n ∈ Finset.range M, w n * Y n) ≤
        ∑ n ∈ Finset.range M, w n * Y n := by
      calc (∑ n ∈ Finset.range M, w n) * (∑ n ∈ Finset.range M, w n * Y n)
          ≤ 1 * (∑ n ∈ Finset.range M, w n * Y n) :=
            mul_le_mul_of_nonneg_right hwM1 hsum_nonneg
        _ = ∑ n ∈ Finset.range M, w n * Y n := one_mul _
    have htailK : (∑ n ∈ Finset.range K, w (H0 + n) * Y (H0 + n)) ≤
        ∑' n : ℕ, w (n + H0) * Y (n + H0) := by
      have hcomm : (fun n : ℕ => w (H0 + n) * Y (H0 + n)) = fun n => w (n + H0) * Y (n + H0) := by
        funext n; rw [add_comm H0 n]
      rw [hcomm]
      exact htail_summable.sum_le_tsum _ (fun n _ => mul_nonneg (hwnn _) (hY _))
    calc (∑ n ∈ Finset.range M, w n * Real.rpow (Y n) (1 / 2)) ^ 2
        ≤ (∑ n ∈ Finset.range M, w n) * (∑ n ∈ Finset.range M, w n * Y n) := hcs
      _ ≤ ∑ n ∈ Finset.range M, w n * Y n := hstep1
      _ = (∑ n ∈ Finset.range H0, w n * Y n) + ∑ n ∈ Finset.range K, w (H0 + n) * Y (H0 + n) :=
          hsplit
      _ ≤ (∑ n ∈ Finset.range H0, w n * Y n) + ∑' n : ℕ, w (n + H0) * Y (n + H0) := by
          gcongr
      _ = RHS := hRHS_def.symm
  have htendsto : Filter.Tendsto (fun M => ∑ n ∈ Finset.range M, w n * Real.rpow (Y n) (1 / 2))
      Filter.atTop (nhds (∑' n : ℕ, w n * Real.rpow (Y n) (1 / 2))) :=
    hsqrt_summable.hasSum.tendsto_sum_nat
  have htendsto2 : Filter.Tendsto
      (fun M => (∑ n ∈ Finset.range M, w n * Real.rpow (Y n) (1 / 2)) ^ 2)
      Filter.atTop (nhds ((∑' n : ℕ, w n * Real.rpow (Y n) (1 / 2)) ^ 2)) :=
    htendsto.pow 2
  have hev : ∀ᶠ M in Filter.atTop,
      (∑ n ∈ Finset.range M, w n * Real.rpow (Y n) (1 / 2)) ^ 2 ≤ RHS := by
    filter_upwards [Filter.eventually_ge_atTop H0] with M hM
    exact hbound M hM
  exact le_of_tendsto htendsto2 hev

theorem aux_lambda_inv_moments_series_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s D Q Cd Cq dl : ℝ) (N : ℕ)
    (hs0 : 0 < s) (_hDnn : 0 ≤ D) (hDQ : 2 * D ≤ s * Q) (hQ1 : 1 ≤ Q)
    (hCdpos : 0 < Cd) (hCqpos : 0 < Cq) (_hdlnn : 0 ≤ dl)
    (hcondA : Cd * (Q + Q ^ 2) * dl ^ 2 ≤ (s / 4) * Real.log 3)
    (hcondB : Cd * dl * (1 + dl) ≤ s * Real.log 3)
    (Y : ℕ → Ω → ℝ) (hYnn : ∀ n om, 0 ≤ Y n om)
    (hYmeas : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hYbound : ∀ n : ℕ, eLpNorm (Y n) (ENNReal.ofReal Q) μ ≤ ENNReal.ofReal
        (Cq * (if n ≤ N then (3 : ℝ) ^ (D * (n : ℝ) / Q) *
              Real.exp (Cd * (Q + Q ^ 2) * dl ^ 2 * (n : ℝ))
             else Real.exp ((Cd * dl + Cd * dl ^ 2) * (N : ℝ))))) :
    MemLp (fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n * Y n om)
        (ENNReal.ofReal Q) μ ∧
      eLpNorm (fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n * Y n om)
        (ENNReal.ofReal Q) μ ≤ ENNReal.ofReal
        ((1 - (3 : ℝ) ^ (-s)) * Cq / (1 - Real.exp (-(s / 2) * Real.log 3 + Cd * (Q + Q ^ 2) * dl ^ 2)) +
          (1 - (3 : ℝ) ^ (-s)) * Cq * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s))) ∧
      (∀ᵐ om ∂μ, Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s 1 n * Y n om)) := by
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ1
  obtain ⟨hwsum1, hwsummable, hwnn⟩ := aux_lambda_inv_moments_weight_sum s hs0
  set w : ℕ → ℝ := Homogenization.Book.Ch02.geometricWeight s 1 with hw_def
  have hρ0pos := aux_lambda_inv_moments_ratio_pos s
  have hρ0lt1 := aux_lambda_inv_moments_ratio_lt_one s hs0
  have hw_eq : ∀ n : ℕ, w n =
      Homogenization.Book.Ch02.geometricDiscount s 1 * ((3 : ℝ) ^ (-s)) ^ n :=
    aux_lambda_inv_moments_weight_eq s
  set c1 : ℝ := Homogenization.Book.Ch02.geometricDiscount s 1 with hc1_def
  have hc1eq : c1 = 1 - (3 : ℝ) ^ (-s) := aux_lambda_inv_moments_discount_eq s
  have hc1pos : 0 < c1 := by rw [hc1eq]; linarith
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrpow3 : ∀ y : ℝ, (3 : ℝ) ^ y = Real.exp (Real.log 3 * y) := fun y =>
    Real.rpow_def_of_pos (by norm_num) y
  set K : ℝ := Cd * (Q + Q ^ 2) * dl ^ 2 with hK_def
  have hKnn : 0 ≤ K := by
    rw [hK_def]; positivity
  set L : ℝ := (-(s / 2)) * Real.log 3 + K with hL_def
  set ρ : ℝ := Real.exp L with hρ_def
  have hρpos : 0 < ρ := Real.exp_pos _
  have hLneg : L < 0 := by
    have : K ≤ (s / 4) * Real.log 3 := hcondA
    rw [hL_def]
    nlinarith [hlog3pos, hs0]
  have hρlt1 : ρ < 1 := by
    rw [hρ_def, show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr hLneg
  -- head term bound: for every n, w n * (3^{D n / Q} * exp (K n)) ≤ c1 * ρ ^ n
  have hhead_term : ∀ n : ℕ,
      w n * ((3 : ℝ) ^ (D * (n : ℝ) / Q) * Real.exp (K * (n : ℝ))) ≤ c1 * ρ ^ n := by
    intro n
    have hA : Real.exp ((n : ℝ) * ((-s) * Real.log 3)) = ((3 : ℝ) ^ (-s)) ^ n := by
      rw [hrpow3 (-s), ← Real.exp_nat_mul]
      congr 1
      ring
    have hB : Real.exp ((n : ℝ) * (Real.log 3 * (D / Q))) = (3 : ℝ) ^ (D * (n : ℝ) / Q) := by
      rw [hrpow3 (D * (n : ℝ) / Q)]
      congr 1
      ring
    have hexpand : (n : ℝ) * ((-s) * Real.log 3 + Real.log 3 * (D / Q) + K) =
        (n : ℝ) * ((-s) * Real.log 3) + ((n : ℝ) * (Real.log 3 * (D / Q)) + K * (n : ℝ)) := by
      ring
    have hstep1 : w n * ((3 : ℝ) ^ (D * (n : ℝ) / Q) * Real.exp (K * (n : ℝ))) =
        c1 * Real.exp ((n : ℝ) * ((-s) * Real.log 3 + Real.log 3 * (D / Q) + K)) := by
      rw [hexpand, Real.exp_add, Real.exp_add, hA, hB, hw_eq n]
      ring
    rw [hstep1]
    have hexp_mono : ((n : ℝ) * ((-s) * Real.log 3 + Real.log 3 * (D / Q) + K)) ≤ (n : ℝ) * L := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      rw [hL_def]
      have hDQ' : D / Q ≤ s / 2 := by
        rw [div_le_iff₀ hQpos]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hDQ' hlog3pos.le]
    have : Real.exp ((n : ℝ) * ((-s) * Real.log 3 + Real.log 3 * (D / Q) + K)) ≤
        Real.exp ((n : ℝ) * L) := Real.exp_le_exp.mpr hexp_mono
    calc c1 * Real.exp ((n : ℝ) * ((-s) * Real.log 3 + Real.log 3 * (D / Q) + K))
        ≤ c1 * Real.exp ((n : ℝ) * L) := by
          exact mul_le_mul_of_nonneg_left this hc1pos.le
      _ = c1 * ρ ^ n := by
          rw [hρ_def, ← Real.exp_nat_mul]
  have hQnetop : ENNReal.ofReal Q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hterm_meas : ∀ n : ℕ, AEStronglyMeasurable (fun om => w n * Y n om) μ :=
    fun n => (hYmeas n).const_mul (w n)
  have hterm_bound_head : ∀ n : ℕ, n ≤ N →
      eLpNorm (fun om => w n * Y n om) (ENNReal.ofReal Q) μ ≤ ENNReal.ofReal (c1 * Cq * ρ ^ n) := by
    intro n hnN
    have h1 : (fun om => w n * Y n om) = w n • Y n := by funext om; simp [smul_eq_mul]
    rw [h1, eLpNorm_const_smul, Real.enorm_eq_ofReal (hwnn n)]
    have h2 := hYbound n
    rw [ite_eq_left hnN] at h2
    calc ENNReal.ofReal (w n) * eLpNorm (Y n) (ENNReal.ofReal Q) μ
        ≤ ENNReal.ofReal (w n) *
            ENNReal.ofReal (Cq * ((3 : ℝ) ^ (D * (n : ℝ) / Q) * Real.exp (K * (n : ℝ)))) := by
          gcongr
      _ = ENNReal.ofReal (w n * (Cq * ((3 : ℝ) ^ (D * (n : ℝ) / Q) * Real.exp (K * (n : ℝ))))) := by
          rw [ENNReal.ofReal_mul (hwnn n)]
      _ ≤ ENNReal.ofReal (c1 * Cq * ρ ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have := hhead_term n
          nlinarith [mul_le_mul_of_nonneg_left this hCqpos.le]
  have hsum_fn_eq : (∑ n ∈ Finset.range (N + 1), fun om => w n * Y n om) =
      (fun om => ∑ n ∈ Finset.range (N + 1), w n * Y n om) := by
    funext om
    rw [Finset.sum_apply]
  have hhead_meas : AEStronglyMeasurable
      (fun om => ∑ n ∈ Finset.range (N + 1), w n * Y n om) μ := by
    rw [← hsum_fn_eq]
    exact Finset.aestronglyMeasurable_sum (Finset.range (N + 1)) (fun n _ => hterm_meas n)
  have hhead_eLpNorm : eLpNorm (fun om => ∑ n ∈ Finset.range (N + 1), w n * Y n om)
      (ENNReal.ofReal Q) μ ≤ ENNReal.ofReal (c1 * Cq / (1 - ρ)) := by
    have hsum_le : eLpNorm (fun om => ∑ n ∈ Finset.range (N + 1), w n * Y n om)
        (ENNReal.ofReal Q) μ ≤
        ∑ n ∈ Finset.range (N + 1), eLpNorm (fun om => w n * Y n om) (ENNReal.ofReal Q) μ := by
      have h := eLpNorm_sum_le (p := ENNReal.ofReal Q) (μ := μ) (s := Finset.range (N + 1))
        (f := fun n om => w n * Y n om)
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
      rw [hsum_fn_eq] at h
      exact h
    have hsum_bound : (∑ n ∈ Finset.range (N + 1),
        eLpNorm (fun om => w n * Y n om) (ENNReal.ofReal Q) μ) ≤
        ENNReal.ofReal (∑ n ∈ Finset.range (N + 1), c1 * Cq * ρ ^ n) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
      exact Finset.sum_le_sum (fun n hn =>
        hterm_bound_head n (Finset.mem_range_succ_iff.mp hn))
    have hρsummable : Summable (fun n : ℕ => ρ ^ n) := summable_geometric_of_lt_one hρpos.le hρlt1
    have hgeom_le : (∑ n ∈ Finset.range (N + 1), c1 * Cq * ρ ^ n) ≤ c1 * Cq / (1 - ρ) := by
      rw [← Finset.mul_sum]
      have : (∑ n ∈ Finset.range (N + 1), ρ ^ n) ≤ (1 - ρ)⁻¹ := by
        rw [← tsum_geometric_of_lt_one hρpos.le hρlt1]
        exact hρsummable.sum_le_tsum _ (fun n _ => pow_nonneg hρpos.le n)
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc eLpNorm (fun om => ∑ n ∈ Finset.range (N + 1), w n * Y n om) (ENNReal.ofReal Q) μ
        ≤ ∑ n ∈ Finset.range (N + 1), eLpNorm (fun om => w n * Y n om) (ENNReal.ofReal Q) μ :=
          hsum_le
      _ ≤ ENNReal.ofReal (∑ n ∈ Finset.range (N + 1), c1 * Cq * ρ ^ n) := hsum_bound
      _ ≤ ENNReal.ofReal (c1 * Cq / (1 - ρ)) := ENNReal.ofReal_le_ofReal hgeom_le
  -- TAIL: n > N, via memLp_geometric_tsum_tails
  set r' : ℝ := (3 : ℝ) ^ (-s) with hr'_def
  have hr'nn : 0 ≤ r' := hρ0pos.le
  have hr'lt1 : r' < 1 := hρ0lt1
  set α : ℝ := Cd * dl + Cd * dl ^ 2 with hα_def
  have hcondB' : α ≤ s * Real.log 3 := by
    have heq : Cd * dl * (1 + dl) = α := by rw [hα_def]; ring
    linarith [heq ▸ hcondB]
  set F' : ℕ → Ω → ℝ := fun n om => w (n + N + 1) * Y (n + N + 1) om with hF'_def
  have hF'_meas : ∀ n : ℕ, AEStronglyMeasurable (F' n) μ :=
    fun n => (hYmeas (n + N + 1)).const_mul _
  set B : ℝ := c1 * Cq * Real.exp (α * (N : ℝ)) * r' ^ (N + 1) with hB_def
  have hBnn : 0 ≤ B := by
    show 0 ≤ c1 * Cq * Real.exp (α * (N : ℝ)) * r' ^ (N + 1)
    exact mul_nonneg (mul_nonneg (mul_nonneg hc1pos.le hCqpos.le) (Real.exp_pos _).le)
      (pow_nonneg hr'nn _)
  have hF'_bound : ∀ n : ℕ, eLpNorm (F' n) (ENNReal.ofReal Q) μ ≤ ENNReal.ofReal (B * r' ^ n) := by
    intro n
    have hnotle : ¬ (n + N + 1 ≤ N) := by omega
    have h2 := hYbound (n + N + 1)
    rw [ite_eq_right hnotle] at h2
    have h1 : F' n = w (n + N + 1) • Y (n + N + 1) := by
      funext om; rw [hF'_def]; simp [smul_eq_mul]
    rw [h1, eLpNorm_const_smul, Real.enorm_eq_ofReal (hwnn (n + N + 1))]
    calc ENNReal.ofReal (w (n + N + 1)) * eLpNorm (Y (n + N + 1)) (ENNReal.ofReal Q) μ
        ≤ ENNReal.ofReal (w (n + N + 1)) *
            ENNReal.ofReal (Cq * Real.exp ((Cd * dl + Cd * dl ^ 2) * (N : ℝ))) := by
          gcongr
      _ = ENNReal.ofReal (w (n + N + 1) * (Cq * Real.exp (α * (N : ℝ)))) := by
          rw [ENNReal.ofReal_mul (hwnn _), hα_def]
      _ = ENNReal.ofReal (B * r' ^ n) := by
          congr 1
          rw [hw_eq (n + N + 1), hB_def, hr'_def]
          rw [show n + N + 1 = (N + 1) + n by ring, pow_add]
          ring
  have hF'_MemLp : ∀ n : ℕ, MemLp (F' n) (ENNReal.ofReal Q) μ :=
    fun n => lt_of_le_of_lt (hF'_bound n) ENNReal.ofReal_lt_top
  have hQ1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hQ1
  have htail := SubdiffusiveProcess.memLp_geometric_tsum_tails μ hQ1e hQnetop F' hF'_MemLp
    hBnn hr'nn hr'lt1 hF'_bound
  obtain ⟨htailAE, htailH⟩ := htail
  obtain ⟨htailMemLp0, htailBound0⟩ := htailH 0
  have hNcast : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hexp_le : Real.exp (α * (N : ℝ)) * r' ^ (N + 1) ≤ r' := by
    have hstep : r' ^ (N + 1) = Real.exp (((N : ℝ) + 1) * (Real.log 3 * (-s))) := by
      rw [hr'_def, hrpow3, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hr'eq : r' = Real.exp (Real.log 3 * (-s)) := by rw [hr'_def, hrpow3]
    rw [hstep, hr'eq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hXeq : Real.log 3 * (-s) = -(s * Real.log 3) := by ring
    rw [hXeq]
    exact aux_lambda_inv_moments_tail_exponent α (-(s * Real.log 3)) (N : ℝ) hNcast
      (by linarith [hcondB'])
  have hB_le' : B ≤ c1 * Cq * r' := by
    show c1 * Cq * Real.exp (α * (N : ℝ)) * r' ^ (N + 1) ≤ c1 * Cq * r'
    have hcCqnn : 0 ≤ c1 * Cq := mul_nonneg hc1pos.le hCqpos.le
    calc c1 * Cq * Real.exp (α * (N : ℝ)) * r' ^ (N + 1)
        = c1 * Cq * (Real.exp (α * (N : ℝ)) * r' ^ (N + 1)) := by ring
      _ ≤ c1 * Cq * r' := mul_le_mul_of_nonneg_left hexp_le hcCqnn
  have hden : 0 < 1 - r' := by linarith
  have htailB_le : B * r' ^ 0 / (1 - r') ≤ c1 * Cq * r' / (1 - r') := by
    rw [pow_zero, mul_one]
    exact (div_le_div_iff_of_pos_right hden).mpr hB_le'
  have htail_eLpNorm : eLpNorm (fun om => ∑' n : ℕ, F' n om) (ENNReal.ofReal Q) μ ≤
      ENNReal.ofReal (c1 * Cq * r' / (1 - r')) :=
    htailBound0.trans (ENNReal.ofReal_le_ofReal htailB_le)
  -- combine head and tail into the full series
  have hdenρ : 0 < 1 - ρ := by linarith
  have hfull_summable_ae : ∀ᵐ om ∂μ, Summable (fun n : ℕ => w n * Y n om) := by
    filter_upwards [htailAE] with om hom
    have hFnn : ∀ n : ℕ, 0 ≤ F' n om := fun n => mul_nonneg (hwnn _) (hYnn _ om)
    have hom' : Summable (fun n => F' n om) := by
      have heq : (fun n => ‖F' n om‖) = fun n => F' n om := by
        funext n; exact Real.norm_of_nonneg (hFnn n)
      rwa [heq] at hom
    exact (summable_nat_add_iff (N + 1)).mp hom'
  have hae_eq : (fun om => ∑' n : ℕ, w n * Y n om) =ᶠ[MeasureTheory.ae μ]
      (fun om => (∑ n ∈ Finset.range (N + 1), w n * Y n om) + ∑' n : ℕ, F' n om) := by
    filter_upwards [hfull_summable_ae] with om hg
    exact (hg.sum_add_tsum_nat_add (N + 1)).symm
  have hcombined_meas : AEStronglyMeasurable
      (fun om => (∑ n ∈ Finset.range (N + 1), w n * Y n om) + ∑' n : ℕ, F' n om) μ :=
    hhead_meas.add htailMemLp0.aestronglyMeasurable
  have hfull_meas : AEStronglyMeasurable (fun om => ∑' n : ℕ, w n * Y n om) μ :=
    hcombined_meas.congr hae_eq.symm
  have hfull_eLpNorm_eq : eLpNorm (fun om => ∑' n : ℕ, w n * Y n om) (ENNReal.ofReal Q) μ =
      eLpNorm (fun om => (∑ n ∈ Finset.range (N + 1), w n * Y n om) + ∑' n : ℕ, F' n om)
        (ENNReal.ofReal Q) μ :=
    eLpNorm_congr_ae hae_eq
  have hfull_bound : eLpNorm (fun om => ∑' n : ℕ, w n * Y n om) (ENNReal.ofReal Q) μ ≤
      ENNReal.ofReal (c1 * Cq / (1 - ρ) + c1 * Cq * r' / (1 - r')) := by
    rw [hfull_eLpNorm_eq, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (eLpNorm_add_le hQ1e).trans
      (add_le_add hhead_eLpNorm htail_eLpNorm)
  have hCboundnn : 0 ≤ c1 * Cq / (1 - ρ) + c1 * Cq * r' / (1 - r') :=
    add_nonneg (div_nonneg (by positivity) hdenρ.le) (div_nonneg (by positivity) hden.le)
  refine ⟨?_, ?_, hfull_summable_ae⟩ <;>
    · rw [hc1eq] at hfull_bound
      first
        | exact hfull_bound.trans_lt ENNReal.ofReal_lt_top
        | exact hfull_bound

/-- Admissible-infrared form of `lambda_inv_moments`: the characterized field or a finite infrared truncation. -/
theorem aux_lambda_inv_moments_adm :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
  ∃ delta0 : ℝ → ℝ, (∀ p : ℝ, 1 ≤ p → 0 < delta0 p) ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ p : ℝ, 1 ≤ p → M.delta ≤ delta0 p →
      ∃ Cbound : ℝ,
        (∀ N : ℕ, MemLp (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N : ℕ, eLpNorm (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound) := by
  intro d hd _ _ E s hs
  obtain ⟨hs0, hs14⟩ := hs
  have hs1 : s ≤ 1 := by linarith
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set Qf : ℝ → ℝ := fun p => max (2 * p) (2 * (d : ℝ) / s) with hQf_def
  have hQfge1 : ∀ p : ℝ, 1 ≤ Qf p := by
    intro p
    have h16 : (16 : ℝ) < 2 * (d : ℝ) / s := by
      rw [lt_div_iff₀ hs0]; nlinarith
    have h2 : (16 : ℝ) ≤ Qf p := h16.le.trans (le_max_right _ _)
    linarith
  have hQfpos : ∀ p : ℝ, 0 < Qf p := fun p => lt_of_lt_of_le one_pos (hQfge1 p)
  have hDQp : ∀ p : ℝ, 2 * (d : ℝ) ≤ s * Qf p := by
    intro p
    have h1 : 2 * (d : ℝ) / s ≤ Qf p := le_max_right _ _
    rw [div_le_iff₀ hs0] at h1
    linarith
  have hcell := fun p => lambda_inv_cell_moment d hd E (Qf p) (hQfge1 p)
  choose deltaQ CdF hdeltaQpos hCdFpos hmain using hcell
  set delta0A : ℝ → ℝ := fun p =>
    Real.sqrt (s * Real.log 3 / (4 * (CdF p * (Qf p + (Qf p) ^ 2)) + 4)) with hdelta0A_def
  set delta0B : ℝ → ℝ := fun p => min 1 (s * Real.log 3 / (2 * (CdF p) + 1)) with hdelta0B_def
  set delta0 : ℝ → ℝ := fun p => min (deltaQ p) (min (delta0A p) (delta0B p)) with hdelta0_def
  have hdelta0A_pos : ∀ p : ℝ, 0 < delta0A p := by
    intro p
    rw [hdelta0A_def]
    apply Real.sqrt_pos.mpr
    apply div_pos (mul_pos hs0 hlog3pos)
    have hQ2 : 0 < Qf p + (Qf p) ^ 2 := by nlinarith [hQfpos p]
    nlinarith [hCdFpos p]
  have hdelta0B_pos : ∀ p : ℝ, 0 < delta0B p := by
    intro p
    rw [hdelta0B_def]
    apply lt_min one_pos
    apply div_pos (mul_pos hs0 hlog3pos)
    linarith [hCdFpos p]
  have hdelta0_pos : ∀ p : ℝ, 0 < delta0 p := by
    intro p
    rw [hdelta0_def]
    exact lt_min (hdeltaQpos p) (lt_min (hdelta0A_pos p) (hdelta0B_pos p))
  refine ⟨delta0, fun p _ => hdelta0_pos p, ?_⟩
  intro M Rm H hInfrared z r hr hrle1 p hp1 hMdelta
  have hMdelta0 : M.delta ≤ deltaQ p := hMdelta.trans (min_le_left _ _)
  have hMdelta_A : M.delta ≤ delta0A p := hMdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMdelta_B : M.delta ≤ delta0B p := hMdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hMdelta_nn : 0 ≤ M.delta := (M.shellPrefix.delta_pos).le
  have hMdelta_le1 : M.delta ≤ 1 := hMdelta_B.trans (min_le_left _ _)
  have hMdelta_leZ : M.delta ≤ s * Real.log 3 / (2 * (CdF p) + 1) := hMdelta_B.trans (min_le_right _ _)
  have hdl2_le : M.delta ^ 2 ≤ s * Real.log 3 / (4 * (CdF p * (Qf p + (Qf p) ^ 2)) + 4) := by
    have hstep : M.delta ^ 2 ≤ (delta0A p) ^ 2 := by
      apply pow_le_pow_left₀ hMdelta_nn hMdelta_A
    have hQ2nn : (0:ℝ) ≤ Qf p + (Qf p) ^ 2 := by nlinarith [hQfpos p]
    have hden_nn : (0:ℝ) ≤ s * Real.log 3 / (4 * (CdF p * (Qf p + (Qf p) ^ 2)) + 4) := by
      apply div_nonneg (mul_nonneg hs0.le hlog3pos.le)
      nlinarith [hCdFpos p, hQ2nn]
    rw [hdelta0A_def, Real.sq_sqrt hden_nn] at hstep
    exact hstep
  have hcondA : CdF p * (Qf p + (Qf p) ^ 2) * M.delta ^ 2 ≤ (s / 4) * Real.log 3 := by
    have := aux_lambda_inv_moments_condA_helper (CdF p * (Qf p + (Qf p) ^ 2))
      (s * Real.log 3) (M.delta ^ 2) (by nlinarith [hCdFpos p, hQfpos p])
      (by positivity) (sq_nonneg _) hdl2_le
    linarith [this]
  have hcondB : CdF p * M.delta * (1 + M.delta) ≤ s * Real.log 3 :=
    aux_lambda_inv_moments_condB_helper (CdF p) (s * Real.log 3) M.delta
      (hCdFpos p).le (by positivity) hMdelta_le1 hMdelta_nn hMdelta_leZ
  obtain ⟨Cq, hCqpos, hcellbound⟩ := hmain p M Rm H hInfrared z r hr hrle1 hMdelta0
  have hQpge : ENNReal.ofReal p ≤ ENNReal.ofReal (Qf p) :=
    ENNReal.ofReal_le_ofReal ((le_max_left (2 * p) (2 * (d : ℝ) / s)).trans' (by linarith))
  have key : ∀ N : ℕ, MemLp (fun om : BilateralField d =>
      (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((1 - (3 : ℝ) ^ (-s)) * Cq /
            (1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * M.delta ^ 2)) +
          (1 - (3 : ℝ) ^ (-s)) * Cq * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s))) := by
    intro N
    set YN : ℕ → BilateralField d → ℝ := fun n om =>
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) with hYN_def
    have hYNnn : ∀ n om, 0 ≤ YN n om := fun n om => aux_lambda_inv_moments_Y_nonneg _ _
    have hYmeasN : ∀ n : ℕ, AEStronglyMeasurable (YN n) (chaosSampleLaw M).toMeasure :=
      fun n => (hcellbound N n).1
    have hYboundN : ∀ n : ℕ, eLpNorm (YN n) (ENNReal.ofReal (Qf p)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cq * (if n ≤ N then (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / (Qf p)) *
              Real.exp (CdF p * (Qf p + (Qf p) ^ 2) * M.delta ^ 2 * (n : ℝ))
             else Real.exp ((CdF p * M.delta + CdF p * M.delta ^ 2) * (N : ℝ)))) :=
      fun n => (hcellbound N n).2
    obtain ⟨hMemLpQ, hBoundQ, hSummableAE⟩ :=
      aux_lambda_inv_moments_series_bound (chaosSampleLaw M).toMeasure s (d : ℝ) (Qf p)
        (CdF p) Cq M.delta N hs0 (Nat.cast_nonneg d) (hDQp p) (hQfge1 p) (hCdFpos p) hCqpos
        hMdelta_nn hcondA hcondB YN hYNnn hYmeasN hYboundN
    have hae_dom : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹ ≤
          ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n * YN n om := by
      filter_upwards [hSummableAE] with om hom_summable
      obtain ⟨Ssum0, hSsum0nn, hsqrt_summable, hSsum0eq, hlam_inv_eq⟩ :=
        aux_lambda_inv_moments_lam_inv_eq E z r hr (cutoffPositiveCoefficient M H om N z hr)
          s hs0 hs1
      have hYnn' : ∀ n : ℕ, 0 ≤ YN n om := fun n => hYNnn n om
      have hcs := aux_lambda_inv_moments_cs hs0 0 (fun n => YN n om) hYnn'
        (by simpa using hsqrt_summable) (by simpa using hom_summable)
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.add_zero] at hcs
      rw [hlam_inv_eq, hSsum0eq]
      exact hcs
    have hsqrt_summable_all : ∀ om : BilateralField d, Summable (fun n : ℕ =>
        Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (YN n om) (1 / 2)) := by
      intro om
      obtain ⟨_, _, hs', _, _⟩ := aux_lambda_inv_moments_lam_inv_eq E z r hr
        (cutoffPositiveCoefficient M H om N z hr) s hs0 hs1
      exact hs'
    have hSsum_meas : AEStronglyMeasurable (fun om => ∑' n : ℕ,
        Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (YN n om) (1 / 2))
        (chaosSampleLaw M).toMeasure :=
      aux_lambda_inv_moments_Ssum_meas (chaosSampleLaw M).toMeasure s YN hYmeasN
        hsqrt_summable_all
    have hlam_inv_meas : AEStronglyMeasurable (fun om : BilateralField d =>
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (chaosSampleLaw M).toMeasure := by
      have heq : (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹) =
          (fun om => (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow (YN n om) (1 / 2)) ^ 2) := by
        funext om
        obtain ⟨Ssum0, _, _, hSsum0eq, hlam_inv_eq⟩ := aux_lambda_inv_moments_lam_inv_eq E z r hr
          (cutoffPositiveCoefficient M H om N z hr) s hs0 hs1
        rw [hlam_inv_eq, hSsum0eq]
      rw [heq]
      exact (continuous_pow 2).comp_aestronglyMeasurable hSsum_meas
    have hlam_nn : ∀ om : BilateralField d, 0 ≤
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹ := fun om =>
      le_of_lt (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _))
    have heLpNorm_le : eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal (Qf p)) (chaosSampleLaw M).toMeasure ≤
        eLpNorm (fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n * YN n om)
          (ENNReal.ofReal (Qf p)) (chaosSampleLaw M).toMeasure := by
      apply eLpNorm_mono_ae_real hlam_inv_meas
      filter_upwards [hae_dom] with om hom
      rwa [Real.norm_of_nonneg (hlam_nn om)]
    have heLpNorm_final : eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        eLpNorm (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal (Qf p)) (chaosSampleLaw M).toMeasure :=
      eLpNorm_le_eLpNorm_of_exponent_le hQpge
    have hfinal_bound : eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((1 - (3 : ℝ) ^ (-s)) * Cq /
            (1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * M.delta ^ 2)) +
          (1 - (3 : ℝ) ^ (-s)) * Cq * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s))) :=
      heLpNorm_final.trans (heLpNorm_le.trans hBoundQ)
    exact ⟨hfinal_bound.trans_lt ENNReal.ofReal_lt_top, hfinal_bound⟩
  exact ⟨_, fun N => (key N).1, fun N => (key N).2⟩



theorem lambda_inv_moments :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
  ∃ delta0 : ℝ → ℝ, (∀ p : ℝ, 1 ≤ p → 0 < delta0 p) ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ p : ℝ, 1 ≤ p → M.delta ≤ delta0 p →
      ∃ Cbound : ℝ,
        (∀ N : ℕ, MemLp (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N : ℕ, eLpNorm (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound) := by
  intro d hd _ _ E s hs
  obtain ⟨delta0, hpos, hall⟩ := aux_lambda_inv_moments_adm d hd E s hs
  exact ⟨delta0, hpos, fun M Rm H hH => hall M Rm H (InfraredAdmissible.of_char hH)⟩

end SubdiffusiveProcess.Paper
