module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Homogenization.Book.Ch02.Matrices
public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationError
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Paper.probemax_measurable_R_gen
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_descendant_rechart
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace Paper


/-- The unit chart of the cutoff coefficient (the `F` of the principal). -/
def aux_lem_prefix_limit_g9_cell_moment_F {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ)) :
    ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
  fun K omega => I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1

theorem aux_geo_arith {w c T q : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (hq : 0 < q)
    (hT : w * c ^ (q / 2) ≤ T) (hTpos : 0 < T) :
    c ≤ w ^ (-(2 / q)) * (T ^ (-(2 / q)))⁻¹ := by
  have hqne : q ≠ 0 := ne_of_gt hq
  have hq2 : 0 < 2 / q := div_pos (by norm_num) hq
  have hc2 : 0 ≤ c ^ (q / 2) := Real.rpow_nonneg hc _
  have hbase : 0 ≤ w * c ^ (q / 2) := mul_nonneg (le_of_lt hw) hc2
  have step1 : (w * c ^ (q / 2)) ^ (2 / q) ≤ T ^ (2 / q) :=
    Real.rpow_le_rpow hbase hT (le_of_lt hq2)
  have hexp : (q / 2) * (2 / q) = 1 := by
    field_simp
  have hval : (w * c ^ (q / 2)) ^ (2 / q) = w ^ (2 / q) * c := by
    rw [Real.mul_rpow (le_of_lt hw) hc2]
    rw [← Real.rpow_mul hc (q / 2) (2 / q), hexp, Real.rpow_one]
  have hmain : w ^ (2 / q) * c ≤ T ^ (2 / q) := by
    rw [hval] at step1
    exact step1
  have hw2pos : 0 < w ^ (2 / q) := Real.rpow_pos_of_pos hw _
  have hfinal : c ≤ (w ^ (2 / q))⁻¹ * T ^ (2 / q) := by
    have h := mul_le_mul_of_nonneg_left hmain (le_of_lt (inv_pos.mpr hw2pos))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hw2pos), one_mul] at h
  rw [Real.rpow_neg (le_of_lt hw) (2 / q), Real.rpow_neg (le_of_lt hTpos) (2 / q), inv_inv]
  exact hfinal

theorem aux_lem_prefix_limit_g9_cell_moment_sigma_le_lambda {d : ℕ}
    (Q : Homogenization.TriadicCube d) (s q : ℝ) (hs : 0 < s) (hq : 0 < q)
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hpos : 0 < Homogenization.Book.Ch02.lambdaSqFinite Q s q a) :
    Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q a ≤
      (Homogenization.Book.Ch02.geometricDiscount s q) ^ (-(2 / q)) *
        (Homogenization.Book.Ch02.lambdaSqFinite Q s q a)⁻¹ := by
  have hdisc_pos : 0 < Homogenization.Book.Ch02.geometricDiscount s q := by
    unfold Homogenization.Book.Ch02.geometricDiscount
    have h1 : Real.rpow (3 : ℝ) (-s * q) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · norm_num
      · have : 0 < s * q := mul_pos hs hq
        linarith
    linarith
  have hdisc_nonneg : 0 ≤ Homogenization.Book.Ch02.geometricDiscount s q := le_of_lt hdisc_pos
  have hq2 : 0 < q / 2 := by linarith
  have hmax_nonneg : ∀ n : ℕ,
      0 ≤ Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
    intro n
    unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    exact Homogenization.Book.Ch02.finsetSupReal_nonneg _ _
      (fun R _ => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg R a)
  have hterm_nonneg : ∀ n : ℕ,
      0 ≤ Homogenization.Book.Ch02.geometricWeight s q n *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
    intro n
    apply mul_nonneg
    · unfold Homogenization.Book.Ch02.geometricWeight
      exact mul_nonneg hdisc_nonneg (Real.rpow_nonneg (by norm_num) _)
    · exact Real.rpow_nonneg (hmax_nonneg n) _
  unfold Homogenization.Book.Ch02.lambdaSqFinite at hpos ⊢
  set T : ℝ := ∑' n : ℕ,
      Homogenization.Book.Ch02.geometricWeight s q n *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) with hTdef
  have hT_nonneg : 0 ≤ T := by
    rw [hTdef]
    exact tsum_nonneg hterm_nonneg
  have hexp_ne : -(2 / q) ≠ 0 := by
    have h2q : (2 : ℝ) / q ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt hq)
    exact neg_ne_zero.mpr h2q
  have hT_ne_zero : T ≠ 0 := by
    intro hT0
    have hzero : Real.rpow T (-(2 / q)) = 0 := by
      rw [hT0]
      exact Real.zero_rpow hexp_ne
    rw [hzero] at hpos
    exact absurd hpos (lt_irrefl 0)
  have hT_pos : 0 < T := lt_of_le_of_ne hT_nonneg (Ne.symm hT_ne_zero)
  have hsumm : Summable (fun n : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s q n *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)) := by
    by_contra hns
    have hzero : T = 0 := by
      rw [hTdef]
      exact tsum_eq_zero_of_not_summable hns
    exact hT_ne_zero hzero
  have hc_nonneg : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q a :=
    Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg Q a
  have hmem : Q ∈ Homogenization.descendantsAtScale Q Q.scale := by
    rw [Homogenization.descendantsAtScale_self]
    exact Finset.mem_singleton_self Q
  have hc_le : Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q a ≤
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q Q.scale a :=
    Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale a hmem
  have hle0 : Homogenization.Book.Ch02.geometricWeight s q 0 *
      Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) a) (q / 2) ≤ T := by
    rw [hTdef]
    exact Summable.le_tsum hsumm 0 (fun j _ => hterm_nonneg j)
  have hw0 : Homogenization.Book.Ch02.geometricWeight s q 0 = Homogenization.Book.Ch02.geometricDiscount s q := by
    unfold Homogenization.Book.Ch02.geometricWeight
    simp
  have hbound : Homogenization.Book.Ch02.geometricDiscount s q *
      Real.rpow (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q a) (q / 2) ≤ T := by
    have h1 : Homogenization.Book.Ch02.geometricDiscount s q *
        Real.rpow (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q a) (q / 2) ≤
        Homogenization.Book.Ch02.geometricDiscount s q *
          Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q Q.scale a) (q / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc_nonneg hc_le (le_of_lt hq2)) hdisc_nonneg
    have h2 : Homogenization.Book.Ch02.geometricDiscount s q *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q Q.scale a) (q / 2) =
        Homogenization.Book.Ch02.geometricWeight s q 0 *
          Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) a) (q / 2) := by
      rw [hw0]
      have hz : Q.scale - ((0 : ℕ) : ℤ) = Q.scale := by simp
      rw [hz]
    linarith [h1, h2, hle0]
  exact aux_geo_arith hdisc_pos hc_nonneg hq hbound hT_pos

theorem aux_lem_prefix_limit_g9_cell_moment_b_le_Lambda {d : ℕ}
    (Q : Homogenization.TriadicCube d) (s q : ℝ) (hs : 0 < s) (hq : 0 < q)
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hpos : 0 < Homogenization.Book.Ch02.LambdaSqFinite Q s q a) :
    Homogenization.Book.Ch02.coarseBMatrixNorm Q a ≤
      (Homogenization.Book.Ch02.geometricDiscount s q) ^ (-(2 / q)) *
        Homogenization.Book.Ch02.LambdaSqFinite Q s q a := by
  unfold Homogenization.Book.Ch02.LambdaSqFinite
  set W := Homogenization.Book.Ch02.geometricDiscount s q with hWdef
  set T := ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s q n *
      Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n:ℤ)) a) (q/2) with hTdef
  set c := Homogenization.Book.Ch02.coarseBMatrixNorm Q a with hcdef
  have hWpos : 0 < W := by
    rw [hWdef, Homogenization.Book.Ch02.geometricDiscount]
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by have := mul_pos hs hq; linarith))
  have hWnn : 0 ≤ W := le_of_lt hWpos
  have hq2 : 0 ≤ q / 2 := div_nonneg (le_of_lt hq) (by norm_num)
  have h2q : 0 ≤ (2:ℝ) / q := div_nonneg (by norm_num) (le_of_lt hq)
  have h2q' : (2:ℝ) / q ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt hq)
  have hc : 0 ≤ c := by
    rw [hcdef, Homogenization.Book.Ch02.coarseBMatrixNorm, Homogenization.Book.Ch02.matrixNorm]
    exact norm_nonneg _
  have hMaxnn : ∀ k : ℤ, 0 ≤ Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q k a := by
    intro k
    rw [Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale]
    apply Homogenization.Book.Ch02.finsetSupReal_nonneg
    intro x _
    rw [Homogenization.Book.Ch02.coarseBMatrixNorm, Homogenization.Book.Ch02.matrixNorm]
    exact norm_nonneg _
  have hFnn : ∀ n : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s q n *
      Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n:ℤ)) a) (q/2) := by
    intro n
    apply mul_nonneg
    · rw [Homogenization.Book.Ch02.geometricWeight, ← hWdef]
      exact mul_nonneg hWnn (Real.rpow_nonneg (by norm_num) _)
    · exact Real.rpow_nonneg (hMaxnn _) _
  have hSumm : Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s q n *
      Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n:ℤ)) a) (q/2)) := by
    by_contra hns
    have hT0 : T = 0 := by
      rw [hTdef]
      exact tsum_eq_zero_of_not_summable hns
    have hzero : Homogenization.Book.Ch02.LambdaSqFinite Q s q a = 0 := by
      unfold Homogenization.Book.Ch02.LambdaSqFinite
      rw [← hTdef, hT0]
      exact Real.zero_rpow h2q'
    linarith [hpos, hzero]
  have hM0 : c ≤ Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q Q.scale a := by
    rw [hcdef]
    refine Homogenization.Book.Ch02.coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale a ?_
    rw [Homogenization.descendantsAtScale_self]
    exact Finset.mem_singleton_self Q
  have hF0eq : Homogenization.Book.Ch02.geometricWeight s q 0 *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - ((0:ℕ):ℤ)) a) (q/2)
      = W * Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q Q.scale a) (q/2) := by
    have h1 : Homogenization.Book.Ch02.geometricWeight s q 0 = W := by
      rw [Homogenization.Book.Ch02.geometricWeight, ← hWdef]
      have hz : -s * q * (↑(0:ℕ) : ℝ) = 0 := by simp only [Nat.cast_zero, mul_zero]
      have hr : Real.rpow (3:ℝ) (0:ℝ) = 1 := Real.rpow_zero 3
      rw [hz, hr, mul_one]
    have h2 : Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - ((0:ℕ):ℤ)) a
        = Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q Q.scale a := by
      simp only [Nat.cast_zero, sub_zero]
    rw [h1, h2]
  have hterm0 : W * Real.rpow c (q/2) ≤ Homogenization.Book.Ch02.geometricWeight s q 0 *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - ((0:ℕ):ℤ)) a) (q/2) := by
    rw [hF0eq]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc hM0 hq2) hWnn
  have hF0_le_T : Homogenization.Book.Ch02.geometricWeight s q 0 *
        Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - ((0:ℕ):ℤ)) a) (q/2) ≤ T := by
    rw [hTdef]
    exact Summable.le_tsum hSumm 0 (fun j hj => hFnn j)
  have hG : W * Real.rpow c (q/2) ≤ T := le_trans hterm0 hF0_le_T
  have hGnn : 0 ≤ W * Real.rpow c (q/2) := mul_nonneg hWnn (Real.rpow_nonneg hc _)
  have hrpow : Real.rpow (W * Real.rpow c (q/2)) (2/q) ≤ Real.rpow T (2/q) :=
    Real.rpow_le_rpow hGnn hG h2q
  have hI : Real.rpow (W * Real.rpow c (q/2)) (2/q) = Real.rpow W (2/q) * c := by
    have hstep : Real.rpow (W * Real.rpow c (q/2)) (2/q)
        = Real.rpow W (2/q) * Real.rpow (Real.rpow c (q/2)) (2/q) :=
      Real.mul_rpow hWnn (Real.rpow_nonneg hc (q/2))
    rw [hstep]
    have hstep2 : Real.rpow (Real.rpow c (q/2)) (2/q) = Real.rpow c ((q/2)*(2/q)) :=
      (Real.rpow_mul hc (q/2) (2/q)).symm
    rw [hstep2]
    have hqq : (q/2) * (2/q) = 1 := by field_simp
    have hstep3 : Real.rpow c ((q/2)*(2/q)) = c := by rw [hqq]; exact Real.rpow_one c
    rw [hstep3]
  rw [hI] at hrpow
  have ha : 0 ≤ Real.rpow W (-(2/q)) := Real.rpow_nonneg hWnn (-(2/q))
  have hmul : Real.rpow W (-(2/q)) * (Real.rpow W (2/q) * c) ≤ Real.rpow W (-(2/q)) * Real.rpow T (2/q) :=
    mul_le_mul_of_nonneg_left hrpow ha
  have h2 : Real.rpow W (-(2/q)) * Real.rpow W (2/q) = 1 := by
    have h1 : Real.rpow W (-(2/q)) = (Real.rpow W (2/q))⁻¹ := Real.rpow_neg hWnn (2/q)
    rw [h1]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hWpos (2/q)))
  rw [← mul_assoc, h2, one_mul] at hmul
  exact hmul

theorem aux_lem_prefix_limit_g9_cell_moment_chart_sigma_le_lam {d : ℕ}
    (I : Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
        (I.chart z r hr a w r') ≤
      (Homogenization.Book.Ch02.geometricDiscount s 2) ^ (-(2 / (2 : ℝ))) *
        (I.lam z r hr a w r' s 2)⁻¹ := by
  have hs0 : 0 < s := hs.1
  have hq : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
  have hEq := I.lam_eq z r hr a w r' hr' hsub s hs (2 : ℝ≥0∞) hq
  have hsimp : (if (2 : ℝ≥0∞) = ⊤ then Homogenization.Book.Ch02.MultiscaleExponent.infinity
      else Homogenization.Book.Ch02.MultiscaleExponent.finite (2 : ℝ≥0∞).toReal)
      = Homogenization.Book.Ch02.MultiscaleExponent.finite (2 : ℝ) := by
    rw [if_neg ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat 2]
  have hEq' : I.lam z r hr a w r' s (2 : ℝ≥0∞)
      = Homogenization.Book.Ch02.lambdaSqFinite (Homogenization.originCube d 0) s 2
          (I.chart z r hr a w r') := by
    rw [hEq, hsimp, Homogenization.Book.Ch02.lambdaSq_finite]
  have hpos : 0 < Homogenization.Book.Ch02.lambdaSqFinite (Homogenization.originCube d 0) s 2
      (I.chart z r hr a w r') := by
    rw [← hEq']
    exact I.lam_pos z r hr a w r' s 2
  have hmain := aux_lem_prefix_limit_g9_cell_moment_sigma_le_lambda
    (Homogenization.originCube d 0) s 2 hs0 (by norm_num) (I.chart z r hr a w r') hpos
  rw [← hEq'] at hmain
  exact hmain

theorem aux_lem_prefix_limit_g9_cell_moment_chart_b_le_Lam {d : ℕ}
    (I : Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    Homogenization.Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
        (I.chart z r hr a w r') ≤
      (Homogenization.Book.Ch02.geometricDiscount s 2) ^ (-(2 / (2 : ℝ))) *
        I.Lam z r hr a w r' s 2 := by
  have hq : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hEq : I.Lam z r hr a w r' s 2 =
      Homogenization.Book.Ch02.LambdaSqFinite (Homogenization.originCube d 0) s 2
        (I.chart z r hr a w r') := by
    rw [I.Lam_eq z r hr a w r' hr' hsub s hs 2 hq]
    rw [if_neg (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
    exact Homogenization.Book.Ch02.LambdaSq_finite _ _ _ _
  have hpos : 0 < Homogenization.Book.Ch02.LambdaSqFinite (Homogenization.originCube d 0) s 2
      (I.chart z r hr a w r') := by
    rw [← hEq]
    exact I.Lam_pos z r hr a w r' s 2
  have hb := aux_lem_prefix_limit_g9_cell_moment_b_le_Lambda (Homogenization.originCube d 0) s 2
    hs.1 (by norm_num) (I.chart z r hr a w r') hpos
  rw [hEq]
  exact hb


/-- (flash-pending) -/
theorem aux_lem_prefix_limit_g9_cell_moment_subchart_aeeq {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ)
    (hsub : (centeredCube w ρ hρ : Set (SpatialCoordinates d)) ⊆
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    Homogenization.Book.Ch02.CoeffOn.AEEq
      ((I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega N 0 one_pos) w ρ).coeffOn Q)
      ((I.chart w ρ hρ (Lane4.cutoffPositiveCoefficient M H omega N w hρ) w ρ).coeffOn Q) := by
  unfold Homogenization.Book.Ch02.CoeffOn.AEEq
  change ((I.chart (0 : SpatialCoordinates d) 1 one_pos
      (Lane4.cutoffPositiveCoefficient M H omega N (0 : SpatialCoordinates d) one_pos) w ρ).coeffOn
        Q).toCoeffField
      =ᵐ[volume.restrict (Homogenization.openCubeSet Q)]
    ((I.chart w ρ hρ (Lane4.cutoffPositiveCoefficient M H omega N w hρ) w ρ).coeffOn Q).toCoeffField
  have hA := I.chart_eq (0 : SpatialCoordinates d) (1 : ℝ) one_pos
    (Lane4.cutoffPositiveCoefficient M H omega N (0 : SpatialCoordinates d) one_pos) w ρ hρ hsub Q hQ
  have hB := I.chart_eq w ρ hρ (Lane4.cutoffPositiveCoefficient M H omega N w hρ) w ρ hρ
    subset_rfl Q hQ
  have hqmp1 : Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => ρ • x) volume volume :=
    Measure.quasiMeasurePreserving_smul volume hρ.ne'
  have hqmp2 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => w + y) volume volume :=
    (measurePreserving_add_left volume w).quasiMeasurePreserving
  have hqmp : Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => w + ρ • x) volume volume :=
    hqmp2.comp hqmp1
  have hqmp' : Measure.QuasiMeasurePreserving
      (fun x : SpatialCoordinates d => fun i => w i + ρ * x i) volume volume := hqmp
  have hSm0 : MeasurableSet
      ((centeredCube (0 : SpatialCoordinates d) 1 one_pos : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) :=
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet
  have hSmw : MeasurableSet
      ((centeredCube w ρ hρ : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) :=
    (centeredCube w ρ hρ).isOpen.measurableSet
  have hcoe0 : ∀ᵐ y ∂volume.restrict
      ((centeredCube (0 : SpatialCoordinates d) 1 one_pos : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)),
      ((Lane4.cutoffPositiveCoefficient M H omega N (0 : SpatialCoordinates d) one_pos).val :
          SpatialCoordinates d → ℝ) y = cutoffCoefficient M H omega N y / 1 := by
    filter_upwards [SubdiffusiveProcess.normalizedContinuousPositiveCoefficient_coeFn
      (Ω := centeredCube (0 : SpatialCoordinates d) 1 one_pos)
      (hΩ := ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos⟩)
      (closedCube (0 : SpatialCoordinates d) 1 one_pos)
      (Lane4.cutoffCoefficientCM M H omega N (0 : SpatialCoordinates d) one_pos)
      (Lane4.cutoffCoefficientCM_pos M H omega N (0 : SpatialCoordinates d) one_pos) 1 one_pos,
      ae_restrict_mem hSm0] with y hy hyc
    unfold Lane4.cutoffPositiveCoefficient
    rw [hy hyc]
    rfl
  have hcoew : ∀ᵐ y ∂volume.restrict
      ((centeredCube w ρ hρ : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
      ((Lane4.cutoffPositiveCoefficient M H omega N w hρ).val : SpatialCoordinates d → ℝ) y =
        cutoffCoefficient M H omega N y / 1 := by
    filter_upwards [SubdiffusiveProcess.normalizedContinuousPositiveCoefficient_coeFn
      (Ω := centeredCube w ρ hρ)
      (hΩ := ⟨centeredCube_subset_closedCube w hρ⟩)
      (closedCube w ρ hρ)
      (Lane4.cutoffCoefficientCM M H omega N w hρ)
      (Lane4.cutoffCoefficientCM_pos M H omega N w hρ) 1 one_pos,
      ae_restrict_mem hSmw] with y hy hyc
    unfold Lane4.cutoffPositiveCoefficient
    rw [hy hyc]
    rfl
  have hcont : Continuous (fun x : SpatialCoordinates d => fun i => w i + ρ * x i) := by
    fun_prop
  have hW0 : MeasurableSet ((fun x : SpatialCoordinates d => fun i => w i + ρ * x i) ⁻¹'
      ((centeredCube (0 : SpatialCoordinates d) 1 one_pos : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))) := hSm0.preimage hcont.measurable
  have hWw : MeasurableSet ((fun x : SpatialCoordinates d => fun i => w i + ρ * x i) ⁻¹'
      ((centeredCube w ρ hρ : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) :=
    hSmw.preimage hcont.measurable
  have hc0 : Homogenization.cubeCenter (Homogenization.originCube d 0) = (0 : SpatialCoordinates d) := by
    funext i
    simp [Homogenization.cubeCenter, Homogenization.originCube, Homogenization.cubeScaleFactor]
  have hs0 : Homogenization.cubeScaleFactor (Homogenization.originCube d 0) = 1 := by
    rw [Homogenization.cubeScaleFactor_originCube]
    norm_num
  have hunit : ((centeredCube (0 : SpatialCoordinates d) 1 one_pos : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    have h := centeredCube_eq_openCubeSet (Homogenization.originCube d 0)
      (by rw [Homogenization.cubeScaleFactor_originCube]; norm_num)
    simp only [hc0, hs0] at h
    exact h
  have hφS1 : ∀ x ∈ Homogenization.openCubeSet Q,
      (fun i => w i + ρ * x i) ∈ ((centeredCube w ρ hρ : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) := by
    intro x hx
    have hx0 : dist x (0 : SpatialCoordinates d) < 1 / 2 := by
      have hx' : x ∈ ((centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) := hunit.symm ▸ hQ hx
      exact hx'
    change dist (fun i => w i + ρ * x i) w < ρ / 2
    have hdist : dist (fun i => w i + ρ * x i) w = ρ * dist x (0 : SpatialCoordinates d) := by
      rw [dist_eq_norm, dist_eq_norm]
      have h5 : (fun i => w i + ρ * x i) - w = ρ • x := by
        funext i
        show w i + ρ * x i - w i = (ρ • x) i
        rw [Pi.smul_apply, smul_eq_mul]
        ring
      rw [h5, norm_smul, Real.norm_of_nonneg hρ.le, sub_zero]
    rw [hdist]
    have hlt := mul_lt_mul_of_pos_left hx0 hρ
    linarith
  have hφS0 : ∀ x ∈ Homogenization.openCubeSet Q,
      (fun i => w i + ρ * x i) ∈ ((centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) :=
    fun x hx => hsub (hφS1 x hx)
  have hcoe0T : ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
      ((Lane4.cutoffPositiveCoefficient M H omega N (0 : SpatialCoordinates d) one_pos).val :
          SpatialCoordinates d → ℝ) (fun i => w i + ρ * x i) =
        cutoffCoefficient M H omega N (fun i => w i + ρ * x i) / 1 :=
    ae_restrict_of_ae_restrict_of_subset hφS0
      ((ae_restrict_iff' hW0).mpr (hqmp'.ae ((ae_restrict_iff' hSm0).mp hcoe0)))
  have hcoewT : ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
      ((Lane4.cutoffPositiveCoefficient M H omega N w hρ).val : SpatialCoordinates d → ℝ)
          (fun i => w i + ρ * x i) =
        cutoffCoefficient M H omega N (fun i => w i + ρ * x i) / 1 :=
    ae_restrict_of_ae_restrict_of_subset hφS1
      ((ae_restrict_iff' hWw).mpr (hqmp'.ae ((ae_restrict_iff' hSmw).mp hcoew)))
  filter_upwards [hA, hB, hcoe0T, hcoewT] with x h1 h2 h3 h4
  exact h1.trans ((congrArg Homogenization.scalarMatrix (h3.trans h4.symm)).trans h2.symm)

/-- (flash-pending) -/
theorem aux_lem_prefix_limit_g9_cell_moment_cell_geom {d : ℕ} (n : ℕ)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ))) :
    Homogenization.cubeScaleFactor R = (3 : ℝ) ^ (-(n : ℤ)) ∧
    Homogenization.cubeCenter R =
      (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) * ((R.index i : ℤ) : ℝ)) ∧
    centeredCube (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) * ((R.index i : ℤ) : ℝ))
        ((3 : ℝ) ^ (-(n : ℤ))) (by positivity) ≤
      centeredCube (0 : SpatialCoordinates d) 1 one_pos := by
  have hscale : R.scale = -(n : ℤ) :=
    Homogenization.Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube (by omega) hR
  refine ⟨?_, ?_, ?_⟩
  · unfold Homogenization.cubeScaleFactor
    rw [hscale]
  · funext i
    unfold Homogenization.cubeCenter Homogenization.cubeScaleFactor
    rw [hscale]
    simp only [Pi.zero_apply]
    ring
  · have hcf : Homogenization.cubeScaleFactor R = (3 : ℝ) ^ (-(n : ℤ)) := by
      unfold Homogenization.cubeScaleFactor
      rw [hscale]
    have hcc : Homogenization.cubeCenter R =
        (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) *
          ((R.index i : ℤ) : ℝ)) := by
      funext i
      unfold Homogenization.cubeCenter Homogenization.cubeScaleFactor
      rw [hscale]
      simp only [Pi.zero_apply]
      ring
    have hcf0 : Homogenization.cubeScaleFactor (Homogenization.originCube d 0) = 1 := by
      unfold Homogenization.cubeScaleFactor Homogenization.originCube
      norm_num
    have hcc0 : Homogenization.cubeCenter (Homogenization.originCube d 0) =
        (0 : SpatialCoordinates d) := by
      funext i
      simp [Homogenization.cubeCenter, Homogenization.originCube]
    have hkR : 0 < Homogenization.cubeScaleFactor R := by rw [hcf]; positivity
    have hk0 : 0 < Homogenization.cubeScaleFactor (Homogenization.originCube d 0) := by
      rw [hcf0]; norm_num
    have hk : -(n : ℤ) ≤ (Homogenization.originCube d 0).scale := by
      have h0 : (Homogenization.originCube d 0).scale = 0 := by
        simp [Homogenization.originCube]
      omega
    have hsets : (centeredCube
          (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) *
            ((R.index i : ℤ) : ℝ)) ((3 : ℝ) ^ (-(n : ℤ))) (by positivity) :
          Set (SpatialCoordinates d)) =
        (centeredCube (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R) hkR :
          Set (SpatialCoordinates d)) := by
      simp only [hcc, hcf]
    have hL : (centeredCube
          (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) *
            ((R.index i : ℤ) : ℝ)) ((3 : ℝ) ^ (-(n : ℤ))) (by positivity) :
          Set (SpatialCoordinates d)) = Homogenization.openCubeSet R := by
      rw [hsets]
      exact SubdiffusiveProcess.centeredCube_eq_openCubeSet R hkR
    have hsets0 : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)) =
        (centeredCube (Homogenization.cubeCenter (Homogenization.originCube d 0))
          (Homogenization.cubeScaleFactor (Homogenization.originCube d 0)) hk0 :
          Set (SpatialCoordinates d)) := by
      simp only [hcc0, hcf0]
    have hB : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)) =
        Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      rw [hsets0]
      exact SubdiffusiveProcess.centeredCube_eq_openCubeSet (Homogenization.originCube d 0) hk0
    intro x hx
    change x ∈ (_ : Set (SpatialCoordinates d)) at hx
    change x ∈ (_ : Set (SpatialCoordinates d))
    rw [hL] at hx
    rw [hB]
    exact Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hR hx

/-- The cell-`R` norms of the unit chart are the unit-root norms of the sub-chart of the ROOT
coefficient at the cell (chart identity `lem_as_coarse_shallow_grid_descendant_rechart` + a.e.
identification `aux_…_subchart_aeeq` + GMC `coarse*_eq_of_localAEEq`). -/
theorem aux_lem_prefix_limit_g9_cell_moment_cell_eq {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (K n : ℕ)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ))) :
    Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) =
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
        (I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos)
          (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) * ((R.index i : ℤ) : ℝ))
          ((3 : ℝ) ^ (-(n : ℤ)))) ∧
    Homogenization.Book.Ch02.coarseBMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) =
      Homogenization.Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
        (I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos)
          (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) * ((R.index i : ℤ) : ℝ))
          ((3 : ℝ) ^ (-(n : ℤ)))) := by
  obtain ⟨_hscale, hcenter, hsub⟩ := aux_lem_prefix_limit_g9_cell_moment_cell_geom n R hR
  have hρ : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := by positivity
  have hrech := lem_as_coarse_shallow_grid_descendant_rechart I M H om K n
    (0 : SpatialCoordinates d) 1 one_pos R hR
  dsimp only at hrech
  have hB : ∀ (w w' : SpatialCoordinates d) (ρ ρ' : ℝ) (h1 : 0 < ρ) (h2 : 0 < ρ'), w = w' → ρ = ρ' →
      I.chart w ρ h1 (Lane4.cutoffPositiveCoefficient M H om K w h1) w ρ =
      I.chart w' ρ' h2 (Lane4.cutoffPositiveCoefficient M H om K w' h2) w' ρ' := by
    intro w w' ρ ρ' h1 h2 hw hρρ
    subst hw
    subst hρρ
    rfl
  have hwEq : (fun i => (0 : SpatialCoordinates d) i + 1 * Homogenization.cubeCenter R i) =
      (fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) * ((R.index i : ℤ) : ℝ)) := by
    funext i
    simp [hcenter]
  have hBB := hB _ _ _ _ (mul_pos one_pos (by positivity)) hρ hwEq (one_mul _)
  have hae := aux_lem_prefix_limit_g9_cell_moment_subchart_aeeq I M H om K _ _ hρ hsub
    (Homogenization.originCube d 0) subset_rfl
  obtain ⟨-, -, hbE, hsE⟩ := hrech
  unfold aux_lem_prefix_limit_g9_cell_moment_F
  constructor
  · rw [hsE, hBB]
    exact (SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.coarseSigmaStarInvMatrixNorm_eq_of_localAEEq
      hae).symm
  · rw [hbE, hBB]
    exact (SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.coarseBMatrixNorm_eq_of_localAEEq hae).symm

/-- Scaling an `L^p` bound by a nonnegative constant. -/
theorem aux_lem_prefix_limit_g9_cell_moment_eLpNorm_const_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ≥0∞) (c B : ℝ) (hc : 0 ≤ c) (G : α → ℝ)
    (hG : eLpNorm G p μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => c * G x) p μ ≤ ENNReal.ofReal (c * B) := by
  have h1 : (fun x => c * G x) = c • G := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [h1, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  exact le_trans (mul_le_mul_right hG (ENNReal.ofReal c))
    (le_of_eq (ENNReal.ofReal_mul hc).symm)

/-- (typed hole) A quadratic form on a unit vector is bounded by the operator norm. -/
theorem aux_lem_prefix_limit_g9_cell_moment_quad_le {d : ℕ} (A : Homogenization.Mat d)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    Homogenization.vecDot e (Homogenization.matVecMul A e) ≤ Homogenization.Book.Ch02.matrixNorm A := by
  have habs := Homogenization.Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq A e
  rw [Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  calc Homogenization.vecDot e (Homogenization.matVecMul A e)
      ≤ |Homogenization.vecDot e (Homogenization.matVecMul A e)| := le_abs_self _
    _ ≤ Homogenization.Book.Ch02.matrixOperatorNorm A * Homogenization.vecNormSq e := habs
    _ = Homogenization.Book.Ch02.matrixOperatorNorm A := by rw [he, mul_one]

/-- (typed hole) Pointwise probe bound on a unit vector: with `p = q = e`,
`J = ½ e·σe + ½ (e+κe)·σ_*⁻¹(e+κe) − |e|² ≤ e·σe + (κe)·σ_*⁻¹(κe) + e·σ_*⁻¹e = e·be + e·σ_*⁻¹e`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_probe_pt {d : ℕ} [NeZero d]
    (R : Homogenization.TriadicCube d) (a : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R a 1 e ≤
      Homogenization.Book.Ch02.coarseBMatrixNorm R a +
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R a := by
  have hPSD : ∀ (S : Homogenization.Mat d), S.PosDef → ∀ v : Homogenization.Vec d,
      0 ≤ Homogenization.vecDot v (Homogenization.matVecMul S v) := by
    intro S hS v
    have := hS.posSemidef.dotProduct_mulVec_nonneg v
    simpa [Homogenization.vecDot, Homogenization.matVecMul, dotProduct, Matrix.mulVec] using this
  have hpar : ∀ (S : Homogenization.Mat d) (u v : Homogenization.Vec d),
      Homogenization.vecDot (u + v) (Homogenization.matVecMul S (u + v)) +
        Homogenization.vecDot (u - v) (Homogenization.matVecMul S (u - v)) =
      2 * Homogenization.vecDot u (Homogenization.matVecMul S u) +
        2 * Homogenization.vecDot v (Homogenization.matVecMul S v) := by
    intro S u v
    change (u + v) ⬝ᵥ S.mulVec (u + v) + (u - v) ⬝ᵥ S.mulVec (u - v) =
      2 * (u ⬝ᵥ S.mulVec u) + 2 * (v ⬝ᵥ S.mulVec v)
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
      dotProduct_sub]
    ring
  have hbq : ∀ (σ κ S : Homogenization.Mat d) (u : Homogenization.Vec d),
      Homogenization.vecDot u (Homogenization.matVecMul
        (σ + Homogenization.matTranspose κ * S * κ) u) =
      Homogenization.vecDot u (Homogenization.matVecMul σ u) +
        Homogenization.vecDot (Homogenization.matVecMul κ u)
          (Homogenization.matVecMul S (Homogenization.matVecMul κ u)) := by
    intro σ κ S u
    have h1 : Homogenization.matVecMul (σ + Homogenization.matTranspose κ * S * κ) u =
        Homogenization.matVecMul σ u + Homogenization.matVecMul (Homogenization.matTranspose κ)
          (Homogenization.matVecMul S (Homogenization.matVecMul κ u)) := by
      change (σ + Homogenization.matTranspose κ * S * κ).mulVec u =
        σ.mulVec u + (Homogenization.matTranspose κ).mulVec (S.mulVec (κ.mulVec u))
      rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [h1]
    have h2 : Homogenization.vecDot u (Homogenization.matVecMul σ u + Homogenization.matVecMul
        (Homogenization.matTranspose κ) (Homogenization.matVecMul S (Homogenization.matVecMul κ u))) =
        Homogenization.vecDot u (Homogenization.matVecMul σ u) + Homogenization.vecDot u
          (Homogenization.matVecMul (Homogenization.matTranspose κ)
            (Homogenization.matVecMul S (Homogenization.matVecMul κ u))) := by
      simp only [Homogenization.vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h2, Homogenization.vecDot_matVecMul_transpose]
  set U := Homogenization.Book.Ch02.cubeDomain R
  set A := a.coeffOn R
  have hJ : SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R a 1 e =
      Homogenization.Book.Ch02.responseJ U A e e := by
    simp [SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe, SubdiffusiveProcess.CoarseGrainingVocab.J, U, A]
  rw [hJ, Homogenization.Book.Ch02.responseJ_eq_coarseMatrices_formula_canonical]
  have hSpd := Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef U A
  have hσ : 0 ≤ Homogenization.vecDot e (Homogenization.matVecMul
      (Homogenization.Book.Ch02.sigmaCoarse U A) e) := by
    have h1 := Homogenization.Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U A e
    have h2 := hPSD _ (Homogenization.Book.Ch02.sigmaStarCoarse_posDef U A) e
    linarith
  have hpe := hpar (Homogenization.Book.Ch02.sigmaStarInvCoarse U A) e
    (Homogenization.matVecMul (Homogenization.Book.Ch02.kappaCoarse U A) e)
  have hm := hPSD _ hSpd (e - Homogenization.matVecMul (Homogenization.Book.Ch02.kappaCoarse U A) e)
  have hb := hbq (Homogenization.Book.Ch02.sigmaCoarse U A) (Homogenization.Book.Ch02.kappaCoarse U A)
    (Homogenization.Book.Ch02.sigmaStarInvCoarse U A) e
  have hbdef : Homogenization.Book.Ch02.bCoarse U A = Homogenization.Book.Ch02.sigmaCoarse U A +
      Homogenization.matTranspose (Homogenization.Book.Ch02.kappaCoarse U A) *
        Homogenization.Book.Ch02.sigmaStarInvCoarse U A * Homogenization.Book.Ch02.kappaCoarse U A := rfl
  have q1 := aux_lem_prefix_limit_g9_cell_moment_quad_le (Homogenization.Book.Ch02.bCoarse U A) e he
  have q2 := aux_lem_prefix_limit_g9_cell_moment_quad_le
    (Homogenization.Book.Ch02.sigmaStarInvCoarse U A) e he
  rw [show Homogenization.matVecMul (Homogenization.Book.Ch02.bCoarse U A) e =
      Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U A +
        Homogenization.matTranspose (Homogenization.Book.Ch02.kappaCoarse U A) *
          Homogenization.Book.Ch02.sigmaStarInvCoarse U A * Homogenization.Book.Ch02.kappaCoarse U A) e
      from rfl, hb] at q1
  have hee : Homogenization.vecDot e e = 1 := he
  have hys := hPSD _ hSpd (Homogenization.matVecMul (Homogenization.Book.Ch02.kappaCoarse U A) e)
  change _ ≤ Homogenization.Book.Ch02.matrixNorm (Homogenization.Book.Ch02.bCoarse U A) +
    Homogenization.Book.Ch02.matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse U A)
  nlinarith [hpe, hm, hσ, q1, q2, hee, hys]

/-- (typed hole, matrix algebra) The normalized scalar probe is dominated by the two one-cube norms:
`J(e,e) = ½ e·σe + ½ (e+κe)·σ_*⁻¹(e+κe) − |e|²` (`responseJ_eq_coarseMatrices_formula_canonical`),
`b = σ + κᵀσ_*⁻¹κ` (`CoarseMatrices.b`), `(x+y)ᵀS(x+y) ≤ 2xᵀSx + 2yᵀSy`, so `J(e,e) ≤ e·be + e·σ_*⁻¹e ≤ |b| + |σ_*⁻¹|`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_probe_le {d : ℕ} [NeZero d]
    (R : Homogenization.TriadicCube d) (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R a 1).toReal ≤
      Homogenization.Book.Ch02.coarseBMatrixNorm R a +
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R a := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
  have h0 : 0 ≤ Homogenization.Book.Ch02.coarseBMatrixNorm R a +
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R a :=
    add_nonneg (Homogenization.Book.Ch02.matrixNorm_nonneg _)
      (Homogenization.Book.Ch02.matrixNorm_nonneg _)
  exact ENNReal.toReal_le_of_le_ofReal h0
    (iSup_le fun e => ENNReal.ofReal_le_ofReal (aux_lem_prefix_limit_g9_cell_moment_probe_pt R a e.1 e.2))

/-- Cells above the cutoff wavelength (`n ≤ K`). Route: chart identity
`lem_as_coarse_shallow_grid_descendant_rechart` + sub-chart a.e. identification + the one-cube vs multiscale
bounds (`…_chart_sigma_le_lam`, `…_chart_b_le_Lam`) + `lem_extension_cell_moment` (k = n ≤ N = K). -/
theorem aux_lem_prefix_limit_g9_cell_moment_low {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta1 A1 : ℝ, 0 < delta1 ∧ 0 ≤ A1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta1 →
      ∀ (_Rm : Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∃ C1 : ℝ, 0 < C1 ∧
      ∀ (n : ℕ) (R : Homogenization.TriadicCube d),
        R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ)) →
        ∀ K : ℕ, n ≤ K →
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C1 * Real.exp (A1 * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseBMatrixNorm R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C1 * Real.exp (A1 * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega) 1).toReal)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * C1 * Real.exp (A1 * M.delta ^ 2 * n)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hqeta : q * (2 * (d : ℝ)) > (d : ℝ) := by nlinarith
  obtain ⟨deltaq, Cd, hdeltaq, hCd, hext⟩ :=
    lem_extension_cell_moment d hd I (3 / 4) (2 * (d : ℝ)) q ⟨by norm_num, by norm_num⟩
      (by positivity) hq hqeta
  have hs : ((3 / 4 : ℝ) - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
  have hw0pos : 0 < Homogenization.Book.Ch02.geometricDiscount (((3 / 4 : ℝ) - 1 / 2) / 4) 2 := by
    unfold Homogenization.Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-(((3 / 4 : ℝ) - 1 / 2) / 4) * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  set c0 : ℝ := (Homogenization.Book.Ch02.geometricDiscount (((3 / 4 : ℝ) - 1 / 2) / 4) 2) ^
    (-(2 / (2 : ℝ))) with hc0
  have hc0pos : 0 < c0 := Real.rpow_pos_of_pos hw0pos _
  refine ⟨deltaq, Cd * (q + q ^ 2), hdeltaq, by positivity, ?_⟩
  intro M hM Rm H hH
  obtain ⟨Cq, hCq, hbound⟩ := hext M Rm H hH hM 0 1 one_pos
  refine ⟨c0 * Cq, mul_pos hc0pos hCq, ?_⟩
  intro n R hR K hnK
  have hsubR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
    Homogenization.openCubeSet_subset_of_mem_descendantsAtScale (show -(n : ℤ) ≤ (Homogenization.originCube d 0).scale by simp [Homogenization.originCube]) hR
  obtain ⟨hscale, hcenter, hsub⟩ := aux_lem_prefix_limit_g9_cell_moment_cell_geom n R hR
  obtain ⟨-, hL⟩ := hbound 1 (fun _ => 0) K n 0 R.index hnK hsub
  set w : SpatialCoordinates d :=
    fun i => (0 : SpatialCoordinates d) i + (3 : ℝ) ^ (-(n : ℤ)) * ((R.index i : ℤ) : ℝ) with hw
  have hρ : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := by positivity
  have hsubset : (centeredCube w ((3 : ℝ) ^ (-(n : ℤ))) hρ : Set (SpatialCoordinates d)) ⊆
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := hsub
  -- the Lam + lam⁻¹ majorant of lem_extension_cell_moment at this cell
  set G : BilateralField d → ℝ := fun om =>
    I.Lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w ((3 : ℝ) ^ (-(n : ℤ)))
        (((3 / 4 : ℝ) - 1 / 2) / 4) 2 +
      (I.lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w ((3 : ℝ) ^ (-(n : ℤ)))
        (((3 / 4 : ℝ) - 1 / 2) / 4) 2)⁻¹ with hG
  -- pointwise: the cell norms are ≤ c0 * G
  have hpt : ∀ om : BilateralField d,
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
          (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) ≤ c0 * G om ∧
      Homogenization.Book.Ch02.coarseBMatrixNorm R
          (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) ≤ c0 * G om := by
    intro om
    have hsig := aux_lem_prefix_limit_g9_cell_moment_chart_sigma_le_lam I 0 1 one_pos
      (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w ((3 : ℝ) ^ (-(n : ℤ))) hρ hsubset
      (((3 / 4 : ℝ) - 1 / 2) / 4) hs
    have hbb := aux_lem_prefix_limit_g9_cell_moment_chart_b_le_Lam I 0 1 one_pos
      (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w ((3 : ℝ) ^ (-(n : ℤ))) hρ hsubset
      (((3 / 4 : ℝ) - 1 / 2) / 4) hs
    have hlampos := I.lam_pos 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
      ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2
    have hLampos := I.Lam_pos 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
      ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2
    -- identify the cell norms with the unit-root norms of the sub-chart
    have hce := aux_lem_prefix_limit_g9_cell_moment_cell_eq I M H om K n R hR
    have hcell_sig : Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
          (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) =
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
            ((3 : ℝ) ^ (-(n : ℤ)))) := hce.1
    have hcell_b : Homogenization.Book.Ch02.coarseBMatrixNorm R
          (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) =
        Homogenization.Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
          (I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
            ((3 : ℝ) ^ (-(n : ℤ)))) := hce.2
    have hinv : 0 < (I.lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
      ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2)⁻¹ := inv_pos.mpr hlampos
    constructor
    · rw [hcell_sig]
      calc _ ≤ c0 * (I.lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
            ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2)⁻¹ := hsig
        _ ≤ c0 * G om := by
          apply mul_le_mul_of_nonneg_left _ hc0pos.le
          simp only [hG]; linarith
    · rw [hcell_b]
      calc _ ≤ c0 * I.Lam 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H om K 0 one_pos) w
            ((3 : ℝ) ^ (-(n : ℤ))) (((3 / 4 : ℝ) - 1 / 2) / 4) 2 := hbb
        _ ≤ c0 * G om := by
          apply mul_le_mul_of_nonneg_left _ hc0pos.le
          simp only [hG]; linarith
  -- the L^q bound for c0 * G
  have hGbound : eLpNorm (fun om => c0 * G om) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (c0 * Cq * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * n)) := by
    rw [mul_assoc]
    exact aux_lem_prefix_limit_g9_cell_moment_eLpNorm_const_mul _ _ c0 _ hc0pos.le G hL
  have hG2bound : eLpNorm (fun om => (2 * c0) * G om) (ENNReal.ofReal q)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (c0 * Cq) * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * n)) := by
    have := aux_lem_prefix_limit_g9_cell_moment_eLpNorm_const_mul _ (ENNReal.ofReal q) (2 * c0)
      (Cq * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * n)) (by positivity) G hL
    calc _ ≤ _ := this
      _ = _ := by ring_nf
  refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  · refine le_trans (eLpNorm_mono_real (by letI : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩; simpa only [aux_lem_prefix_limit_g9_cell_moment_F] using! (probemax_measurable_R_gen hd I M H hH.1 K R hsubR).aestronglyMeasurable) (fun om => ?_)) hG2bound
    have hple := aux_lem_prefix_limit_g9_cell_moment_probe_le R
      (aux_lem_prefix_limit_g9_cell_moment_F I M H K om)
    have hp0 : 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) 1).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hp0]
    have h1 := (hpt om).1
    have h2 := (hpt om).2
    linarith
  · refine le_trans (eLpNorm_mono_real (by simpa only [aux_lem_prefix_limit_g9_cell_moment_F] using! (aux_lem_extension_cell_moment_aesm_coarseS_chart hd I M H hH.1 K 0 1 one_pos 0 1 one_pos subset_rfl R hsubR)) (fun om => ?_)) hGbound
    have := (hpt om).1
    have h0 : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) := Homogenization.Book.Ch02.matrixNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact this
  · refine le_trans (eLpNorm_mono_real (by simpa only [aux_lem_prefix_limit_g9_cell_moment_F] using! (aux_lem_extension_cell_moment_aesm_coarseB_chart hd I M H hH.1 K 0 1 one_pos 0 1 one_pos subset_rfl R hsubR)) (fun om => ?_)) hGbound
    have := (hpt om).2
    have h0 : 0 ≤ Homogenization.Book.Ch02.coarseBMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) := Homogenization.Book.Ch02.matrixNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact this

section
open MeasureTheory TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4 Metric
open scoped ENNReal BigOperators

/-- Native-rate copy of `aux_lem_extension_cell_moment_below_extremes` (its proof verbatim, without the final
conversion `B δ² (N+1) ≤ B δ² k + ε n`): the envelope moment is `C0 e^{B δ² (N+1)}`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_below_native {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p : ℝ) (hp : 0 < p) :
    ∃ C1 : ℝ, 0 < C1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      ∃ C0 : ℝ, 0 < C0 ∧
        ∀ (w : SpatialCoordinates d) (N k : ℕ), k ≤ N →
          (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
        ∀ n : ℕ, N < k + n →
        ∀ Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
            ((Homogenization.originCube d 0).scale - (n : ℤ)),
        ∃ lo hi : BilateralField d → ℝ,
          (∀ om, 0 < lo om ∧ lo om ≤ hi om ∧
            ∀ x ∈ Homogenization.openCubeSet Q,
              lo om ≤ cutoffCoefficient M H om N
                  (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∧
                cutoffCoefficient M H om N
                  (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ≤ hi om) ∧
          eLpNorm (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 +
              4 * (d : ℝ) * (lo om)⁻¹)
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * ((N : ℝ) + 1))) := by
  let B : ℝ := 6 * Real.log 2 + 9 * p *
    (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨C, _hC, hCM⟩ := aux_lem_extension_cell_moment_totalLogNorm_eLpNorm hd
  refine ⟨B, hB, ?_⟩
  intro M H hH z0 R hR
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall z0 R, isCompact_closedBall _ _⟩
  let P : ℝ := Real.log 4 / p + 36 * p * C K * M.delta ^ 2
  let C0 : ℝ := 8 * (d : ℝ) * Real.exp P
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  refine ⟨C0, by dsimp [C0]; positivity, ?_⟩
  intro w N k _hk hcell n hbelow Q hQ
  let z : SpatialCoordinates d :=
    (3 : ℝ) ^ (N : ℤ) • (w + (3 : ℝ) ^ (-(k : ℤ)) • Homogenization.cubeCenter Q)
  let G : BilateralField d → ℝ := fun om =>
    ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
      aux_lem_extension_cell_moment_physicalLogNorm M N z om
  have hG0 : ∀ om, 0 ≤ G om := by
    intro om
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  let lo : BilateralField d → ℝ := fun om => Real.exp (-G om)
  let hi : BilateralField d → ℝ := fun om => Real.exp (G om)
  have hloinv : ∀ om, (lo om)⁻¹ = hi om := by
    intro om
    dsimp [lo, hi]
    rw [Real.exp_neg, inv_inv]
  refine ⟨lo, hi, ?_, ?_⟩
  · intro om
    refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr (by have := hG0 om; linarith), ?_⟩
    intro x hx
    let ξ : SpatialCoordinates d :=
      (3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) • (x - Homogenization.cubeCenter Q)
    have hξ := aux_lem_extension_cell_moment_descendant_micro_mem N k n hbelow Q hQ x hx
    have hid := aux_lem_extension_cell_moment_descendant_micro_identity N k Q w x
    have hxroot : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale (by simp) hQ hx
    have hyroot : (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈
        (centeredCube z0 R hR : Set (SpatialCoordinates d)) :=
      hcell (aux_lem_extension_cell_moment_cellAffine_mem w _ (by positivity) hxroot)
    have hyK : (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) ∈
        (K : Set (SpatialCoordinates d)) := by
      change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 ≤ R
      change dist (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) z0 < R / 2 at hyroot
      linarith
    have hHpt : |H om (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i)| ≤
        ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
      ContinuousMap.norm_coe_le_norm ((H om).restrict (K : Set (SpatialCoordinates d))) ⟨_, hyK⟩
    have hlog := aux_lem_extension_cell_moment_physicalLogNorm_bounds M H N z ξ hξ om
    rw [hid] at hlog
    have hbound : |Real.log (cutoffCoefficient M H om N
        (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i))| ≤ G om :=
      hlog.trans (add_le_add hHpt (le_refl _))
    have hpos : 0 < cutoffCoefficient M H om N
        (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * x i) :=
      mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
    constructor
    · exact (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log hpos)
    · exact (Real.exp_log hpos).symm.trans_le (Real.exp_le_exp.mpr hhi)
  · have henv : ∀ om,
        4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 + 4 * (d : ℝ) * (lo om)⁻¹ ≤
          (8 * (d : ℝ)) * Real.exp (3 * G om) := by
      intro om
      have hh : hi om * hi om ^ 2 = Real.exp (3 * G om) := by
        change Real.exp (G om) * Real.exp (G om) ^ 2 = Real.exp (3 * G om)
        rw [show 3 * G om = G om + G om + G om by ring,
          Real.exp_add (G om + G om) (G om), Real.exp_add (G om) (G om)]
        ring
      have hh' : hi om ≤ Real.exp (3 * G om) :=
        Real.exp_le_exp.mpr (by have := hG0 om; linarith)
      rw [hloinv]
      calc
        _ = 4 * (d : ℝ) * (hi om * hi om ^ 2) + 4 * (d : ℝ) * hi om := by ring
        _ ≤ 4 * (d : ℝ) * Real.exp (3 * G om) + 4 * (d : ℝ) * Real.exp (3 * G om) := by
          rw [hh]
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hh' (by positivity))
        _ = _ := by ring
    have hnorm : eLpNorm (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 +
        4 * (d : ℝ) * (lo om)⁻¹) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (8 * (d : ℝ)) *
          eLpNorm (fun om => Real.exp (3 * G om)) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure := by
      have hGm : Measurable G :=
        (((ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).norm.measurable).comp hH.1).add
          (aux_lem_extension_cell_moment_physicalLogNorm_measurable M N z)
      have hhim := hGm.exp
      have hlom := hGm.neg.exp
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        ((measurable_const.mul hlom.inv).mul (hhim.pow_const 2) |>.add
          (measurable_const.mul hlom.inv)).aestronglyMeasurable
      filter_upwards with om
      rw [Real.norm_of_nonneg (by dsimp [lo, hi]; positivity),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact henv om
    have hGe : eLpNorm (fun om => Real.exp (3 * G om)) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * ((N : ℝ) + 1))) := by
      have h := hCM M H hH K N z 3 p (by norm_num) hp
      convert h using 2 <;> dsimp [G, P, B] <;> congr 1 <;> ring
    calc
      _ ≤ ENNReal.ofReal (8 * (d : ℝ)) *
          ENNReal.ofReal (Real.exp (P + B * M.delta ^ 2 * ((N : ℝ) + 1))) :=
        hnorm.trans (mul_le_mul_right hGe _)
      _ = ENNReal.ofReal (C0 * Real.exp (B * M.delta ^ 2 * ((N : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.exp_add]
        dsimp [C0]
        congr 1
        ring

end

/-- Cells below the cutoff wavelength (`K < n`). Route: Voigt–Reuss averages for a scalar coefficient
(CoarseGraining …/MuOrdering/EllipticConsequences/{SigmaStarInvAveraged,BCoarseAveraged}.lean), Minkowski,
and one-point lognormal moments `E[a_K(x)^{±q}] ≤ C e^{C q² δ² K}` (K < n). -/
theorem aux_lem_prefix_limit_g9_cell_moment_high {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta2 A2 : ℝ, 0 < delta2 ∧ 0 ≤ A2 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta2 →
      ∀ (_Rm : Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (n : ℕ) (R : Homogenization.TriadicCube d),
        R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ)) →
        ∀ K : ℕ, K < n →
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C2 * Real.exp (A2 * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseBMatrixNorm R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C2 * Real.exp (A2 * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
              (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega) 1).toReal)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * C2 * Real.exp (A2 * M.delta ^ 2 * n)) := by
  obtain ⟨C1, hC1, hnat⟩ := aux_lem_prefix_limit_g9_cell_moment_below_native hd q (by linarith)
  refine ⟨1, C1, one_pos, hC1.le, ?_⟩
  intro M _hM _Rm H hH
  obtain ⟨C0, hC0, hb⟩ := hnat M H hH 0 1 one_pos
  refine ⟨C0, hC0, ?_⟩
  intro n R hR K hKn
  have h30 : (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 := by simp
  have hcell : centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) (by positivity) ≤
      centeredCube 0 1 one_pos := by
    have key : ∀ (r : ℝ) (hr : 0 < r), r = 1 →
        centeredCube (0 : SpatialCoordinates d) r hr ≤ centeredCube 0 1 one_pos := by
      rintro r hr rfl; exact le_rfl
    exact key _ _ h30
  have hscale : (Homogenization.originCube d 0).scale - (n : ℤ) = -(n : ℤ) := by
    simp [Homogenization.originCube]
  have hR' : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ)) := by
    rw [hscale]; exact hR
  have hsubR : Homogenization.openCubeSet R ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0) := fun x hx =>
    Homogenization.openCubeSet_subset_of_mem_descendantsAtScale (by simp) hR' hx
  have hb' := hb 0 K 0 (Nat.zero_le K) hcell n (by omega) R hR'
  rcases hb' with ⟨lo, hi, hpt, hmom⟩
  have henv : ∀ om, Homogenization.Book.Ch02.coarseBMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) ≤ 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 ∧
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) ≤ 4 * (d : ℝ) * (lo om)⁻¹ := by
    intro om
    have hbd : ∀ x ∈ Homogenization.openCubeSet R,
        lo om ≤ cutoffCoefficient M H om K (fun i => (0 : SpatialCoordinates d) i + 1 * x i) ∧
          cutoffCoefficient M H om K (fun i => (0 : SpatialCoordinates d) i + 1 * x i) ≤ hi om := by
      intro x hx
      have := (hpt om).2.2 x hx
      simpa using this
    exact aux_lem_extension_cell_moment_chart_envelope I M H om K 0 1 one_pos 0 1 one_pos
      subset_rfl R hsubR (hpt om).1 (hpt om).2.1 hbd
  have hrate : ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * ((K : ℝ) + 1))) ≤
      ENNReal.ofReal (C0 * Real.exp (C1 * M.delta ^ 2 * n)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC0.le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast (show K + 1 ≤ n by omega)
  have hmom' := hmom.trans hrate
  have hlo : ∀ om, 0 ≤ 4 * (d : ℝ) * (lo om)⁻¹ := fun om => by
    have := (hpt om).1; positivity
  have hhi : ∀ om, 0 ≤ 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 := fun om => by
    have := (hpt om).1; positivity
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans (eLpNorm_mono_real (by simpa only [aux_lem_prefix_limit_g9_cell_moment_F] using! (aux_lem_extension_cell_moment_aesm_coarseS_chart hd I M H hH.1 K 0 1 one_pos 0 1 one_pos subset_rfl R hsubR)) (fun om => ?_)) hmom'
    have h0 : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) := Homogenization.Book.Ch02.matrixNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    linarith [(henv om).2, hhi om]
  · refine le_trans (eLpNorm_mono_real (by simpa only [aux_lem_prefix_limit_g9_cell_moment_F] using! (aux_lem_extension_cell_moment_aesm_coarseB_chart hd I M H hH.1 K 0 1 one_pos 0 1 one_pos subset_rfl R hsubR)) (fun om => ?_)) hmom'
    have h0 : 0 ≤ Homogenization.Book.Ch02.coarseBMatrixNorm R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) := Homogenization.Book.Ch02.matrixNorm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    linarith [(henv om).1, hlo om]
  · have h2 := aux_lem_prefix_limit_g9_cell_moment_eLpNorm_const_mul _ (ENNReal.ofReal q) 2
      (C0 * Real.exp (C1 * M.delta ^ 2 * n)) (by norm_num)
      (fun om => 4 * (d : ℝ) * (lo om)⁻¹ * hi om ^ 2 + 4 * (d : ℝ) * (lo om)⁻¹) hmom'
    refine le_trans (eLpNorm_mono_real (by letI : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩; simpa only [aux_lem_prefix_limit_g9_cell_moment_F] using! (probemax_measurable_R_gen hd I M H hH.1 K R hsubR).aestronglyMeasurable) (fun om => ?_)) (h2.trans (le_of_eq (by ring_nf)))
    have hple := aux_lem_prefix_limit_g9_cell_moment_probe_le R
      (aux_lem_prefix_limit_g9_cell_moment_F I M H K om)
    have hp0 : 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (aux_lem_prefix_limit_g9_cell_moment_F I M H K om) 1).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hp0]
    linarith [(henv om).1, (henv om).2, hlo om, hhi om]

/-- (typed hole) `σ_*^{-1}` of any coefficient family has positive operator norm (it is positive definite). -/
theorem aux_lem_prefix_limit_g9_cell_moment_sigmaStarInv_norm_pos {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    0 < Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q a := by
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Homogenization.Book.Ch02.matrixNorm
  rw [norm_pos_iff]
  set A := Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain Q)
    (a.coeffOn Q)
  have hpd : A.PosDef :=
    Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef (Homogenization.Book.Ch02.cubeDomain Q)
      (a.coeffOn Q)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hAne : A ≠ 0 := by
    intro h0
    have hii : 0 < A (⟨0, hd⟩ : Fin d) (⟨0, hd⟩ : Fin d) := by
      simpa using hpd.2 (x := Finsupp.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) (by simp)
    rw [h0] at hii
    simp at hii
  intro h
  refine hAne ?_
  have hinj : Function.Injective (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).injective
  refine hinj ?_
  rw [h, map_zero]

/-- (flash-pending) operator norm of an inverse. -/
theorem aux_lem_prefix_limit_g9_cell_moment_inv_matrixNorm_le {d : ℕ} [NeZero d]
    (A : Homogenization.Mat d) (hA : IsUnit A.det) :
    (Homogenization.Book.Ch02.matrixNorm A)⁻¹ ≤ Homogenization.Book.Ch02.matrixNorm A⁻¹ := by
  rw [Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
    Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  have h1 : (1:ℝ) ≤ Homogenization.Book.Ch02.matrixOperatorNorm A *
      Homogenization.Book.Ch02.matrixOperatorNorm A⁻¹ := by
    have hle := Homogenization.Book.Ch02.matrixOperatorNorm_mul_le A A⁻¹
    rw [Matrix.mul_nonsing_inv A hA, Homogenization.Book.Ch02.matrixOperatorNorm_one] at hle
    exact hle
  have hcpos : 0 < Homogenization.Book.Ch02.matrixOperatorNorm A := by
    rcases lt_or_eq_of_le (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg A) with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at h1
      linarith
  rw [inv_le_iff_one_le_mul₀ hcpos, mul_comm]
  exact h1

/-- (flash-pending) `|σ_*| ≤ |b|`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_sigmaStar_norm_le_b {d : ℕ} [NeZero d]
    (U : Homogenization.Book.Ch02.Domain d) (a : Homogenization.Book.Ch02.CoeffOn U) :
    Homogenization.Book.Ch02.matrixNorm (Homogenization.Book.Ch02.sigmaStarCoarse U a) ≤
      Homogenization.Book.Ch02.matrixNorm (Homogenization.Book.Ch02.bCoarse U a) := by
  have h1 := Homogenization.Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U a
  have h2 := Homogenization.Book.Ch02.sigmaCoarse_le_bCoarse U a
  have htrans : Homogenization.MatLoewnerLE (Homogenization.Book.Ch02.sigmaStarCoarse U a)
      (Homogenization.Book.Ch02.bCoarse U a) := by
    rw [Homogenization.matLoewnerLE_iff] at h1 h2 ⊢
    intro x
    exact le_trans (h1 x) (h2 x)
  exact Homogenization.Book.Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
    (Homogenization.Book.Ch02.sigmaStarCoarse_posDef U a).posSemidef
    (Homogenization.Book.Ch02.bCoarse_posDef U a).posSemidef htrans

/-- (typed hole) `|σ_*^{-1}(Q)|⁻¹ ≤ |b(Q)|`: `|σ_*^{-1}|⁻¹ ≤ |σ_*|` (operator norms, `σ_* = (σ_*^{-1})⁻¹`) and
`σ_* ≤ σ ≤ b` in Loewner order with operator-norm monotonicity on positive semidefinite matrices. -/
theorem aux_lem_prefix_limit_g9_cell_moment_inv_sigmaStarInv_le_b {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q a)⁻¹ ≤
      Homogenization.Book.Ch02.coarseBMatrixNorm Q a := by
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Homogenization.Book.Ch02.coarseBMatrixNorm
  calc (Homogenization.Book.Ch02.matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse
          (Homogenization.Book.Ch02.cubeDomain Q) (a.coeffOn Q)))⁻¹
      ≤ Homogenization.Book.Ch02.matrixNorm (Homogenization.Book.Ch02.sigmaStarInvCoarse
          (Homogenization.Book.Ch02.cubeDomain Q) (a.coeffOn Q))⁻¹ :=
        aux_lem_prefix_limit_g9_cell_moment_inv_matrixNorm_le _
          (Homogenization.Book.Ch02.isUnit_det_sigmaStarInvCoarse _ _)
    _ = Homogenization.Book.Ch02.matrixNorm (Homogenization.Book.Ch02.sigmaStarCoarse
          (Homogenization.Book.Ch02.cubeDomain Q) (a.coeffOn Q)) := rfl
    _ ≤ _ := aux_lem_prefix_limit_g9_cell_moment_sigmaStar_norm_le_b _ _

/-- The root lower bound: `|σ_*^{-1}(Q_0)|⁻¹ ≤ |σ_*(Q_0)|`, bounded in `L^q`. -/
theorem aux_lem_prefix_limit_g9_cell_moment_root {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta4 : ℝ, 0 < delta4 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta4 →
      ∀ (_Rm : Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∃ C4 : ℝ, 0 < C4 ∧
      ∀ K : ℕ,
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          0 < Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
            (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega)) ∧
        eLpNorm (fun omega => (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
              (Homogenization.originCube d 0) (aux_lem_prefix_limit_g9_cell_moment_F I M H K omega))⁻¹)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C4 := by
  obtain ⟨δ1, A1, hδ1, hA1, h1⟩ := aux_lem_prefix_limit_g9_cell_moment_low hd I q hq
  refine ⟨δ1, hδ1, ?_⟩
  intro M hM Rm H hH
  obtain ⟨C1, hC1, b1⟩ := h1 M hM Rm H hH
  refine ⟨C1, hC1, fun K => ⟨Filter.Eventually.of_forall (fun om =>
    aux_lem_prefix_limit_g9_cell_moment_sigmaStarInv_norm_pos _ _), ?_⟩⟩
  have hR0 : Homogenization.originCube d 0 ∈ Homogenization.descendantsAtScale
      (Homogenization.originCube d 0) (-((0 : ℕ) : ℤ)) := by
    have h := Homogenization.descendantsAtScale_self (Homogenization.originCube d 0)
    have h0 : (-((0 : ℕ) : ℤ)) = (Homogenization.originCube d 0).scale := by
      simp [Homogenization.originCube]
    rw [h0, h]
    exact Finset.mem_singleton_self _
  have hb := (b1 0 (Homogenization.originCube d 0) hR0 K (Nat.zero_le K)).2.1
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at hb
  refine le_trans (eLpNorm_mono_real (by simpa only [aux_lem_prefix_limit_g9_cell_moment_F] using! (aux_lem_extension_cell_moment_aesm_coarseS_chart hd I M H hH.1 K 0 1 one_pos 0 1 one_pos subset_rfl (Homogenization.originCube d 0) subset_rfl).aemeasurable.inv.aestronglyMeasurable) (fun om => ?_)) hb
  have hpos := aux_lem_prefix_limit_g9_cell_moment_sigmaStarInv_norm_pos (Homogenization.originCube d 0)
    (aux_lem_prefix_limit_g9_cell_moment_F I M H K om)
  have hle := aux_lem_prefix_limit_g9_cell_moment_inv_sigmaStarInv_le_b (Homogenization.originCube d 0)
    (aux_lem_prefix_limit_g9_cell_moment_F I M H K om)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact hle

/-- Monotonicity used by the assembly. -/
theorem aux_lem_prefix_limit_g9_cell_moment_mono (C C' A A' δ : ℝ) (n : ℕ)
    (hC0 : 0 ≤ C) (hC : C ≤ C') (hA : A ≤ A') :
    ENNReal.ofReal (C * Real.exp (A * δ ^ 2 * n)) ≤ ENNReal.ofReal (C' * Real.exp (A' * δ ^ 2 * n)) := by
  apply ENNReal.ofReal_le_ofReal
  have h1 : Real.exp (A * δ ^ 2 * n) ≤ Real.exp (A' * δ ^ 2 * n) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ δ ^ 2 * (n : ℝ) := by positivity
    nlinarith
  have h2 : 0 < Real.exp (A' * δ ^ 2 * n) := Real.exp_pos _
  calc C * Real.exp (A * δ ^ 2 * n) ≤ C * Real.exp (A' * δ ^ 2 * n) :=
        mul_le_mul_of_nonneg_left h1 hC0
    _ ≤ C' * Real.exp (A' * δ ^ 2 * n) := mul_le_mul_of_nonneg_right hC h2.le



theorem lem_prefix_limit_g9_cell_moment {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_Poincare : Paper.in_poincare d hd I)
    (_Extension : Paper.in_extension d hd I) (_Perturbation : Lane4.SmallPerturbationInput d)
    (_Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 A : ℝ, 0 < delta0 ∧ 0 ≤ A ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      let F : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
        fun K omega => I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
      ∃ C : ℝ, 0 < C ∧
      (∀ (n : ℕ) (R : Homogenization.TriadicCube d),
        R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ)) →
        ∀ K : ℕ,
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C * Real.exp (A * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C * Real.exp (A * M.delta ^ 2 * n)) ∧
          eLpNorm (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C * Real.exp (A * M.delta ^ 2 * n))) ∧
      (∀ K : ℕ,
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          0 < Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
            (F K omega)) ∧
        eLpNorm (fun omega => (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
              (Homogenization.originCube d 0) (F K omega))⁻¹)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) := by
  obtain ⟨δ1, A1, hδ1, hA1, h1⟩ := aux_lem_prefix_limit_g9_cell_moment_low hd I q hq
  obtain ⟨δ2, A2, hδ2, hA2, h2⟩ := aux_lem_prefix_limit_g9_cell_moment_high hd I q hq
  obtain ⟨δ4, hδ4, h4⟩ := aux_lem_prefix_limit_g9_cell_moment_root hd I q hq
  refine ⟨min δ1 (min δ2 δ4), max A1 A2,
    lt_min hδ1 (lt_min hδ2 hδ4), le_max_of_le_left hA1, ?_⟩
  intro M hM Rm _hRm _Sreg _It H hH
  have hM1 : M.delta ≤ δ1 := hM.trans (min_le_left _ _)
  have hM2 : M.delta ≤ δ2 := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hM4 : M.delta ≤ δ4 := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C1, hC1, b1⟩ := h1 M hM1 Rm H hH
  obtain ⟨C2, hC2, b2⟩ := h2 M hM2 Rm H hH
  obtain ⟨C4, hC4, b4⟩ := h4 M hM4 Rm H hH
  set A := max A1 A2 with hAdef
  set C := max (2 * C1) (max (2 * C2) C4) with hCdef
  have hA1A : A1 ≤ A := le_max_left _ _
  have hA2A : A2 ≤ A := le_max_right _ _
  have hC1C2 : 2 * C1 ≤ C := le_max_left _ _
  have hC2C2 : 2 * C2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC1C : C1 ≤ C := le_trans (by linarith) hC1C2
  have hC2C : C2 ≤ C := le_trans (by linarith) hC2C2
  have hC4C : C4 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  intro F
  refine ⟨C, lt_of_lt_of_le hC1 hC1C, ?_⟩
  refine ⟨fun n R hR K => ?_, fun K => ?_⟩
  · rcases le_or_gt n K with hnK | hKn
    · obtain ⟨hs, hb, hp⟩ := b1 n R hR K hnK
      exact ⟨hs.trans (aux_lem_prefix_limit_g9_cell_moment_mono C1 C A1 A M.delta n hC1.le hC1C hA1A),
        hb.trans (aux_lem_prefix_limit_g9_cell_moment_mono C1 C A1 A M.delta n hC1.le hC1C hA1A),
        hp.trans (aux_lem_prefix_limit_g9_cell_moment_mono (2 * C1) C A1 A M.delta n (by positivity)
          hC1C2 hA1A)⟩
    · obtain ⟨hs, hb, hp⟩ := b2 n R hR K hKn
      exact ⟨hs.trans (aux_lem_prefix_limit_g9_cell_moment_mono C2 C A2 A M.delta n hC2.le hC2C hA2A),
        hb.trans (aux_lem_prefix_limit_g9_cell_moment_mono C2 C A2 A M.delta n hC2.le hC2C hA2A),
        hp.trans (aux_lem_prefix_limit_g9_cell_moment_mono (2 * C2) C A2 A M.delta n (by positivity)
          hC2C2 hA2A)⟩
  · obtain ⟨hpos, hinv⟩ := b4 K
    exact ⟨hpos, hinv.trans (ENNReal.ofReal_le_ofReal hC4C)⟩


end Paper
