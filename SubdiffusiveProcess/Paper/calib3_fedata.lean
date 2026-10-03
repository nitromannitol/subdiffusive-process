module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_HT
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_responses

@[expose] public section

/-! Stage 3 (calibration): the Section-6 frame data of the top-block-removed coefficient on the unit cube: at frame `N + j` the
coefficient `A^{HT_j}_{N+j}` equals `c` times the stationary coefficient `a_N` (FE level `N`) of the `(N+j)`-relabelled field,
and the reference `c · refAvg` is the deterministic `ahom_N/ahom_{N+j} · e^{-jτ²}`, bounded by `e^{j|τ²|}`.
This is the input `hFEd` of `calib3_energy_core`, `calib3_macro_unit`, `calib3_holder_unit`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Frame identity with the explicit constant `c = ahom_{N+j}⁻¹ e^{-jτ²}` (paper lines 605-617 for `H = 0`). -/
theorem aux_calib3_fedata_identity {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M)
    (om : BilateralField d) (j N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1)
    (hR : (0 : ℝ) < 3 ^ (N + j)) :
    ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z h1).val y =
          ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))⁻¹ * Real.exp (-((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))) *
            (Sreg.cutoffOn N (aux_aux_macro_energy_recurrence_relabel (N + j) om)
            ((3 : ℝ) ^ (N + j) • z) (3 ^ (N + j)) hR).val ((3 : ℝ) ^ (N + j) • y) := by
  have hsr : (0 : ℝ) < (3 : ℝ) ^ (N + j) * 1 := by positivity
  have hBae := aux_prop_growth_macro_energy_cutoffOn_scaled Sreg N
      (aux_aux_macro_energy_recurrence_relabel (N + j) om)
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (N + j)) z h1 hsr
  filter_upwards [aux_prop_growth_macro_energy_coeff_ae M (calib3_HT d j) om (N + j) z h1,
    hBae] with y hA hB
  rw [hA]
  have hcong := aux_aux_macro_energy_recurrence_cutoffOn_congr Sreg N
    (rfl : aux_aux_macro_energy_recurrence_relabel (N + j) om =
      aux_aux_macro_energy_recurrence_relabel (N + j) om)
    (rfl : (3 : ℝ) ^ (N + j) • z = (3 : ℝ) ^ (N + j) • z)
    (by rw [mul_one])
    hR hsr
    (rfl : (3 : ℝ) ^ (N + j) • y = (3 : ℝ) ^ (N + j) • y)
  rw [hcong, hB]
  simp only [aux_aux_macro_energy_recurrence_relabel_apply]
  unfold SubdiffusiveProcess.cutoffCoefficient SubdiffusiveProcess.cutoffPotential calib3_HT
  simp only [ContinuousMap.neg_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  have hL : -(∑ i ∈ Finset.range j, (om (-(Int.ofNat i))) y) +
        (∑ i ∈ Finset.range (N + j + 1), (om (-(Int.ofNat i))) y) -
        (((N + j : ℕ) : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
      -((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
        ((∑ i ∈ Finset.range (N + 1), (om ((i : ℤ) - ((N + j : ℕ) : ℤ))) y) -
          (((N : ℕ) : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    have hsplit : (∑ i ∈ Finset.range (N + j + 1), (om (-(Int.ofNat i))) y)
        = (∑ i ∈ Finset.range j, (om (-(Int.ofNat i))) y) +
          ∑ k ∈ Finset.range (N + 1), (om (-(Int.ofNat (j + k)))) y := by
      rw [show N + j + 1 = j + (N + 1) by omega, Finset.sum_range_add]
    have hreflect : (∑ k ∈ Finset.range (N + 1), (om (-(Int.ofNat (j + k)))) y)
        = ∑ i ∈ Finset.range (N + 1), (om ((i : ℤ) - ((N + j : ℕ) : ℤ))) y := by
      rw [← Finset.sum_range_reflect (fun i : ℕ => (om ((i : ℤ) - ((N + j : ℕ) : ℤ))) y) (N + 1)]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show N + 1 - 1 - k = N - k by omega]
      congr 1
      congr 1
      rw [Nat.cast_sub hk', Int.ofNat_eq_natCast]
      push_cast
      ring
    rw [hsplit, hreflect]
    push_cast
    ring
  rw [hL, mul_assoc, ← Real.exp_add]

/-- The reference average is the constant `ahom_{Lc}` when `Lc ≤ m`. -/
theorem aux_calib3_fedata_refAvg {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M)
    (Lc m : ℕ) (hLm : Lc ≤ m) (y : SpatialCoordinates d) (om : BilateralField d) :
    Sreg.refAvg Lc m y om = SubdiffusiveProcess.CoarseGrainingVocab.ahom M Lc := by
  have hR : (0 : ℝ) < 3 ^ m := by positivity
  rw [Sreg.refAvg_eq Lc m y om hR]
  have hmin : min m Lc = Lc := min_eq_right hLm
  rw [hmin]
  have hminR : min (m:ℝ) (Lc:ℝ) = (Lc:ℝ) := by rw [← Nat.cast_min, hmin]
  rw [hminR]
  simp only [sub_self, zero_mul, Real.exp_zero, mul_one]
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, inv_mul_cancel_left₀ (ne_of_gt (centeredCube_volume_pos y hR))]

/-- The reference constant `c · ahom_N` and its inverse are at most `2 e^{j|τ²|}`. -/
theorem aux_calib3_fedata_bounds {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (j N : ℕ) (hj : 0 < j) :
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))⁻¹ * Real.exp (-((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤ 2 * Real.exp ((j : ℝ) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ∧
      ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))⁻¹ * Real.exp (-((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ ≤ 2 * Real.exp ((j : ℝ) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) := by
  set T : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P with hT
  set aN : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M N with haN
  set aNj : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) with haNj
  have hpN : 0 < aN := by rw [haN]; exact aux_prop_growth_large_root_ahom_pos_of M Rm N
  have hpNj : 0 < aNj := by rw [haNj]; exact aux_prop_growth_large_root_ahom_pos_of M Rm (N + j)
  have hord := Rm.ahom_ordering N (N + j) (by omega)
  rw [← hT, ← haN, ← haNj] at hord
  obtain ⟨ha, hb⟩ := hord
  have hcast : ((N + j : ℕ) : ℝ) - (N : ℝ) = (j : ℝ) := by push_cast; ring
  rw [hcast] at hb
  have hr2 : aN / aNj ≤ Real.exp (2 * T * (j:ℝ)) := by
    rw [div_le_iff₀ hpNj]; exact hb
  have hr1 : 1 ≤ aN / aNj := by
    rw [one_le_div hpNj]; exact ha
  have hfirst : aNj⁻¹ * Real.exp (-((j:ℝ)*T)) * aN ≤ 2 * Real.exp ((j:ℝ)*|T|) := by
    have hk_eq : aNj⁻¹ * Real.exp (-((j:ℝ)*T)) * aN = (aN/aNj) * Real.exp (-((j:ℝ)*T)) := by
      rw [div_eq_mul_inv]; ring
    rw [hk_eq]
    calc (aN/aNj) * Real.exp (-((j:ℝ)*T))
        ≤ Real.exp (2*T*(j:ℝ)) * Real.exp (-((j:ℝ)*T)) :=
          mul_le_mul_of_nonneg_right hr2 (le_of_lt (Real.exp_pos _))
      _ = Real.exp (2*T*(j:ℝ) + -((j:ℝ)*T)) := by rw [← Real.exp_add]
      _ = Real.exp ((j:ℝ)*T) := by congr 1; ring
      _ ≤ Real.exp ((j:ℝ)*|T|) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (le_abs_self T) (by positivity)
      _ ≤ 2 * Real.exp ((j:ℝ)*|T|) := le_mul_of_one_le_left (le_of_lt (Real.exp_pos _)) (by norm_num)
  have hsecond : (aNj⁻¹ * Real.exp (-((j:ℝ)*T)) * aN)⁻¹ ≤ 2 * Real.exp ((j:ℝ)*|T|) := by
    have hexpinv : (Real.exp (-((j:ℝ)*T)))⁻¹ = Real.exp ((j:ℝ)*T) := by
      rw [Real.exp_neg, inv_inv]
    have hk_eq : (aNj⁻¹ * Real.exp (-((j:ℝ)*T)) * aN)⁻¹ = (aNj/aN) * Real.exp ((j:ℝ)*T) := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hexpinv, div_eq_mul_inv]
      ring
    rw [hk_eq]
    have hs : aNj/aN ≤ 1 := by rw [div_le_one hpN]; exact ha
    calc (aNj/aN) * Real.exp ((j:ℝ)*T)
        ≤ 1 * Real.exp ((j:ℝ)*T) := mul_le_mul_of_nonneg_right hs (le_of_lt (Real.exp_pos _))
      _ = Real.exp ((j:ℝ)*T) := one_mul _
      _ ≤ Real.exp ((j:ℝ)*|T|) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (le_abs_self T) (by positivity)
      _ ≤ 2 * Real.exp ((j:ℝ)*|T|) := le_mul_of_one_le_left (le_of_lt (Real.exp_pos _)) (by norm_num)
  exact ⟨hfirst, hsecond⟩

/-- **Frame data of the top-block-removed coefficient** on the unit cube. -/
theorem calib3_fedata {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (Sreg : in_6_16 d M) (om : BilateralField d) (j N : ℕ) (hj : 0 < j) (z : SpatialCoordinates d)
    (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ (N + j)) :
    ∃ cFin : ℝ, 0 < cFin ∧
      (∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z h1).val y =
          cFin * (Sreg.cutoffOn N (aux_aux_macro_energy_recurrence_relabel (N + j) om)
            ((3 : ℝ) ^ (N + j) • z) (3 ^ (N + j)) hR).val ((3 : ℝ) ^ (N + j) • y)) ∧
      cFin * Sreg.refAvg N (N + j) ((3 : ℝ) ^ (N + j) • z) (aux_aux_macro_energy_recurrence_relabel (N + j) om) ≤
        2 * Real.exp ((j : ℝ) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ∧
      (cFin * Sreg.refAvg N (N + j) ((3 : ℝ) ^ (N + j) • z) (aux_aux_macro_energy_recurrence_relabel (N + j) om))⁻¹ ≤
        2 * Real.exp ((j : ℝ) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) := by
  refine ⟨(SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))⁻¹ * Real.exp (-((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)),
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + j))) (Real.exp_pos _),
    aux_calib3_fedata_identity Sreg om j N z h1 hR, ?_⟩
  rw [aux_calib3_fedata_refAvg Sreg N (N + j) (Nat.le_add_right N j)]
  exact aux_calib3_fedata_bounds M Rm j N hj

end Paper
