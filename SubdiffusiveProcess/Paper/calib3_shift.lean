module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_HT
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.in_responses

@[expose] public section

/-! Stage 3 (calibration): scale covariance of the infrared-free coefficient.  On a cube of side `3^j` the coefficient `A^0_N`
(`H = 0`, level `N`) equals `c` times the level-`(N+j)` coefficient of the scale-shifted sample `S_j ω` with potential
`HT_j = -∑_{i<j} ω(-i)` (`calib3_HT`); the deterministic constant `c` is bounded above and below by `exp(j|τ²|)`.
This is the rescaling of the proof of `mfd:prop-growth`  for `H = 0`, where the infrared event
`IRShiftAt H j ω` of `prop_growth_large_root` is replaced by the exact identity of the potentials. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The deterministic constant of the scale shift for `H = 0`: `A^0_N(3^j y) = c · A^{HT_j}_{N+j}(S_jω)(y)`. -/
def aux_calib3_shift_const (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j N : ℕ) : ℝ :=
  SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
    Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_calib3_shift_potential (om : BilateralField d) (j N : ℕ) (y : SpatialCoordinates d) :
    cutoffPotential (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N (((3 : ℝ) ^ j) • y) =
      cutoffPotential (calib3_HT d j) (aux_prop_growth_large_root_scaleShift j om) (N + j) y := by
  unfold cutoffPotential calib3_HT
  have hsplit : (∑ i ∈ Finset.range (N + j + 1), aux_prop_growth_large_root_scaleShift j om (-(Int.ofNat i)) y) =
      (∑ i ∈ Finset.range j, aux_prop_growth_large_root_scaleShift j om (-(Int.ofNat i)) y) +
        ∑ k ∈ Finset.range (N + 1), om (-(Int.ofNat k)) (((3 : ℝ) ^ j) • y) := by
    rw [show N + j + 1 = j + (N + 1) by omega, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [aux_prop_growth_large_root_scaleShift_apply]
    congr 2
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [hsplit]
  simp only [ContinuousMap.neg_apply, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.zero_apply]
  ring

theorem aux_calib3_shift_const_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (j N : ℕ) : 0 < aux_calib3_shift_const M j N := by
  unfold aux_calib3_shift_const
  exact mul_pos (div_pos (aux_prop_growth_large_root_ahom_pos_of M Rm (N + j))
    (aux_prop_growth_large_root_ahom_pos_of M Rm N)) (Real.exp_pos _)

theorem aux_calib3_shift_const_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (j N : ℕ) (hj : 0 < j) :
    aux_calib3_shift_const M j N ≤ Real.exp ((j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P|) := by
  have hord : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    (Rm.ahom_ordering N (N + j) (by omega)).1
  have hratio : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤ 1 :=
    (div_le_one (aux_prop_growth_large_root_ahom_pos_of M Rm N)).2 hord
  unfold aux_calib3_shift_const
  refine le_trans (mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le) ?_
  rw [one_mul]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg j))

theorem aux_calib3_shift_const_inv_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (j N : ℕ) (hj : 0 < j) :
    (aux_calib3_shift_const M j N)⁻¹ ≤ Real.exp ((j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P|) := by
  have hord := (Rm.ahom_ordering N (N + j) (by omega)).2
  have hpN := aux_prop_growth_large_root_ahom_pos_of M Rm N
  have hpNj := aux_prop_growth_large_root_ahom_pos_of M Rm (N + j)
  have hcast : ((N + j : ℕ) : ℝ) - (N : ℝ) = j := by push_cast; ring
  rw [hcast] at hord
  unfold aux_calib3_shift_const
  rw [mul_inv, inv_div, ← Real.exp_neg]
  calc SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) *
        Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
      ≤ Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (j : ℝ)) *
        Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        rw [div_le_iff₀ hpNj]
        exact hord
    _ = Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P|) := by
        apply Real.exp_le_exp.2
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg j)

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_calib3_shift_coefficient
    [_portSection0 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection1 : BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (om : BilateralField d) (j N : ℕ)
    (hpos : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j)) (y : SpatialCoordinates d) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N (((3 : ℝ) ^ j) • y) =
      aux_calib3_shift_const M j N *
        cutoffCoefficient M (calib3_HT d j) (aux_prop_growth_large_root_scaleShift j om) (N + j) y := by
  unfold cutoffCoefficient aux_calib3_shift_const
  rw [aux_calib3_shift_potential om j N y]
  have hne : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) ≠ 0 := hpos.ne'
  have hexp : Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
      Real.exp (cutoffPotential (calib3_HT d j) (aux_prop_growth_large_root_scaleShift j om) (N + j) y -
        (((N + j : ℕ) : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
      Real.exp (cutoffPotential (calib3_HT d j) (aux_prop_growth_large_root_scaleShift j om) (N + j) y -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [← hexp]
  field_simp

/-- **Scale covariance of `A^0_N` (Stage 3).**  For the infrared-free coefficient (`H = 0`): `A^0_N(3^j y) = c · A^{HT_j}_{N+j}(S_j ω)(y)`
with `0 < c` and `c, c⁻¹ ≤ exp(j |τ²|)` (deterministic). -/
theorem calib3_shift (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (j N : ℕ) (hj : 0 < j)
    (om : BilateralField d) (y : SpatialCoordinates d) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N (((3 : ℝ) ^ j) • y) =
      aux_calib3_shift_const M j N *
        cutoffCoefficient M (calib3_HT d j) (aux_prop_growth_large_root_scaleShift j om) (N + j) y ∧
      0 < aux_calib3_shift_const M j N ∧
      aux_calib3_shift_const M j N ≤ Real.exp ((j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P|) ∧
      (aux_calib3_shift_const M j N)⁻¹ ≤ Real.exp ((j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P|) :=
  ⟨aux_calib3_shift_coefficient M om j N (aux_prop_growth_large_root_ahom_pos_of M Rm (N + j)) y,
    aux_calib3_shift_const_pos M Rm j N, aux_calib3_shift_const_le M Rm j N hj,
    aux_calib3_shift_const_inv_le M Rm j N hj⟩

end SubdiffusiveProcess.Paper
