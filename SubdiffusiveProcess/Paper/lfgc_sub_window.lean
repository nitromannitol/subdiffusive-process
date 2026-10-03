module

public import SubdiffusiveProcess.Paper.lfgc_sub_oscillation

@[expose] public section

/-! Below the wavelength the cutoff coefficient has small relative oscillation on subcells, controlled by the padded wavelength score.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper
attribute [local instance] Classical.propDecidable

/-- The cutoff coefficient varies by a relative factor at most 3θ on a subcell of side r when d·G₀·3^N r/2 ≤ θ ≤ 1. -/
theorem lfgc_sub_window {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (s eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k : ℕ) (hkN : k ≤ N) (qside : ℝ) (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d)
    (G0 : ℝ) (hG0 : 0 ≤ G0)
    (hpad : ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) •
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤ G0)
    (x : SpatialCoordinates d) (hxq : ∀ i, |x i - qcenter i| < qside / 2)
    (r : ℝ) (hr0 : 0 < r) (hrq : r ≤ qside)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθr : (d : ℝ) * G0 * ((3 : ℝ) ^ N * r) / 2 ≤ θ) :
    ∀ v ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
      |cutoffCoefficient M H omega N (fun i => x i + r * v i) /
          cutoffCoefficient M H omega N x - 1| ≤ 3 * θ ∧
      |cutoffCoefficient M H omega N x /
          cutoffCoefficient M H omega N (fun i => x i + r * v i) - 1| ≤ 3 * θ := by
  intro v hv
  set y : SpatialCoordinates d := fun i => x i + r * v i with hy
  have hvi := aux_in_deterministic_good_scale_transfer_mem_unit_root hv
  have hyx : ‖y - x‖ ≤ r / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simp only [hy, Pi.sub_apply, add_sub_cancel_left, Real.norm_eq_abs, abs_mul,
      abs_of_pos hr0]
    have h1 := hvi i
    have h2 : |v i| ≤ 1 / 2 := abs_le.mpr ⟨by linarith only [h1.1], by linarith only [h1.2]⟩
    calc r * |v i| ≤ r * (1 / 2) := mul_le_mul_of_nonneg_left h2 hr0.le
      _ = r / 2 := by ring
  have hyq : ∀ i, |y i - qcenter i| ≤ qside := by
    intro i
    have h1 : |y i - x i| ≤ r / 2 := by
      have := (pi_norm_le_iff_of_nonneg (by positivity)).mp hyx i
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using this
    calc |y i - qcenter i| ≤ |y i - x i| + |x i - qcenter i| := abs_sub_le _ _ _
      _ ≤ r / 2 + qside / 2 := add_le_add h1 (hxq i).le
      _ ≤ qside := by linarith only [hrq]
  have hosc := lfgc_sub_oscillation M H omega N eta hEta hIR s eps
    Fsc Psc Rsc Dsc Zsc goodEvt hPS k hkN qside hqpos hqside qcenter G0 hpad x y
    (fun i => (hxq i).le.trans (by linarith only [hqpos])) hyq
  have hΔ : |cutoffPotential H omega N y - cutoffPotential H omega N x| ≤ θ := by
    refine hosc.trans ?_
    have h1 : (d : ℝ) * G0 * ((3 : ℝ) ^ N * ‖y - x‖) ≤ (d : ℝ) * G0 * ((3 : ℝ) ^ N * (r / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyx (by positivity)) (by positivity)
    have h2 : (d : ℝ) * G0 * ((3 : ℝ) ^ N * (r / 2)) = (d : ℝ) * G0 * ((3 : ℝ) ^ N * r) / 2 := by
      ring
    linarith only [h1, h2, hθr]
  set t := cutoffPotential H omega N y - cutoffPotential H omega N x with ht
  have he : Real.exp |t| ≤ 3 := by
    have : Real.exp |t| ≤ Real.exp 1 := Real.exp_le_exp.mpr (hΔ.trans hθ1)
    have h2 := Real.exp_one_lt_d9
    linarith only [this, h2]
  have hb : ∀ t' : ℝ, |t'| = |t| → |Real.exp t' - 1| ≤ 3 * θ := by
    intro t' ht'
    refine (aux_in_deterministic_good_scale_transfer_abs_exp_sub_one t').trans ?_
    rw [ht']
    calc |t| * Real.exp |t| ≤ θ * 3 :=
          mul_le_mul hΔ he (Real.exp_pos _).le hθ0
      _ = 3 * θ := mul_comm _ _
  constructor
  · rw [aux_in_deterministic_onestep_coeff_ratio]; exact hb t rfl
  · rw [aux_in_deterministic_onestep_coeff_ratio, show cutoffPotential H omega N x -
        cutoffPotential H omega N y = -t by rw [ht]; ring]
    exact hb (-t) (abs_neg t)


end Paper
