module

public import SubdiffusiveProcess.Paper.lfgc_potential_lipschitz
public import SubdiffusiveProcess.Paper.lfgc_ratio_ray

@[expose] public section

/-! Below the wavelength the inverse cutoff coefficient is bounded by the cell reference and the summed wavelength scores.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace Paper
attribute [local instance] Classical.propDecidable

/-- The inverse cutoff coefficient at a point of the cell is bounded by the inverse cell reference times an explicit exponential of the wavelength scores. -/
theorem lfgc_sub_reference {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k cbuf : ℕ) (hkN : k ≤ N) (qside : ℝ) (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d)
    (x : SpatialCoordinates d) (hx : x ∈ Metric.ball qcenter (qside / 2))
    (Sig : ℝ)
    (hself : ∀ dword : Fin (N - k) → OddGridIndex d 1,
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside (N - k) dword)).toReal ≤ Sig ∧
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)),
        Dsc ((N : ℤ) - l).toNat
          (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside (N - k) dword) ≠ ⊤) :
    (cutoffCoefficient M H omega N x)⁻¹ ≤
      Real.exp (((d : ℝ) + 2) * Sig + ((N - k : ℕ) : ℝ) * M.delta ^ 2 + (d : ℝ) * Sig + Sig +
        M.delta ^ 2) *
        (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹ := by
  have hxq : ∀ i, |x i - qcenter i| < qside / 2 := by
    intro i
    have hx' : dist x qcenter < qside / 2 := hx
    rw [dist_pi_lt_iff (by positivity)] at hx'
    have := hx' i
    rwa [Real.dist_eq] at this
  obtain ⟨dword, hdw⟩ := aux_in_deterministic_onestep_descendant_exists qcenter qside hqpos x
    (fun i => (hxq i).le) (N - k)
  set w' := descendantCenter 1 qcenter qside (N - k) dword with hw'
  have hside := (aux_in_deterministic_onestep_side_pad k N hkN qside hqside).2
  obtain ⟨hSig, hfin⟩ := hself dword
  have hkNz : (k : ℤ) + ((N - k : ℕ) : ℤ) = (N : ℤ) := by push_cast [Nat.cast_sub hkN]; ring
  have hNmem : (N : ℤ) ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)) := by
    rw [Finset.mem_Icc, hkNz]; constructor <;> omega
  have hD0 : ∀ l, 0 ≤ (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w')).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hDN : (Dsc 0 (((3 : ℝ) ^ N) • w')).toReal ≤ Sig := by
    have h := Finset.single_le_sum (fun l _ => hD0 l) hNmem
    simp only [sub_self, Int.toNat_zero] at h
    exact h.trans hSig
  have hfinN : Dsc 0 (((3 : ℝ) ^ N) • w') ≠ ⊤ := by
    have := hfin _ hNmem
    simpa using this
  have hwq : ∀ i, |w' i - qcenter i| < (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
    intro i
    have h1 := (hdw i).2
    have h2 := descendantSide_pos 1 (N - k) hqpos
    rw [← hqside]; linarith only [h1, h2]
  -- (a) the ray comparison down to level `N`
  have hray := lfgc_ratio_ray M H omega N eta hEta hIR s eps hs
    Fsc Psc Rsc Dsc Zsc goodEvt hPS k qcenter w' hwq
    (Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)))
    (by rw [Finset.mem_Icc, hkNz]; constructor <;> omega) (N : ℤ) (by exact_mod_cast hkN) le_rfl
    (by intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_Icc, hkNz]; constructor <;> omega)
    hfin Sig hSig
  have hcast : (((N : ℤ) - (k : ℤ) : ℤ) : ℝ) = ((N - k : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hkN]; ring
  rw [hcast] at hray
  -- (b) the level-`N` reference versus the coefficient at `x`
  have hcoef := aux_in_deterministic_onestep_sref_N_le_coeff M H omega N x w'
  -- (c) the potential oscillation inside the self cell
  have hosc : |cutoffPotential H omega N x - cutoffPotential H omega N w'| ≤ (d : ℝ) * Sig := by
    have hlip := lfgc_potential_lipschitz H omega N eta hEta hIR
      (Dsc 0 (((3 : ℝ) ^ N) • w')).toReal w' x (by
        intro Z hZ J
        refine aux_in_deterministic_onestep_gradsum_le_draw M s eps eta Fsc Psc Rsc Dsc Zsc
          goodEvt hPS _ hfinN J Z ?_
        have hconv := convex_closedBall (((3 : ℝ) ^ N) • w') (1 / 2 : ℝ)
        refine hconv.segment_subset (Metric.mem_closedBall_self (by norm_num)) ?_ hZ
        rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
        intro i
        rw [Real.dist_eq]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
        have h1 := (hdw i).1
        rw [hside] at h1
        have hN : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
        calc (3 : ℝ) ^ N * |x i - w' i| ≤ (3 : ℝ) ^ N * (((3 : ℝ) ^ N)⁻¹ / 2) :=
              mul_le_mul_of_nonneg_left h1 hN.le
          _ = 1 / 2 := by field_simp)
    have hnorm : (3 : ℝ) ^ N * ‖x - w'‖ ≤ 1 := by
      have : ‖x - w'‖ ≤ ((3 : ℝ) ^ N)⁻¹ / 2 := by
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        intro i
        rw [Pi.sub_apply, Real.norm_eq_abs, ← hside]
        exact (hdw i).1
      have hN : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
      calc (3 : ℝ) ^ N * ‖x - w'‖ ≤ (3 : ℝ) ^ N * (((3 : ℝ) ^ N)⁻¹ / 2) :=
            mul_le_mul_of_nonneg_left this hN.le
        _ ≤ 1 := by field_simp; norm_num
    calc |cutoffPotential H omega N x - cutoffPotential H omega N w'|
        ≤ (d : ℝ) * (Dsc 0 (((3 : ℝ) ^ N) • w')).toReal * ((3 : ℝ) ^ N * ‖x - w'‖) := hlip
      _ ≤ (d : ℝ) * Sig * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hDN (Nat.cast_nonneg d)) hnorm
            (by positivity) (mul_nonneg (Nat.cast_nonneg d) (ENNReal.toReal_nonneg.trans hDN))
      _ = (d : ℝ) * Sig := mul_one _
  -- (d) the finest layer at `w'`
  have hlay : |omega (-(N : ℤ)) w'| ≤ Sig := by
    have h := aux_in_deterministic_onestep_layer0_le_draw M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt
      hPS _ hfinN
    rw [hEta] at h
    have : (((0 : ℕ) : ℤ) - (N : ℤ)) = -(N : ℤ) := by simp only [Nat.cast_zero, zero_sub]
    rw [this, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul] at h
    exact h.trans hDN
  -- assemble
  have hcoef0 := aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N x
  have hsk0 := aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  set Y : ℝ := ((d : ℝ) + 2) * Sig + ((N - k : ℕ) : ℝ) * M.delta ^ 2 + (d : ℝ) * Sig + Sig +
    M.delta ^ 2 with hY
  have hsk : aux_in_deterministic_onestep_sref M H omega N k qcenter ≤
      cutoffCoefficient M H omega N x * Real.exp Y := by
    have hN0 := aux_in_deterministic_onestep_sref_pos M H omega N N w'
    have e1 := hray.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
    refine e1.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hcoef0.le
    apply Real.exp_le_exp.mpr
    rw [hY]
    linarith only [hosc, hlay]
  have hq : aux_in_deterministic_onestep_sref M H omega N k qcenter *
      (cutoffCoefficient M H omega N x)⁻¹ ≤ Real.exp Y := by
    rw [← div_eq_mul_inv, div_le_iff₀ hcoef0]; linarith only [hsk]
  calc (cutoffCoefficient M H omega N x)⁻¹
      = (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹ *
          (aux_in_deterministic_onestep_sref M H omega N k qcenter *
            (cutoffCoefficient M H omega N x)⁻¹) := by field_simp
    _ ≤ (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹ * Real.exp Y :=
        mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hsk0.le)
    _ = Real.exp Y * (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹ := mul_comm _ _


end Paper
