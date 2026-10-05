module

public import SubdiffusiveProcess.Paper.lfgc_sref_point

@[expose] public section

/-! The cell reference is controlled along a ray of finer levels by the summed wavelength scores and the annealed per-level factor.
The quantitative prefix and weak-equation assumptions remain explicit; no good event is assumed. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The reference at level k of a cell is bounded by the reference at a finer level l at a nearby point times exp((d+2)Σ + (l-k)δ²). -/
theorem lfgc_ratio_ray {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k : ℕ) (qcenter w : SpatialCoordinates d)
    (hwq : ∀ i, |w i - qcenter i| < (3 : ℝ) ^ (-(k : ℤ)) / 2)
    (S : Finset ℤ) (hkS : (k : ℤ) ∈ S) (l : ℤ) (hkl : (k : ℤ) ≤ l) (hlN : l ≤ (N : ℤ))
    (hIcoS : Finset.Ico (k : ℤ) l ⊆ S)
    (hfin : ∀ i ∈ S, Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤)
    (Sig : ℝ)
    (hSig : ∑ i ∈ S, (Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal ≤ Sig) :
    aux_in_deterministic_onestep_sref M H omega N k qcenter ≤
      aux_in_deterministic_onestep_sref M H omega N l w *
        Real.exp (((d : ℝ) + 2) * Sig + ((l - k : ℤ) : ℝ) * M.delta ^ 2) := by
  set Dl : ℤ → ℝ := fun i => (Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal with hDl
  have hD0 : ∀ i, 0 ≤ Dl i := fun i => ENNReal.toReal_nonneg
  have hkN : (k : ℤ) ≤ N := hkl.trans hlN
  -- point comparison at level `k`
  set xq : Vec d := fun i => (3 : ℝ) ^ (k : ℤ) * (qcenter i - w i) with hxq
  have hxq_mem : xq ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    rw [Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
    have hw := abs_lt.mp (hwq i)
    have hinv : (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-(k : ℤ)) = 1 := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; simp only [add_neg_cancel, zpow_zero]
    simp only [xq, zpow_zero, mul_one]
    constructor
    · have : (3 : ℝ) ^ (k : ℤ) * (-( (3 : ℝ) ^ (-(k : ℤ)) / 2)) <
          (3 : ℝ) ^ (k : ℤ) * (qcenter i - w i) :=
        mul_lt_mul_of_pos_left (by linarith only [hw.1, hw.2]) h3
      nlinarith only [hinv, this]
    · have : (3 : ℝ) ^ (k : ℤ) * (qcenter i - w i) <
          (3 : ℝ) ^ (k : ℤ) * ((3 : ℝ) ^ (-(k : ℤ)) / 2) :=
        mul_lt_mul_of_pos_left (by linarith only [hw.1, hw.2]) h3
      nlinarith only [hinv, this]
  have hpt := lfgc_sref_point M H omega N (k : ℤ) hkN (Nat.cast_nonneg k) eta hEta hIR
    s eps Fsc Psc Rsc Dsc Zsc goodEvt hPS w (hfin _ hkS) xq hxq_mem
  have hqc : (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * xq i) = qcenter := by
    funext i
    simp only [xq]
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp only [neg_add_cancel, zpow_zero, one_mul, add_sub_cancel]
  rw [hqc] at hpt
  -- level comparison at `w`
  have hlev := aux_in_deterministic_onestep_sref_level_le M H omega N (k : ℤ) l
    (Nat.cast_nonneg k) hkl hlN w
  -- the layer sum
  have hlay : ∑ i ∈ Finset.Ico (k : ℤ) l, |omega (-i) w| ≤ 2 * Sig := by
    calc ∑ i ∈ Finset.Ico (k : ℤ) l, |omega (-i) w|
        ≤ ∑ i ∈ Finset.Ico (k : ℤ) l, 2 * Dl i := by
          apply Finset.sum_le_sum
          intro i hi
          have hil : i < l := (Finset.mem_Ico.mp hi).2
          exact aux_in_deterministic_onestep_omega_le_draw M omega N eta hEta s eps hs
            Fsc Psc Rsc Dsc Zsc goodEvt hPS w i (by omega) (hfin i (hIcoS hi))
      _ = 2 * ∑ i ∈ Finset.Ico (k : ℤ) l, Dl i := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑ i ∈ S, Dl i := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg hIcoS (fun i _ _ => hD0 i)
      _ ≤ 2 * Sig := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hSig
  have hDk : Dl k ≤ Sig :=
    (Finset.single_le_sum (fun i _ => hD0 i) hkS).trans hSig
  -- the disorder term
  have htau : ((l - k : ℤ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
      ((l - k : ℤ) : ℝ) * M.delta ^ 2 := by
    have hlk : (0 : ℝ) ≤ ((l - k : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ l - k := by omega
      exact_mod_cast this
    have ht := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
    have hl2 : Real.log 2 / 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith only [this]
    have : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 :=
      ht.trans (by nlinarith only [hl2, sq_nonneg M.delta])
    exact mul_le_mul_of_nonneg_left this hlk
  have hs0 := aux_in_deterministic_onestep_sref_pos M H omega N l w
  have hsk0 := aux_in_deterministic_onestep_sref_pos M H omega N k w
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hexp1 : (d : ℝ) * Dl k ≤ (d : ℝ) * Sig := mul_le_mul_of_nonneg_left hDk hd0
  calc aux_in_deterministic_onestep_sref M H omega N k qcenter
      ≤ aux_in_deterministic_onestep_sref M H omega N k w * Real.exp ((d : ℝ) * Dl k) := hpt
    _ ≤ (aux_in_deterministic_onestep_sref M H omega N l w *
          Real.exp (((l - k : ℤ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
            ∑ i ∈ Finset.Ico (k : ℤ) l, |omega (-i) w|)) * Real.exp ((d : ℝ) * Dl k) :=
        mul_le_mul_of_nonneg_right hlev (Real.exp_pos _).le
    _ = aux_in_deterministic_onestep_sref M H omega N l w *
          Real.exp ((d : ℝ) * Dl k + (((l - k : ℤ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
            ∑ i ∈ Finset.Ico (k : ℤ) l, |omega (-i) w|)) := by
        rw [Real.exp_add ((d : ℝ) * Dl k)]; ring
    _ ≤ aux_in_deterministic_onestep_sref M H omega N l w *
          Real.exp (((d : ℝ) + 2) * Sig + ((l - k : ℤ) : ℝ) * M.delta ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hs0.le
        apply Real.exp_le_exp.mpr
        nlinarith only [hlay, htau, hexp1]


end SubdiffusiveProcess.Paper
