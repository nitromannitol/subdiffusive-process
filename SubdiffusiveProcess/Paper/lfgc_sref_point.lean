module

public import SubdiffusiveProcess.Paper.in_deterministic

@[expose] public section

/-! The root reference varies by the raw gradient score at nonnegative levels.
Both the actual infrared field and the zero infrared field are covered; negative levels are not asserted here. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The nonnegative-level root reference obeys its exponential spatial comparison for either infrared variant. -/
theorem lfgc_sref_point {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ)) (hl0 : 0 ≤ l)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (s eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (w : SpatialCoordinates d)
    (hD : Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤)
    (x : Vec d) (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    aux_in_deterministic_onestep_sref M H omega N l (fun i => w i + (3 : ℝ) ^ (-l) * x i) ≤
      aux_in_deterministic_onestep_sref M H omega N l w *
        Real.exp ((d : ℝ) * (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w)).toReal)  := by
  rcases hIR with hIR | hH0
  · exact aux_in_deterministic_onestep_sref_point_le M H omega N l hl eta hEta hIR
      s eps Fsc Psc Rsc Dsc Zsc goodEvt hPS w hD x hx
  set m : ℕ := ((N : ℤ) - l).toNat with hm
  set xp : SpatialCoordinates d := fun i => w i + (3 : ℝ) ^ (-l) * x i with hxp
  set z : Vec d := ((3 : ℝ) ^ N) • w with hz
  set T : ℝ := (Dsc m z).toReal with hT
  have hvec : ((3 : ℝ) ^ N) • xp = ((3 : ℝ) ^ m) • x + z := by
    funext i
    simp only [xp, z, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [mul_add, ← mul_assoc, aux_in_deterministic_good_scale_transfer_scale_pow N l hl]
    ring
  set sw := aux_in_deterministic_onestep_sref M H omega N l w with hsw
  set sx := aux_in_deterministic_onestep_sref M H omega N l xp with hsx
  have hsw0 : 0 < sw := aux_in_deterministic_onestep_sref_pos M H omega N l w
  have hsx0 : 0 < sx := aux_in_deterministic_onestep_sref_pos M H omega N l xp
  -- the exponents of the exact identity, as functions of the infrared truncation `K`
  let Sm : ℕ → ℝ := fun K => ∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
    (eta k (((3 : ℝ) ^ m) • x + z) - eta k z)
  let bK : ℕ → ℝ := fun K => (H omega xp - H omega w) -
    ∑ n ∈ Finset.range K, (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) w)
  have hcut0 : 0 < cutoffCoefficient M H omega N xp :=
    aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N xp
  have hac0 : 0 < _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M m eta _
  have hahom : 0 < ahom M m := ahom_pos M m
  -- for every admissible `K`, `sx = sw · exp(Sm K + bK K)`
  have hXK : ∀ K, m ≤ N + K → sx = sw * Real.exp (Sm K + bK K) := by
    intro K hK
    have h1 := aux_in_deterministic_good_scale_transfer_log_identity M H omega N l hl eta hEta
      xp w K hK
    have h2 := aux_in_deterministic_good_scale_transfer_log_identity M H omega N l hl eta hEta
      xp xp K hK
    simp only at h1 h2
    have hE2 : (∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
          (eta k (((3 : ℝ) ^ N) • xp) - eta k (((3 : ℝ) ^ N) • xp))) +
        ((H omega xp - H omega xp) -
          ∑ n ∈ Finset.range K,
            (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) xp)) = 0 := by
      simp only [sub_self, Finset.sum_const_zero, add_zero]
    rw [hE2, Real.exp_zero, mul_one] at h2
    have hE1 : (∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
          (eta k (((3 : ℝ) ^ N) • xp) - eta k (((3 : ℝ) ^ N) • w))) +
        ((H omega xp - H omega w) -
          ∑ n ∈ Finset.range K,
            (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) w)) = Sm K + bK K := by
      simp only [Sm, bK, hvec, z]
    rw [hE1] at h1
    -- h1 : cut / sw = c * exp(...), h2 : cut / sx = c
    have h1' : cutoffCoefficient M H omega N xp / sw =
        (ahom M m)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) *
          Real.exp (Sm K + bK K) := h1
    have h2' : cutoffCoefficient M H omega N xp / sx =
        (ahom M m)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) := h2
    set c : ℝ := (ahom M m)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp)
      with hc
    have hc0 : 0 < c := mul_pos (inv_pos.mpr hahom) hac0
    have e1 : cutoffCoefficient M H omega N xp = c * Real.exp (Sm K + bK K) * sw := by
      rw [div_eq_iff hsw0.ne'] at h1'; exact h1'
    have e2 : cutoffCoefficient M H omega N xp = c * sx := by
      rw [div_eq_iff hsx0.ne'] at h2'; exact h2'
    have : c * sx = c * (sw * Real.exp (Sm K + bK K)) := by rw [← e2, e1]; ring
    exact mul_left_cancel₀ hc0.ne' this
  -- the common exponent and its bound
  set X : ℝ := Sm m + bK m with hXdef
  have hXeq : ∀ K, m ≤ N + K → X = Sm K + bK K := by
    intro K hK
    have h0 := hXK m (by omega)
    have h1 := hXK K (by omega)
    have : sw * Real.exp X = sw * Real.exp (Sm K + bK K) := by rw [← h0, ← h1]
    exact Real.exp_injective (mul_left_cancel₀ hsw0.ne' this)
  have hSB : ∀ K, |Sm K| ≤ (d : ℝ) * T := by
    intro K
    have habs : |Sm K| ≤ ∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
        |eta k (((3 : ℝ) ^ m) • x + z) - eta k z| := Finset.abs_sum_le_sum_abs _ _
    refine habs.trans ?_
    refine (aux_in_deterministic_good_scale_transfer_gradient_block eta m z hx _ _).trans ?_
    exact mul_le_mul_of_nonneg_left
      (aux_in_deterministic_good_scale_transfer_T_bound M s eps eta Fsc Psc Rsc Dsc Zsc
        goodEvt hPS m z hD _ _ (Nat.le_succ m))
      (Nat.cast_nonneg d)
  have hmN : m ≤ N := by dsimp only [m]; omega
  have hXle : |X| ≤ (d : ℝ) * T := by
    rw [hXeq 0 (by omega)]
    simpa only [bK, hH0, Pi.zero_apply, ContinuousMap.zero_apply, sub_self,
      Finset.range_zero, Finset.sum_empty, sub_zero, add_zero] using hSB 0
  rw [hXK m (by omega), ← hXdef]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((le_abs_self X).trans hXle)) hsw0.le


end SubdiffusiveProcess.Paper
