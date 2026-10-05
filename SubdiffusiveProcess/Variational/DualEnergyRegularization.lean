module

public import SubdiffusiveProcess.Variational.DualEnergy
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter Set
open scoped Topology

/-! Regularization of the literal extended dual energy on a real Hilbert space. -/
namespace SubdiffusiveProcess

/-- Vanishing positive penalties recover the entire extended dual energy. -/
theorem tendsto_regularized_quadraticDual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H) (u : H) :
    Tendsto (fun n : ℕ => ⨆ f : H,
      ((2 * inner ℝ f u - inner ℝ f (G f) - (1 / (n + 1 : ℝ)) * ‖f‖ ^ 2 : ℝ) : EReal))
      atTop (𝓝 (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal))) := by
  let q : ℕ → H → EReal := fun n f =>
    ((2 * inner ℝ f u - inner ℝ f (G f) - (1 / (n + 1 : ℝ)) * ‖f‖ ^ 2 : ℝ) : EReal)
  have hq_mono : ∀ f : H, Monotone (fun n => q n f) := by
    intro f n m hnm
    rw [EReal.coe_le_coe_iff]
    have hcast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hfrac : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hpos hcast
    nlinarith [sq_nonneg ‖f‖]
  have hq_tendsto : ∀ f : H, Tendsto (fun n => q n f) atTop
      (𝓝 ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) := by
    intro f
    rw [EReal.tendsto_coe]
    have hzero : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) * ‖f‖ ^ 2) atTop (𝓝 0) := by
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (‖f‖ ^ 2)
    simpa using tendsto_const_nhds.sub hzero
  have hq_iSup : ∀ f : H, (⨆ n : ℕ, q n f) =
      ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) := by
    intro f
    exact iSup_eq_of_tendsto (hq_mono f) (hq_tendsto f)
  have hmono : Monotone (fun n : ℕ => ⨆ f : H, q n f) := by
    intro n m hnm
    exact iSup_mono fun f => hq_mono f hnm
  change Tendsto (fun n : ℕ => ⨆ f : H, q n f) atTop _
  convert tendsto_atTop_iSup hmono using 1
  rw [iSup_comm]
  simp_rw [hq_iSup]

/-- The actual positive-shift inverse attains the penalized variational formula. -/
theorem regularized_quadraticDual_eq_pairing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hR : (G + ε • ContinuousLinearMap.id ℝ H).comp R = ContinuousLinearMap.id ℝ H)
    (u : H) :
    (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) - ε * ‖f‖ ^ 2 : ℝ) : EReal)) =
      ((inner ℝ u (R u) : ℝ) : EReal) := by
  let A : H →L[ℝ] H := G + ε • ContinuousLinearMap.id ℝ H
  have hAq (f : H) : inner ℝ f (A f) = inner ℝ f (G f) + ε * ‖f‖ ^ 2 := by
    simp only [A, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have hAsym : ∀ x y : H, inner ℝ (A x) y = inner ℝ x (A y) := by
    intro x y
    simp only [A, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hsym]
  have hApos (x : H) : 0 ≤ inner ℝ x (A x) := by
    rw [hAq]
    exact add_nonneg (hpos x) (mul_nonneg hε (sq_nonneg _))
  have hAR : A (R u) = u := by
    exact congrArg (fun F : H →L[ℝ] H => F u) hR
  calc
    (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) - ε * ‖f‖ ^ 2 : ℝ) : EReal)) =
        ⨆ f : H, ((2 * inner ℝ f (A (R u)) - inner ℝ f (A f) : ℝ) : EReal) := by
      apply iSup_congr
      intro f
      rw [hAR, hAq, sub_add_eq_sub_sub]
    _ = ((inner ℝ (R u) (A (R u)) : ℝ) : EReal) :=
      iSup_quadraticDual_apply_image A hAsym hApos (R u)
    _ = ((inner ℝ u (R u) : ℝ) : EReal) := by
      rw [hAR, real_inner_comm]

end SubdiffusiveProcess
