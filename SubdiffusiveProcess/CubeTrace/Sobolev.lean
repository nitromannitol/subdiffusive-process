module

public import Mathlib
public import Homogenization.Sobolev.H1.Definitions
public import SubdiffusiveProcess.CubeTrace.Scale
public import SubdiffusiveProcess.CubeTrace.WeakDeriv

@[expose] public section

/-!
# Cube trace extension: pointwise regularity of `b` and the `H¹(Q)` element

A function `b` that is `C²` on the open cube with `|∇b| ≤ M m^{β-1}`, `|D²b| ≤ M m^{β-2}` (and
bounded) has continuous, mean-value controlled, square-integrable gradient components, and is an
`H¹(Q)` function with the classical gradient.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- The pointwise regularity package. -/
structure CTReg [NeZero d] (z : Fin d → ℝ) (β M : ℝ) (b : (Fin d → ℝ) → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 2 b (ctQ z)
  grad_bound : ∀ x ∈ ctQ z, ∀ j : Fin d, |fderiv ℝ b x (Pi.single j 1)| ≤ M * ctM z x ^ (β - 1)
  hess_bound : ∀ x ∈ ctQ z, ∀ j l : Fin d,
    |fderiv ℝ (fun y => fderiv ℝ b y (Pi.single j 1)) x (Pi.single l 1)| ≤ M * ctM z x ^ (β - 2)
  bdd : ∃ B : ℝ, ∀ x ∈ ctQ z, |b x| ≤ B

/-- The gradient component `∂_j b` is continuous on the cube. -/
theorem CTReg.continuousOn_grad [NeZero d] {z : Fin d → ℝ} {β M : ℝ}
    {b : (Fin d → ℝ) → ℝ} (h : CTReg z β M b) (j : Fin d) :
    ContinuousOn (fun x => fderiv ℝ b x (Pi.single j 1)) (ctQ z) :=
  (h.contDiffOn.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).clm_apply
    continuousOn_const

/-- The operator norm of a functional on `ℝ^d` is at most the sum of its values on the basis. -/
theorem ct_opNorm_le (L : (Fin d → ℝ) →L[ℝ] ℝ) : ‖L‖ ≤ ∑ l : Fin d, |L (Pi.single l 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun l _ => abs_nonneg _)
    fun v => ?_
  have hv : L v = ∑ l : Fin d, v l * L (Pi.single l 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : (Pi.single l (v l) : Fin d → ℝ) = v l • (Pi.single l (1 : ℝ) : Fin d → ℝ) := by
      ext k
      by_cases hk : k = l
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [this, map_smul, smul_eq_mul]
  rw [Real.norm_eq_abs, hv]
  calc |∑ l : Fin d, v l * L (Pi.single l 1)| ≤ ∑ l : Fin d, |v l * L (Pi.single l 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin d, ‖v‖ * |L (Pi.single l 1)| := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v l) (abs_nonneg _)
    _ = (∑ l : Fin d, |L (Pi.single l 1)|) * ‖v‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- Mean value: the gradient components are Lipschitz on the sup-ball of radius `m(x)/2`. -/
theorem CTReg.lipschitz_near [NeZero d] {z : Fin d → ℝ} {β M : ℝ}
    {b : (Fin d → ℝ) → ℝ} (h : CTReg z β M b) (hM : 0 ≤ M) (hβ : β ≤ 2) (j : Fin d)
    {x : Fin d → ℝ} (hx : x ∈ ctQ z) {y : Fin d → ℝ}
    (hy : ‖y - x‖ < ctM z x / 2) :
    |fderiv ℝ b x (Pi.single j 1) - fderiv ℝ b y (Pi.single j 1)| ≤
      ((d : ℝ) * 2 ^ (2 - β) * M) * ctM z x ^ (β - 2) * ‖x - y‖ := by
  have hxm := ctM_pos hx
  set F : (Fin d → ℝ) → ℝ := fun w => fderiv ℝ b w (Pi.single j 1) with hF
  set s : Set (Fin d → ℝ) := Metric.ball x (ctM z x / 2) with hs
  have hsQ : ∀ w ∈ s, w ∈ ctQ z := by
    intro w hw
    refine mem_ctQ_of_dist_lt_ctM hx ?_
    rw [hs, mem_ball_iff_norm] at hw
    linarith
  have hb1 : ContDiffOn ℝ 1 (fderiv ℝ b) (ctQ z) :=
    h.contDiffOn.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hF1 : ContDiffOn ℝ 1 F (ctQ z) := hb1.clm_apply contDiffOn_const
  have hFd : ∀ w ∈ s, DifferentiableAt ℝ F w := fun w hw =>
    (hF1.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds (hsQ w hw))
  have hCnn : 0 ≤ (d : ℝ) * 2 ^ (2 - β) * M * ctM z x ^ (β - 2) := by positivity
  have hbound : ∀ w ∈ s, ‖fderiv ℝ F w‖ ≤ (d : ℝ) * 2 ^ (2 - β) * M * ctM z x ^ (β - 2) := by
    intro w hw
    have hwQ := hsQ w hw
    have hmw : ctM z x / 2 ≤ ctM z w := by
      have h1 := abs_ctM_sub_le hx hwQ
      have h2 : ‖x - w‖ < ctM z x / 2 := by
        rw [hs, mem_ball_iff_norm] at hw
        rwa [norm_sub_rev]
      have h3 := (abs_le.1 h1).2
      linarith
    have hpow : ctM z w ^ (β - 2) ≤ 2 ^ (2 - β) * ctM z x ^ (β - 2) := by
      calc ctM z w ^ (β - 2) ≤ (ctM z x / 2) ^ (β - 2) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hmw (by linarith)
        _ = 2 ^ (2 - β) * ctM z x ^ (β - 2) := by
            rw [div_eq_mul_inv, Real.mul_rpow hxm.le (by norm_num), Real.inv_rpow (by norm_num),
              ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            rw [show -(β - 2) = 2 - β by ring]
            ring
    refine (ct_opNorm_le (fderiv ℝ F w)).trans ?_
    calc ∑ l : Fin d, |fderiv ℝ F w (Pi.single l 1)|
        ≤ ∑ _l : Fin d, M * (2 ^ (2 - β) * ctM z x ^ (β - 2)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          exact (h.hess_bound w hwQ j l).trans (mul_le_mul_of_nonneg_left hpow hM)
      _ = (d : ℝ) * 2 ^ (2 - β) * M * ctM z x ^ (β - 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hxs : x ∈ s := mem_ball_self (by positivity)
  have hys : y ∈ s := by
    rw [hs, mem_ball_iff_norm]
    exact hy
  have := (convex_ball x (ctM z x / 2)).norm_image_sub_le_of_norm_fderiv_le hFd hbound hys hxs
  rw [Real.norm_eq_abs] at this
  exact this

/-- The `L²` integral of a gradient component: `∫_Q (∂_j b)² ≤ M² d 4^{2-2β}/(2β-1)`. -/
theorem CTReg.grad_sq_integral [NeZero d] {z : Fin d → ℝ} {β M : ℝ}
    (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) {b : (Fin d → ℝ) → ℝ} (h : CTReg z β M b)
    (hM : 0 ≤ M) (j : Fin d) :
    IntegrableOn (fun x => fderiv ℝ b x (Pi.single j 1) ^ 2) (ctQ z) volume ∧
      ∫ x in ctQ z, fderiv ℝ b x (Pi.single j 1) ^ 2 ≤
        M ^ 2 * ((d : ℝ) * (4 ^ (2 - 2 * β) / (1 - (2 - 2 * β)))) := by
  have hβ1 := hβ.1
  have hβ2 := hβ.2
  have ha0 : 0 ≤ 2 - 2 * β := by linarith
  have ha1 : 2 - 2 * β < 1 := by linarith
  obtain ⟨hint, hle⟩ := integral_ctM_rpow_le (d := d) z ha0 ha1
  have hpt : ∀ x ∈ ctQ z, fderiv ℝ b x (Pi.single j 1) ^ 2 ≤ M ^ 2 * ctM z x ^ (-(2 - 2 * β)) := by
    intro x hx
    have hm := ctM_pos hx
    have h1 : fderiv ℝ b x (Pi.single j 1) ^ 2 ≤ (M * ctM z x ^ (β - 1)) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (h.grad_bound x hx j) 2
      rwa [sq_abs] at this
    have h2 : (M * ctM z x ^ (β - 1)) ^ 2 = M ^ 2 * ctM z x ^ (-(2 - 2 * β)) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
      congr 1
      push_cast
      ring
    exact h1.trans h2.le
  have hcont : ContinuousOn (fun x => fderiv ℝ b x (Pi.single j 1) ^ 2) (ctQ z) :=
    (h.continuousOn_grad j).pow 2
  have hg : IntegrableOn (fun x => M ^ 2 * ctM z x ^ (-(2 - 2 * β))) (ctQ z) volume :=
    hint.const_mul _
  have hf : IntegrableOn (fun x => fderiv ℝ b x (Pi.single j 1) ^ 2) (ctQ z) volume := by
    refine Integrable.mono' hg (hcont.aestronglyMeasurable isOpen_ball.measurableSet) ?_
    exact ae_restrict_of_forall_mem isOpen_ball.measurableSet fun x hx => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt x hx
  refine ⟨hf, ?_⟩
  calc ∫ x in ctQ z, fderiv ℝ b x (Pi.single j 1) ^ 2
      ≤ ∫ x in ctQ z, M ^ 2 * ctM z x ^ (-(2 - 2 * β)) :=
        setIntegral_mono_on hf hg isOpen_ball.measurableSet hpt
    _ = M ^ 2 * ∫ x in ctQ z, ctM z x ^ (-(2 - 2 * β)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- An `H¹(Q)` function with the classical gradient. -/
theorem CTReg.exists_h1 [NeZero d] {z : Fin d → ℝ} {β M : ℝ}
    (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) {b : (Fin d → ℝ) → ℝ} (h : CTReg z β M b)
    (hM : 0 ≤ M) :
    ∃ u : Homogenization.H1Function (ctQ z), u.toFun = b ∧
      u.grad = fun x j => fderiv ℝ b x (Pi.single j 1) := by
  haveI : IsFiniteMeasure (volume.restrict (ctQ z)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hbc : ContinuousOn b (ctQ z) := h.contDiffOn.continuousOn
  obtain ⟨B, hB⟩ := h.bdd
  refine ⟨{ toFun := b
            grad := fun x j => fderiv ℝ b x (Pi.single j 1)
            memL2 := ?_
            gradMemL2 := ?_
            hasWeakGradient := ?_ }, rfl, rfl⟩
  · exact MemLp.of_bound (hbc.aestronglyMeasurable isOpen_ball.measurableSet) B
      (ae_restrict_of_forall_mem isOpen_ball.measurableSet fun x hx => by
        rw [Real.norm_eq_abs]; exact hB x hx)
  · intro j
    exact (memLp_two_iff_integrable_sq
      ((h.continuousOn_grad j).aestronglyMeasurable isOpen_ball.measurableSet)).2
      (h.grad_sq_integral hβ hM j).1
  · intro j
    exact ct_hasWeakPartialDerivOn isOpen_ball (h.contDiffOn.of_le (by norm_num)) j

end SubdiffusiveProcess.CubeTrace
