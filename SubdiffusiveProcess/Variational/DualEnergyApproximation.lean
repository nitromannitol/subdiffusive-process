module

public import SubdiffusiveProcess.Variational.DualEnergyRegularization
@[expose] public section

open Filter Set
open scoped Topology
namespace SubdiffusiveProcess

/-- Positive-shift resolvents approximate every finite dual-energy vector in norm and energy. -/
theorem tendsto_positive_shift_energy_approximation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H) (R : ℕ → H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x))
    (hR : ∀ n : ℕ,
      (G + (1 / (n + 1 : ℝ)) • ContinuousLinearMap.id ℝ H).comp (R n) =
        ContinuousLinearMap.id ℝ H)
    (u : H) (e : ℝ)
    (he : (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) = (e : EReal)) :
    Tendsto (fun n : ℕ =>
      (G (R n u), inner ℝ (R n u) (G (R n u)),
        ⨆ f : H, ((2 * inner ℝ f (u - G (R n u)) - inner ℝ f (G f) : ℝ) : EReal)))
      atTop (𝓝 (u, e, (0 : EReal))) := by
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let v : ℕ → H := fun n => R n u
  let q : ℕ → ℝ := fun n => inner ℝ u (v n)
  let p : ℕ → ℝ := fun n => ε n * ‖v n‖ ^ 2
  let d : ℕ → ℝ := fun n => e - q n - p n
  have hsolve (n : ℕ) : G (v n) + ε n • v n = u := by
    have h := congrArg (fun A : H →L[ℝ] H => A u) (hR n)
    simpa only [v, ε, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] using h
  have hqE : Tendsto (fun n => ((q n : ℝ) : EReal)) atTop (𝓝 (e : EReal)) := by
    rw [← he]
    apply (tendsto_regularized_quadraticDual G u).congr'
    filter_upwards [] with n
    rw [regularized_quadraticDual_eq_pairing G (R n) hsym hpos (ε n) (by positivity)
      (hR n) u]
  have hq : Tendsto q atTop (𝓝 e) := EReal.tendsto_coe.mp hqE
  have hp_nonneg (n : ℕ) : 0 ≤ p n := mul_nonneg (by positivity) (sq_nonneg _)
  have hpair (n : ℕ) : q n = inner ℝ (v n) (G (v n)) + p n := by
    have h := congrArg (fun z : H => inner ℝ (v n) z) (hsolve n)
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
    dsimp [q, p]
    rw [← real_inner_comm u (v n)]
    exact h.symm
  have hdual (n : ℕ) :
      (⨆ f : H, ((2 * inner ℝ f (u - G (v n)) - inner ℝ f (G f) : ℝ) : EReal)) =
        ((d n : ℝ) : EReal) := by
    rw [quadraticDual_sub_image G hsym u (v n), he, ← EReal.coe_sub]
    congr 1
    dsimp [d]
    have hcross : inner ℝ (v n) u = q n := by
      dsimp [q]
      exact real_inner_comm _ _
    rw [hcross, hpair]
    ring
  have hd_nonneg (n : ℕ) : 0 ≤ d n := by
    apply EReal.coe_le_coe_iff.mp
    rw [← hdual]
    simpa only [inner_zero_left, map_zero, mul_zero, sub_self] using
      (le_iSup (fun f : H =>
        ((2 * inner ℝ f (u - G (v n)) - inner ℝ f (G f) : ℝ) : EReal)) 0)
  have hp_le (n : ℕ) : p n ≤ e - q n := by
    dsimp [d] at hd_nonneg
    linarith [hd_nonneg n]
  have hgap : Tendsto (fun n => e - q n) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.sub hq) using 1 <;> simp
  have hp : Tendsto p atTop (𝓝 0) := squeeze_zero hp_nonneg hp_le hgap
  have hd : Tendsto d atTop (𝓝 0) := by
    dsimp [d]
    convert (tendsto_const_nhds.sub hq).sub hp using 1 <;> simp
  have hres_norm_sq : Tendsto (fun n => ‖u - G (v n)‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n =>
      norm_sq_le_operatorNorm_mul_quadraticDual G (u - G (v n)) (d n) (hdual n))
    simpa using tendsto_const_nhds.mul hd
  have hres_norm : Tendsto (fun n => ‖u - G (v n)‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hres_norm_sq (δ ^ 2) (sq_pos_of_pos hδ)
    refine ⟨N, fun n hn => ?_⟩
    have hs := hN n hn
    rw [Real.dist_eq, sub_zero] at hs
    rw [abs_of_nonneg (sq_nonneg ‖u - G (v n)‖)] at hs
    simp only [Real.dist_eq, sub_zero, abs_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp hs
  have hG : Tendsto (fun n => G (v n)) atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hres_norm
  have henergy : Tendsto (fun n => inner ℝ (v n) (G (v n))) atTop (𝓝 e) := by
    have : (fun n => inner ℝ (v n) (G (v n))) = fun n => q n - p n := by
      funext n
      rw [hpair]
      ring
    rw [this]
    simpa using hq.sub hp
  have hdual_lim : Tendsto (fun n =>
      ⨆ f : H, ((2 * inner ℝ f (u - G (v n)) - inner ℝ f (G f) : ℝ) : EReal))
      atTop (𝓝 (0 : EReal)) := by
    apply (EReal.tendsto_coe.mpr hd).congr'
    exact Eventually.of_forall fun n => (hdual n).symm
  exact hG.prodMk_nhds (henergy.prodMk_nhds hdual_lim)

end SubdiffusiveProcess
