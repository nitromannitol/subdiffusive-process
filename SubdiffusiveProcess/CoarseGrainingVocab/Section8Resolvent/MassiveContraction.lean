import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}



theorem massive_energy_identity_of_isMassiveWeakSolutionOn
    {W : Set (Vec d)} {c rho : Vec d → ℝ} {mu : ℝ}
    {u : H10Function W} {f : Vec d → ℝ}
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f) :
    mu * ∫ x in W, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume +
        ∫ x in W, c x * vecNormSq (u.toH1Function.grad x) ∂volume =
      ∫ x in W, rho x * f x * u.toH1Function.toFun x ∂volume := by
  have h := hu u
  have hcongr :
      ∫ x in W, vecDot (c x • u.toH1Function.grad x) (u.toH1Function.grad x) ∂volume =
        ∫ x in W, c x * vecNormSq (u.toH1Function.grad x) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [vecDot_smul_left, vecNormSq]
  rw [← hcongr]
  exact h

/-- Pointwise Young inequality with the weight `ρ`. -/
theorem weighted_young {mu r v s : ℝ} (hmu : 0 < mu) (hr : 0 ≤ r) :
    r * s * v ≤ mu / 2 * (r * v * v) + (2 * mu)⁻¹ * (r * s * s) := by
  have h2mu : (0 : ℝ) < 2 * mu := by linarith
  have ht : (2 * mu)⁻¹ * (2 * mu) = 1 := inv_mul_cancel₀ h2mu.ne'
  have ht0 : (0 : ℝ) < (2 * mu)⁻¹ := inv_pos.2 h2mu
  have hexp : mu / 2 * (v * v) + (2 * mu)⁻¹ * (s * s) - s * v =
      (2 * mu)⁻¹ * (mu * v - s) ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ (2 * mu)⁻¹ * (mu * v - s) ^ 2 :=
    mul_nonneg ht0.le (sq_nonneg _)
  have hkey : s * v ≤ mu / 2 * (v * v) + (2 * mu)⁻¹ * (s * s) := by
    linarith [hexp, hnn]
  calc r * s * v = r * (s * v) := by ring
    _ ≤ r * (mu / 2 * (v * v) + (2 * mu)⁻¹ * (s * s)) :=
        mul_le_mul_of_nonneg_left hkey hr
    _ = mu / 2 * (r * v * v) + (2 * mu)⁻¹ * (r * s * s) := by ring

/-- The integral form of the weighted Young inequality. -/
theorem integral_weighted_young {W : Set (Vec d)} (hWmeas : MeasurableSet W)
    {rho : Vec d → ℝ} {mu rhoMin rhoMax : ℝ} (hmu : 0 < mu) (hrhoMin : 0 < rhoMin)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {v f : Vec d → ℝ} (hv : MemL2On W v) (hf : MemL2On W f) :
    ∫ x in W, rho x * f x * v x ∂volume ≤
      mu / 2 * ∫ x in W, rho x * v x * v x ∂volume +
        (2 * mu)⁻¹ * ∫ x in W, rho x * f x * f x ∂volume := by
  have hfv : Integrable (fun x ↦ rho x * f x * v x) (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd hf hv
  have hvv : Integrable (fun x ↦ rho x * v x * v x) (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd hv hv
  have hff : Integrable (fun x ↦ rho x * f x * f x) (volume.restrict W) :=
    integrableOn_mass_term hrhoMeas hrhoBdd hf hf
  have hvvC : Integrable (fun x ↦ mu / 2 * (rho x * v x * v x))
      (volume.restrict W) := hvv.const_mul _
  have hffC : Integrable (fun x ↦ (2 * mu)⁻¹ * (rho x * f x * f x))
      (volume.restrict W) := hff.const_mul _
  have hbound : ∫ x in W, rho x * f x * v x ∂volume ≤
      ∫ x in W, (mu / 2 * (rho x * v x * v x) +
        (2 * mu)⁻¹ * (rho x * f x * f x)) ∂volume := by
    refine integral_mono_ae hfv (hvvC.add hffC) ?_
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    exact weighted_young hmu (le_trans hrhoMin.le (hrhoLow x hx))
  calc ∫ x in W, rho x * f x * v x ∂volume
      ≤ ∫ x in W, (mu / 2 * (rho x * v x * v x) +
          (2 * mu)⁻¹ * (rho x * f x * f x)) ∂volume := hbound
    _ = mu / 2 * ∫ x in W, rho x * v x * v x ∂volume +
          (2 * mu)⁻¹ * ∫ x in W, rho x * f x * f x ∂volume := by
        rw [integral_add hvvC hffC, integral_const_mul, integral_const_mul]

/-- **The `L²(μ)` contraction bound for the local resolvent.**  If `u = R_μ^W f`
is the zero-trace solution of `μ ρ u - ∇·(c∇u) = ρ f`, then

  `μ² ∫_W ρ u² ≤ ∫_W ρ f²`,

i.e. `‖μ R_μ^W‖_{L²(μ)} ≤ 1`. -/
theorem massive_l2_contraction
    {W : Set (Vec d)} (hWmeas : MeasurableSet W)
    {c rho : Vec d → ℝ} {mu lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin)
    (hlam : 0 < lam) (hc : ∀ x ∈ W, lam ≤ c x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u : H10Function W} {f : Vec d → ℝ} (hf : MemL2On W f)
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f) :
    mu ^ 2 * ∫ x in W, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume ≤
      ∫ x in W, rho x * f x * f x ∂volume := by
  have hid := massive_energy_identity_of_isMassiveWeakSolutionOn hu
  have hyoung := integral_weighted_young hWmeas hmu hrhoMin hrhoMeas hrhoLow hrhoBdd
    u.toH1Function.memL2 hf
  have hE : 0 ≤ ∫ x in W, c x * vecNormSq (u.toH1Function.grad x) ∂volume := by
    refine setIntegral_nonneg hWmeas fun x hx ↦ ?_
    exact mul_nonneg (le_trans hlam.le (hc x hx)) (vecNormSq_nonneg _)
  have hkey : mu / 2 *
      ∫ x in W, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume ≤
      (2 * mu)⁻¹ * ∫ x in W, rho x * f x * f x ∂volume := by linarith
  have h2mu : (0 : ℝ) < 2 * mu := by linarith
  have := mul_le_mul_of_nonneg_left hkey (le_of_lt h2mu)
  have hL : 2 * mu * (mu / 2 *
      ∫ x in W, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume) =
      mu ^ 2 * ∫ x in W, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume := by
    ring
  have hR : 2 * mu * ((2 * mu)⁻¹ * ∫ x in W, rho x * f x * f x ∂volume) =
      ∫ x in W, rho x * f x * f x ∂volume := by
    field_simp
  rw [hL, hR] at this
  exact this
  -- (the coercivity of `c` was used only through `hE`)



theorem massive_energy_bound
    {W : Set (Vec d)} (hWmeas : MeasurableSet W)
    {c rho : Vec d → ℝ} {mu rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u : H10Function W} {f : Vec d → ℝ} (hf : MemL2On W f)
    (hu : IsMassiveWeakSolutionOn c rho mu W u.toH1Function f) :
    2 * mu * ∫ x in W, c x * vecNormSq (u.toH1Function.grad x) ∂volume ≤
      ∫ x in W, rho x * f x * f x ∂volume := by
  have hid := massive_energy_identity_of_isMassiveWeakSolutionOn hu
  have hyoung := integral_weighted_young hWmeas hmu hrhoMin hrhoMeas hrhoLow hrhoBdd
    u.toH1Function.memL2 hf
  have hM : 0 ≤
      ∫ x in W, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume := by
    refine setIntegral_nonneg hWmeas fun x hx ↦ ?_
    have hr : 0 ≤ rho x := le_trans hrhoMin.le (hrhoLow x hx)
    have hnn : 0 ≤ rho x * (u.toH1Function.toFun x * u.toH1Function.toFun x) :=
      mul_nonneg hr (mul_self_nonneg _)
    simpa [mul_assoc] using hnn
  have hkey : ∫ x in W, c x * vecNormSq (u.toH1Function.grad x) ∂volume ≤
      (2 * mu)⁻¹ * ∫ x in W, rho x * f x * f x ∂volume := by nlinarith
  have h2mu : (0 : ℝ) < 2 * mu := by linarith
  have hstep := mul_le_mul_of_nonneg_left hkey (le_of_lt h2mu)
  have hR : 2 * mu * ((2 * mu)⁻¹ * ∫ x in W, rho x * f x * f x ∂volume) =
      ∫ x in W, rho x * f x * f x ∂volume := by field_simp
  rw [hR] at hstep
  exact hstep

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
