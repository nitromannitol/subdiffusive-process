import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import Homogenization.Ambient.ScalarMatrix
import Homogenization.Sobolev.PotentialSolenoidalL2




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The weak massive equation -/



def IsMassiveWeakSolutionOn (c rho : Vec d → ℝ) (mu : ℝ) (W : Set (Vec d))
    (u : H1Function W) (f : Vec d → ℝ) : Prop :=
  ∀ φ : H10Function W,
    mu * ∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume +
        ∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume =
      ∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume



def IsMassiveDirichletSolutionOn (c rho : Vec d → ℝ) (mu : ℝ) (W : Set (Vec d))
    (u hD : H1Function W) (f : Vec d → ℝ) : Prop :=
  HasZeroTraceDifferenceOn W u hD ∧ IsMassiveWeakSolutionOn c rho mu W u f

/-! ### The difference of two solutions -/

/-- Two `H¹` functions with the same zero-trace datum differ by an `H¹₀`
function.  (A local re-proof: the corresponding lemma in
`SubdiffusiveProcess/CoarseGrainingVocab/DirichletUniqueness.lean` is private.) -/
theorem exists_h10_add_of_hasZeroTraceDifferenceOn {W : Set (Vec d)}
    {u u' hD : H1Function W} (hu : HasZeroTraceDifferenceOn W u hD)
    (hu' : HasZeroTraceDifferenceOn W u' hD) :
    ∃ w : H10Function W,
      (∀ x, u.toFun x = u'.toFun x + w.toH1Function.toFun x) ∧
        ∀ x, u.grad x = u'.grad x + w.toH1Function.grad x := by
  obtain ⟨w₁, hw₁f, hw₁g⟩ := hu
  obtain ⟨w₂, hw₂f, hw₂g⟩ := hu'
  refine ⟨w₁ - w₂, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hsub : (w₁ - w₂).toH1Function.toFun x =
        w₁.toH1Function.toFun x - w₂.toH1Function.toFun x := by
      change (w₁.toH1Function - w₂.toH1Function).toFun x =
        w₁.toH1Function.toFun x - w₂.toH1Function.toFun x
      rw [H1Function.sub_toFun]
    rw [hsub, hw₁f x, hw₂f x]
    ring
  · have hsub : (w₁ - w₂).toH1Function.grad x =
        w₁.toH1Function.grad x - w₂.toH1Function.grad x := by
      change (w₁.toH1Function - w₂.toH1Function).grad x =
        w₁.toH1Function.grad x - w₂.toH1Function.grad x
      rw [H1Function.sub_grad]
    rw [hsub, hw₁g x, hw₂g x]
    abel

/-! ### Integrability of the two terms of the form -/

/-- The density times an `L²` function is again `L²`, when the density is
bounded. -/
theorem memL2On_mul_of_bounded {W : Set (Vec d)} {rho v : Vec d → ℝ}
    (hmeas : AEStronglyMeasurable rho (volume.restrict W))
    {rhoMax : ℝ} (hbdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hv : MemL2On W v) :
    MemL2On W (fun x ↦ rho x * v x) := by
  refine MemLp.mono (hv.const_mul rhoMax) (hmeas.mul hv.aestronglyMeasurable) ?_
  filter_upwards [hbdd] with x hx
  have h0 : (0 : ℝ) ≤ rhoMax := le_trans (abs_nonneg _) hx
  calc ‖rho x * v x‖ = |rho x| * ‖v x‖ := by
        rw [norm_mul, Real.norm_eq_abs]
    _ ≤ rhoMax * ‖v x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = ‖rhoMax * v x‖ := by rw [norm_mul, Real.norm_of_nonneg h0]

/-- The mass term of the massive form is integrable. -/
theorem integrableOn_mass_term {W : Set (Vec d)} {rho : Vec d → ℝ}
    (hmeas : AEStronglyMeasurable rho (volume.restrict W))
    {rhoMax : ℝ} (hbdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {v w : Vec d → ℝ} (hv : MemL2On W v) (hw : MemL2On W w) :
    IntegrableOn (fun x ↦ rho x * v x * w x) W :=
  (memL2On_mul_of_bounded hmeas hbdd hv).integrable_mul hw

/-- The energy term of the massive form is integrable. -/
theorem integrableOn_energy_term {W : Set (Vec d)} {c : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    {F G : Vec d → Vec d} (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) :
    IntegrableOn (fun x ↦ vecDot (c x • F x) (G x)) W := by
  have hmem : MemVectorL2 W (fun x ↦ c x • F x) := by
    have := memVectorL2_matVecMul_of_isEllipticFieldOn hEll hF
    simpa [scalarCoeffField, matVecMul_scalarMatrix] using this
  exact integrableOn_vecDot_of_memVectorL2 hmem hG

/-! ### The energy identity and uniqueness -/

/-- **The energy identity for the difference of two massive solutions.**
If `u` and `u'` solve the same zero-boundary massive problem and `w` is their
`H¹₀` difference, then

  `μ ∫_W ρ w² + ∫_W c |∇w|² = 0`.

Both summands are nonnegative under the ellipticity hypotheses, which is the
whole content of uniqueness. -/
theorem massive_energy_identity_of_isMassiveDirichletSolutionOn
    {W : Set (Vec d)} {c rho : Vec d → ℝ} {mu lam Lam rhoMax : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u u' hD : H1Function W} {f : Vec d → ℝ}
    (hu : IsMassiveDirichletSolutionOn c rho mu W u hD f)
    (hu' : IsMassiveDirichletSolutionOn c rho mu W u' hD f)
    {w : H10Function W}
    (hwf : ∀ x, u.toFun x = u'.toFun x + w.toH1Function.toFun x)
    (hwg : ∀ x, u.grad x = u'.grad x + w.toH1Function.grad x) :
    mu * ∫ x in W, rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume +
        ∫ x in W, c x * vecNormSq (w.toH1Function.grad x) ∂volume = 0 := by
  have hEq := hu.2 w
  have hEq' := hu'.2 w
  -- the mass terms
  have hmassU : IntegrableOn
      (fun x ↦ rho x * u.toFun x * w.toH1Function.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 w.toH1Function.memL2
  have hmassU' : IntegrableOn
      (fun x ↦ rho x * u'.toFun x * w.toH1Function.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd u'.memL2 w.toH1Function.memL2
  have hmassSplit :
      ∫ x in W, rho x * u.toFun x * w.toH1Function.toFun x ∂volume -
          ∫ x in W, rho x * u'.toFun x * w.toH1Function.toFun x ∂volume =
        ∫ x in W, rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume := by
    rw [← integral_sub hmassU hmassU']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [hwf x]
    ring
  -- the energy terms
  have henU : IntegrableOn
      (fun x ↦ vecDot (c x • u.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_energy_term hEll u.grad_memVectorL2 w.toH1Function.grad_memVectorL2
  have henU' : IntegrableOn
      (fun x ↦ vecDot (c x • u'.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_energy_term hEll u'.grad_memVectorL2 w.toH1Function.grad_memVectorL2
  have henSplit :
      ∫ x in W, vecDot (c x • u.grad x) (w.toH1Function.grad x) ∂volume -
          ∫ x in W, vecDot (c x • u'.grad x) (w.toH1Function.grad x) ∂volume =
        ∫ x in W, c x * vecNormSq (w.toH1Function.grad x) ∂volume := by
    rw [← integral_sub henU henU']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [hwg x, smul_add, vecDot_add_left, vecDot_smul_left, vecNormSq]
    ring
  have := congrArg₂ (· - ·) hEq hEq'
  simp only [sub_self] at this
  have hkey :
      mu * (∫ x in W, rho x * u.toFun x * w.toH1Function.toFun x ∂volume -
              ∫ x in W, rho x * u'.toFun x * w.toH1Function.toFun x ∂volume) +
          (∫ x in W, vecDot (c x • u.grad x) (w.toH1Function.grad x) ∂volume -
            ∫ x in W, vecDot (c x • u'.grad x) (w.toH1Function.grad x) ∂volume) = 0 := by
    linarith [this]
  rw [hmassSplit, henSplit] at hkey
  exact hkey

/-- **A.e. uniqueness for the zero-boundary massive problem.**  Two solutions of
`μ ρ u - ∇·(c∇u) = ρ f` with the same zero-trace datum agree almost everywhere,
together with their weak gradients.

Unlike the pure Dirichlet problem, no Poincaré inequality is used: the mass term
`μ ∫ ρ w²` already controls `w`, and the energy term controls `∇w`.  Hence `W`
need only be measurable. -/
theorem ae_eq_of_isMassiveDirichletSolutionOn
    {W : Set (Vec d)} (hWmeas : MeasurableSet W)
    {c rho : Vec d → ℝ} {mu lam Lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hlam : 0 < lam) (hc : ∀ x ∈ W, lam ≤ c x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u u' hD : H1Function W} {f : Vec d → ℝ}
    (hu : IsMassiveDirichletSolutionOn c rho mu W u hD f)
    (hu' : IsMassiveDirichletSolutionOn c rho mu W u' hD f) :
    u.toFun =ᵐ[volume.restrict W] u'.toFun ∧
      u.grad =ᵐ[volume.restrict W] u'.grad := by
  obtain ⟨w, hwf, hwg⟩ := exists_h10_add_of_hasZeroTraceDifferenceOn hu.1 hu'.1
  have hid := massive_energy_identity_of_isMassiveDirichletSolutionOn
    hEll hrhoMeas hrhoBdd hu hu' hwf hwg
  set W2 : ℝ := ∫ x in W, rho x * w.toH1Function.toFun x * w.toH1Function.toFun x ∂volume
    with hW2
  set E2 : ℝ := ∫ x in W, c x * vecNormSq (w.toH1Function.grad x) ∂volume with hE2
  have hW2nonneg : 0 ≤ W2 := by
    rw [hW2]
    refine setIntegral_nonneg hWmeas fun x hx ↦ ?_
    have : 0 ≤ rho x := le_trans hrhoMin.le (hrhoLow x hx)
    nlinarith [sq_nonneg (w.toH1Function.toFun x)]
  have hE2nonneg : 0 ≤ E2 := by
    rw [hE2]
    refine setIntegral_nonneg hWmeas fun x hx ↦ ?_
    exact mul_nonneg (le_trans hlam.le (hc x hx)) (vecNormSq_nonneg _)
  have hmw : 0 ≤ mu * W2 := mul_nonneg hmu.le hW2nonneg
  have hE2zero : E2 = 0 := by linarith
  have hW2zero : W2 = 0 :=
    (mul_eq_zero.1 (by linarith : mu * W2 = 0)).resolve_left hmu.ne'
  -- from the mass term: `w = 0` a.e.
  have hwInt : IntegrableOn
      (fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd w.toH1Function.memL2 w.toH1Function.memL2
  have hwAeNonneg : 0 ≤ᵐ[volume.restrict W]
      fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x := by
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    have hr : 0 ≤ rho x := le_trans hrhoMin.le (hrhoLow x hx)
    have hnn : 0 ≤ rho x * (w.toH1Function.toFun x * w.toH1Function.toFun x) :=
      mul_nonneg hr (mul_self_nonneg _)
    simpa [mul_assoc] using hnn
  have hwAe : (fun x ↦ rho x * w.toH1Function.toFun x * w.toH1Function.toFun x)
      =ᵐ[volume.restrict W] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hwAeNonneg hwInt.integrable).1 hW2zero
  have hwZero : w.toH1Function.toFun =ᵐ[volume.restrict W] 0 := by
    filter_upwards [hwAe, ae_restrict_mem hWmeas] with x hx hxW
    have hrho : 0 < rho x := lt_of_lt_of_le hrhoMin (hrhoLow x hxW)
    have hsq : w.toH1Function.toFun x * w.toH1Function.toFun x = 0 := by
      have : rho x * (w.toH1Function.toFun x * w.toH1Function.toFun x) = 0 := by
        simpa [mul_assoc] using hx
      exact (mul_eq_zero.1 this).resolve_left hrho.ne'
    exact mul_self_eq_zero.1 hsq
  -- from the energy term: `∇w = 0` a.e.
  have henInt : IntegrableOn (fun x ↦ c x * vecNormSq (w.toH1Function.grad x)) W := by
    have := integrableOn_energy_term hEll
      w.toH1Function.grad_memVectorL2 w.toH1Function.grad_memVectorL2
    refine this.congr_fun (fun x _ ↦ ?_) hWmeas
    rw [vecDot_smul_left, vecNormSq]
  have henAeNonneg : 0 ≤ᵐ[volume.restrict W]
      fun x ↦ c x * vecNormSq (w.toH1Function.grad x) := by
    filter_upwards [ae_restrict_mem hWmeas] with x hx
    have hnn : 0 ≤ c x * vecNormSq (w.toH1Function.grad x) :=
      mul_nonneg (le_trans hlam.le (hc x hx)) (vecNormSq_nonneg _)
    simpa using hnn
  have henAe : (fun x ↦ c x * vecNormSq (w.toH1Function.grad x))
      =ᵐ[volume.restrict W] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae henAeNonneg henInt.integrable).1 hE2zero
  have hgradZero : w.toH1Function.grad =ᵐ[volume.restrict W] 0 := by
    filter_upwards [henAe, ae_restrict_mem hWmeas] with x hx hxW
    have hcx : 0 < c x := lt_of_lt_of_le hlam (hc x hxW)
    have : vecNormSq (w.toH1Function.grad x) = 0 :=
      (mul_eq_zero.1 hx).resolve_left hcx.ne'
    exact vecNormSq_eq_zero this
  refine ⟨?_, ?_⟩
  · filter_upwards [hwZero] with x hx
    simp [hwf x, hx]
  · filter_upwards [hgradZero] with x hx
    simp [hwg x, hx]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
