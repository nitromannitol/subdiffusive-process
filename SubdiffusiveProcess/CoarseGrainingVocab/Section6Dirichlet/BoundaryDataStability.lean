module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.LocalUniformCoefficientStability

@[expose] public section

/-!
# Stability of scalar Dirichlet solutions under boundary-data perturbations

This module records the deterministic energy-minimality argument for two
solutions of the same scalar equation with different boundary data.  It is the
fixed-coefficient counterpart of `LocalUniformCoefficientStability`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The integral square-root norm used by the Dirichlet estimates is exactly
the norm of the canonical Hilbert-valued `L²` realization. -/
theorem norm_toHilbertVectorL2OfVecField_eq_l2NormOn
    {W : Set (Vec d)} {F : Vec d → Vec d} (hWm : MeasurableSet W)
    (hF : MemVectorL2 W F) :
    ‖toHilbertVectorL2OfVecField hF‖ = Section5Support.l2NormOn W F := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (Section5Support.l2NormOn_nonneg W F)).mp
  rw [← real_inner_self_eq_norm_sq,
    inner_toHilbertVectorL2OfVecField_eq_integral hF hF,
    Section5Support.sq_l2NormOn hWm]
  exact MeasureTheory.setIntegral_congr_fun hWm fun x _ ↦ rfl

private theorem vecDot_sub_left (a b c : Vec d) :
    vecDot (a - b) c = vecDot a c - vecDot b c := by
  classical
  simp only [vecDot, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

private theorem weighted_vecDot_sub_self_expand (a : ℝ) (p q : Vec d) :
    vecDot (a • (p - q)) (p - q) =
      vecDot (a • p) p - 2 * vecDot (a • p) q + vecDot (a • q) q := by
  classical
  simp only [vecDot, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- If `u - h₁` and `v - h₂` have zero trace, then
`(u-v) - (h₁-h₂)` has zero trace, with literal value and gradient
representatives. -/
theorem exists_h10Function_solutionDifference_sub_boundaryDifference
    {W : Set (Vec d)} {u v h₁ h₂ : H1Function W}
    (hu : HasZeroTraceDifferenceOn W u h₁)
    (hv : HasZeroTraceDifferenceOn W v h₂) :
    ∃ w : H10Function W,
      (∀ x, w.toH1Function.toFun x =
        (u.toFun x - v.toFun x) - (h₁.toFun x - h₂.toFun x)) ∧
      ∀ x, w.toH1Function.grad x =
        (u.grad x - v.grad x) - (h₁.grad x - h₂.grad x) := by
  obtain ⟨wu, hwuf, hwug⟩ := hu
  obtain ⟨wv, hwvf, hwvg⟩ := hv
  refine ⟨wu - wv, fun x ↦ ?_, fun x ↦ ?_⟩
  · change (wu.toH1Function - wv.toH1Function).toFun x = _
    rw [H1Function.sub_toFun, hwuf x, hwvf x]
    ring
  · change (wu.toH1Function - wv.toH1Function).grad x = _
    rw [H1Function.sub_grad, hwug x, hwvg x]
    abel_nf

/-- The difference of two weakly harmonic functions for the same scalar
coefficient is weakly harmonic.  Ellipticity supplies the integrability needed
to subtract the two weak formulations. -/
theorem isWeaklyHarmonicOn_sub
    {W : Set (Vec d)} {a : Vec d → ℝ} {lambda Lambda : ℝ}
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    {u v : H1Function W} (hu : IsWeaklyHarmonicOn a W u)
    (hv : IsWeaklyHarmonicOn a W v) :
    IsWeaklyHarmonicOn a W (u - v) := by
  intro phi
  have huFlux : MemVectorL2 W (fun x ↦ a x • u.grad x) := by
    simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2)
  have hvFlux : MemVectorL2 W (fun x ↦ a x • v.grad x) := by
    simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.grad_memVectorL2)
  have huInt := integrableOn_vecDot_of_memVectorL2
    huFlux phi.toH1Function.grad_memVectorL2
  have hvInt := integrableOn_vecDot_of_memVectorL2
    hvFlux phi.toH1Function.grad_memVectorL2
  rw [H1Function.sub_grad]
  have hfun :
      (fun x ↦ vecDot (a x • (u.grad x - v.grad x))
        (phi.toH1Function.grad x)) =
      fun x ↦ vecDot (a x • u.grad x) (phi.toH1Function.grad x) -
        vecDot (a x • v.grad x) (phi.toH1Function.grad x) := by
    funext x
    rw [smul_sub, vecDot_sub_left]
  rw [hfun, integral_sub huInt hvInt, hu phi, hv phi, sub_self]

/-- A weakly harmonic scalar-coefficient replacement minimizes the weighted
Dirichlet energy among functions with the same trace. -/
theorem integral_coefficient_mul_grad_sq_le_of_boundaryDifference
    {W : Set (Vec d)} {a : Vec d → ℝ} {lambda Lambda : ℝ}
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    (ha : ∀ x ∈ W, 0 ≤ a x)
    {w h : H1Function W} (hw : IsWeaklyHarmonicOn a W w)
    (rho : H10Function W)
    (hgrad : ∀ x, w.grad x = h.grad x + rho.toH1Function.grad x) :
    (∫ x in W, a x * vecNormSq (w.grad x) ∂volume) ≤
      ∫ x in W, a x * vecNormSq (h.grad x) ∂volume := by
  have hwFlux : MemVectorL2 W (fun x ↦ a x • w.grad x) := by
    simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.grad_memVectorL2)
  have hhFlux : MemVectorL2 W (fun x ↦ a x • h.grad x) := by
    simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll h.grad_memVectorL2)
  have hrhoFlux : MemVectorL2 W
      (fun x ↦ a x • rho.toH1Function.grad x) := by
    simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
        rho.toH1Function.grad_memVectorL2)
  have hIww := integrableOn_vecDot_of_memVectorL2 hwFlux w.grad_memVectorL2
  have hIwh := integrableOn_vecDot_of_memVectorL2 hwFlux h.grad_memVectorL2
  have hIhh := integrableOn_vecDot_of_memVectorL2 hhFlux h.grad_memVectorL2
  have hIrr := integrableOn_vecDot_of_memVectorL2
    hrhoFlux rho.toH1Function.grad_memVectorL2
  have hr : ∀ x, rho.toH1Function.grad x = w.grad x - h.grad x := by
    intro x
    rw [hgrad x]
    abel_nf
  have hzero :
      ∫ x in W, vecDot (a x • w.grad x) (rho.toH1Function.grad x) ∂volume = 0 :=
    hw rho
  have hcross :
      (∫ x in W, vecDot (a x • w.grad x) (h.grad x) ∂volume) =
        ∫ x in W, vecDot (a x • w.grad x) (w.grad x) ∂volume := by
    have hsplit :
        (∫ x in W, vecDot (a x • w.grad x) (rho.toH1Function.grad x) ∂volume) =
          (∫ x in W, vecDot (a x • w.grad x) (w.grad x) ∂volume) -
            ∫ x in W, vecDot (a x • w.grad x) (h.grad x) ∂volume := by
      have hfun :
          (fun x ↦ vecDot (a x • w.grad x) (rho.toH1Function.grad x)) =
          fun x ↦ vecDot (a x • w.grad x) (w.grad x) -
            vecDot (a x • w.grad x) (h.grad x) := by
        funext x
        rw [hr x]
        classical
        simp only [vecDot, Pi.sub_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [hfun, integral_sub hIww hIwh]
    rw [hzero] at hsplit
    linarith only [hsplit]
  have hnonneg :
      0 ≤ ∫ x in W,
        vecDot (a x • rho.toH1Function.grad x) (rho.toH1Function.grad x)
          ∂volume := by
    refine setIntegral_nonneg (measurableSet_of_isEllipticFieldOn hEll)
      (fun x hx ↦ ?_)
    rw [vecDot_smul_left]
    exact mul_nonneg (ha x hx) (vecNormSq_nonneg _)
  have hexpand :
      (∫ x in W,
        vecDot (a x • rho.toH1Function.grad x) (rho.toH1Function.grad x)
          ∂volume) =
        (∫ x in W, vecDot (a x • w.grad x) (w.grad x) ∂volume) -
          2 * (∫ x in W, vecDot (a x • w.grad x) (h.grad x) ∂volume) +
          ∫ x in W, vecDot (a x • h.grad x) (h.grad x) ∂volume := by
    have htwice : IntegrableOn
        (fun x ↦ 2 * vecDot (a x • w.grad x) (h.grad x)) W :=
      hIwh.const_mul 2
    have hleft : IntegrableOn
        (fun x ↦ vecDot (a x • w.grad x) (w.grad x) -
          2 * vecDot (a x • w.grad x) (h.grad x)) W :=
      hIww.sub htwice
    have hfun :
        (fun x ↦ vecDot (a x • rho.toH1Function.grad x)
          (rho.toH1Function.grad x)) =
        fun x ↦ (vecDot (a x • w.grad x) (w.grad x) -
          2 * vecDot (a x • w.grad x) (h.grad x)) +
          vecDot (a x • h.grad x) (h.grad x) := by
      funext x
      rw [hr x, weighted_vecDot_sub_self_expand]
    rw [hfun, integral_add hleft hIhh, integral_sub hIww htwice,
      integral_const_mul]
  have hpair :
      (∫ x in W, vecDot (a x • w.grad x) (w.grad x) ∂volume) ≤
        ∫ x in W, vecDot (a x • h.grad x) (h.grad x) ∂volume := by
    linarith only [hnonneg, hexpand, hcross]
  simpa only [vecDot_smul_left, vecNormSq] using hpair

/-- Quantitative gradient stability for a fixed scalar coefficient and two
different boundary data. -/
theorem l2NormOn_gradDifference_le_of_boundaryDifference
    {W : Set (Vec d)} {a : Vec d → ℝ} {lambda Lambda : ℝ}
    (hWm : MeasurableSet W) (hlambda : 0 < lambda) (hLambda : 0 ≤ Lambda)
    (halow : ∀ x ∈ W, lambda ≤ a x) (haup : ∀ x ∈ W, a x ≤ Lambda)
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    {u v h₁ h₂ : H1Function W}
    (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn a W v)
    (huTrace : HasZeroTraceDifferenceOn W u h₁)
    (hvTrace : HasZeroTraceDifferenceOn W v h₂) :
    Section5Support.l2NormOn W (fun x ↦ u.grad x - v.grad x) ≤
      Real.sqrt (Lambda / lambda) *
        Section5Support.l2NormOn W (fun x ↦ h₁.grad x - h₂.grad x) := by
  let D : H1Function W := u - v
  let H : H1Function W := h₁ - h₂
  obtain ⟨rho, _hrhoFun, hrhoGrad⟩ :=
    exists_h10Function_solutionDifference_sub_boundaryDifference huTrace hvTrace
  have hDHarm : IsWeaklyHarmonicOn a W D :=
    isWeaklyHarmonicOn_sub hEll hu hv
  have hDgrad : ∀ x, D.grad x = H.grad x + rho.toH1Function.grad x := by
    intro x
    dsimp only [D, H]
    rw [H1Function.sub_grad, H1Function.sub_grad, hrhoGrad x]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hminimal := integral_coefficient_mul_grad_sq_le_of_boundaryDifference
    hEll (fun x hx ↦ hlambda.le.trans (halow x hx)) hDHarm rho hDgrad
  have hDint : IntegrableOn (fun x ↦ vecNormSq (D.grad x)) W :=
    Section5Support.integrableOn_vecNormSq_of_memLp D.gradMemL2
  have hHint : IntegrableOn (fun x ↦ vecNormSq (H.grad x)) W :=
    Section5Support.integrableOn_vecNormSq_of_memLp H.gradMemL2
  have hDaInt : IntegrableOn (fun x ↦ a x * vecNormSq (D.grad x)) W := by
    have hflux : MemVectorL2 W (fun x ↦ a x • D.grad x) := by
      simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll D.grad_memVectorL2)
    simpa only [vecDot_smul_left, vecNormSq] using
      (integrableOn_vecDot_of_memVectorL2 hflux D.grad_memVectorL2)
  have hHaInt : IntegrableOn (fun x ↦ a x * vecNormSq (H.grad x)) W := by
    have hflux : MemVectorL2 W (fun x ↦ a x • H.grad x) := by
      simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll H.grad_memVectorL2)
    simpa only [vecDot_smul_left, vecNormSq] using
      (integrableOn_vecDot_of_memVectorL2 hflux H.grad_memVectorL2)
  have hlower :
      lambda * (∫ x in W, vecNormSq (D.grad x) ∂volume) ≤
        ∫ x in W, a x * vecNormSq (D.grad x) ∂volume := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hDint.const_mul lambda) hDaInt hWm
      (fun x hx ↦ mul_le_mul_of_nonneg_right (halow x hx) (vecNormSq_nonneg _))
  have hupper :
      (∫ x in W, a x * vecNormSq (H.grad x) ∂volume) ≤
        Lambda * ∫ x in W, vecNormSq (H.grad x) ∂volume := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hHaInt (hHint.const_mul Lambda) hWm
      (fun x hx ↦ mul_le_mul_of_nonneg_right (haup x hx) (vecNormSq_nonneg _))
  have henergy :
      lambda * (∫ x in W, vecNormSq (D.grad x) ∂volume) ≤
        Lambda * ∫ x in W, vecNormSq (H.grad x) ∂volume :=
    hlower.trans (hminimal.trans hupper)
  have hsq :
      Section5Support.l2NormOn W D.grad ^ 2 ≤
        (Lambda / lambda) * Section5Support.l2NormOn W H.grad ^ 2 := by
    rw [Section5Support.sq_l2NormOn hWm,
      Section5Support.sq_l2NormOn hWm]
    calc
      (∫ x in W, vecNormSq (D.grad x) ∂volume) ≤
          (Lambda * ∫ x in W, vecNormSq (H.grad x) ∂volume) / lambda := by
        rw [le_div_iff₀ hlambda]
        simpa only [mul_comm] using henergy
      _ = (Lambda / lambda) *
          ∫ x in W, vecNormSq (H.grad x) ∂volume := by ring
  have hratio : 0 ≤ Lambda / lambda := div_nonneg hLambda hlambda.le
  have hsqrtSq : Real.sqrt (Lambda / lambda) ^ 2 = Lambda / lambda :=
    Real.sq_sqrt hratio
  have hresult : Section5Support.l2NormOn W D.grad ≤
      Real.sqrt (Lambda / lambda) * Section5Support.l2NormOn W H.grad := by
    apply (sq_le_sq₀ (Section5Support.l2NormOn_nonneg W D.grad)
      (mul_nonneg (Real.sqrt_nonneg _)
        (Section5Support.l2NormOn_nonneg W H.grad))).mp
    rw [mul_pow, hsqrtSq]
    exact hsq
  simpa only [D, H, H1Function.sub_grad] using hresult

/-- Boundary-data gradient convergence passes through the fixed-coefficient
Dirichlet solution map. -/
theorem tendsto_l2NormOn_gradDifference_of_boundaryData
    {W : Set (Vec d)} {a : Vec d → ℝ} {lambda Lambda : ℝ}
    {u h : ℕ → H1Function W} {ulim hlim : H1Function W}
    (hWm : MeasurableSet W) (hlambda : 0 < lambda) (hLambda : 0 ≤ Lambda)
    (halow : ∀ x ∈ W, lambda ≤ a x) (haup : ∀ x ∈ W, a x ≤ Lambda)
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    (hu : ∀ n, IsWeaklyHarmonicOn a W (u n))
    (hulim : IsWeaklyHarmonicOn a W ulim)
    (huTrace : ∀ n, HasZeroTraceDifferenceOn W (u n) (h n))
    (hulimTrace : HasZeroTraceDifferenceOn W ulim hlim)
    (hh : Filter.Tendsto
      (fun n ↦ Section5Support.l2NormOn W
        (fun x ↦ (h n).grad x - hlim.grad x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ Section5Support.l2NormOn W
        (fun x ↦ (u n).grad x - ulim.grad x))
      Filter.atTop (nhds 0) := by
  have hbound : ∀ n,
      Section5Support.l2NormOn W (fun x ↦ (u n).grad x - ulim.grad x) ≤
        Real.sqrt (Lambda / lambda) *
          Section5Support.l2NormOn W (fun x ↦ (h n).grad x - hlim.grad x) := by
    intro n
    exact l2NormOn_gradDifference_le_of_boundaryDifference hWm hlambda hLambda
      halow haup hEll (hu n) hulim (huTrace n) hulimTrace
  have hscaled := hh.const_mul (Real.sqrt (Lambda / lambda))
  have hscaled0 : Filter.Tendsto
      (fun n ↦ Real.sqrt (Lambda / lambda) *
        Section5Support.l2NormOn W
          (fun x ↦ (h n).grad x - hlim.grad x))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hscaled
  exact squeeze_zero
    (fun n ↦ Section5Support.l2NormOn_nonneg W
      (fun x ↦ (u n).grad x - ulim.grad x)) hbound hscaled0

/-- For a bounded convex domain, convergence of boundary extensions and of
the corresponding solution gradients forces convergence of the solution
values.  This is the zero-trace Poincare half of boundary-data stability and
does not use the equation. -/
theorem tendsto_norm_toScalarL2_sub_of_boundaryData
    [NeZero d] {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {u h : ℕ → H1Function W} {ulim hlim : H1Function W}
    (huTrace : ∀ n, HasZeroTraceDifferenceOn W (u n) (h n))
    (hulimTrace : HasZeroTraceDifferenceOn W ulim hlim)
    (hhValue : Filter.Tendsto
      (fun n ↦ ‖((h n) - hlim).toScalarL2‖) Filter.atTop (nhds 0))
    (huGrad : Filter.Tendsto
      (fun n ↦ ‖((u n) - ulim).gradToHilbertVectorL2‖)
      Filter.atTop (nhds 0))
    (hhGrad : Filter.Tendsto
      (fun n ↦ ‖((h n) - hlim).gradToHilbertVectorL2‖)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ ‖((u n) - ulim).toScalarL2‖)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hPoincare⟩ :=
    H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hW
  have hbound : ∀ n,
      ‖((u n) - ulim).toScalarL2‖ ≤
        ‖((h n) - hlim).toScalarL2‖ +
          C * d * (‖((u n) - ulim).gradToHilbertVectorL2‖ +
            ‖((h n) - hlim).gradToHilbertVectorL2‖) := by
    intro n
    let D : H1Function W := u n - ulim
    let H : H1Function W := h n - hlim
    obtain ⟨rho, hrhoFun, hrhoGrad⟩ :=
      exists_h10Function_solutionDifference_sub_boundaryDifference
        (huTrace n) hulimTrace
    have hrho : rho.toH1Function = D - H := by
      apply H1Function.ext
      · funext x
        simpa only [D, H, H1Function.sub_toFun] using hrhoFun x
      · funext x
        simpa only [D, H, H1Function.sub_grad] using hrhoGrad x
    have hD : D = H + rho.toH1Function := by
      rw [hrho]
      abel
    have hscalar : ‖D.toScalarL2‖ ≤
        ‖H.toScalarL2‖ + ‖rho.toH1Function.toScalarL2‖ := by
      rw [hD, H1Function.toScalarL2_add]
      exact norm_add_le _ _
    have hrhoPoincare : ‖rho.toH1Function.toScalarL2‖ ≤
        C * d * ‖rho.toH1Function.gradToHilbertVectorL2‖ := by
      calc
        ‖rho.toH1Function.toScalarL2‖ ≤
            C * rho.toH1Function.gradientCoordL2NormSum := hPoincare rho
        _ ≤ C * (d * ‖rho.toH1Function.gradToVectorL2‖) := by
          exact mul_le_mul_of_nonneg_left
            rho.toH1Function.gradientCoordL2NormSum_le hC
        _ ≤ C * (d * ‖rho.toH1Function.gradToHilbertVectorL2‖) := by
          gcongr
          exact rho.toH1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
        _ = C * d * ‖rho.toH1Function.gradToHilbertVectorL2‖ := by ring
    have hrhoGradBound : ‖rho.toH1Function.gradToHilbertVectorL2‖ ≤
        ‖D.gradToHilbertVectorL2‖ + ‖H.gradToHilbertVectorL2‖ := by
      rw [hrho, sub_eq_add_neg, H1Function.gradToHilbertVectorL2_add,
        ← neg_one_smul ℝ H, H1Function.gradToHilbertVectorL2_smul,
        neg_one_smul]
      simpa only [norm_neg] using
        norm_add_le D.gradToHilbertVectorL2 (-H.gradToHilbertVectorL2)
    calc
      ‖((u n) - ulim).toScalarL2‖ = ‖D.toScalarL2‖ := rfl
      _ ≤ ‖H.toScalarL2‖ + ‖rho.toH1Function.toScalarL2‖ := hscalar
      _ ≤ ‖H.toScalarL2‖ +
          C * d * ‖rho.toH1Function.gradToHilbertVectorL2‖ := by
        gcongr
      _ ≤ ‖H.toScalarL2‖ +
          C * d * (‖D.gradToHilbertVectorL2‖ +
            ‖H.gradToHilbertVectorL2‖) := by
        gcongr
      _ = ‖((h n) - hlim).toScalarL2‖ +
          C * d * (‖((u n) - ulim).gradToHilbertVectorL2‖ +
            ‖((h n) - hlim).gradToHilbertVectorL2‖) := rfl
  have hright : Filter.Tendsto
      (fun n ↦ ‖((h n) - hlim).toScalarL2‖ +
        C * d * (‖((u n) - ulim).gradToHilbertVectorL2‖ +
          ‖((h n) - hlim).gradToHilbertVectorL2‖))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      hhValue.add ((huGrad.add hhGrad).const_mul (C * d))
  exact squeeze_zero (fun n ↦ norm_nonneg _) hbound hright

/-- Convergence in the integral `l2NormOn` gradient carrier is convergence of
the canonical Hilbert-valued Sobolev gradient realization. -/
theorem tendsto_norm_gradToHilbertVectorL2_sub_of_l2NormOn
    {W : Set (Vec d)} (hWm : MeasurableSet W)
    {u : ℕ → H1Function W} {ulim : H1Function W}
    (hgrad : Filter.Tendsto
      (fun n ↦ Section5Support.l2NormOn W
        (fun x ↦ (u n).grad x - ulim.grad x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ ‖((u n) - ulim).gradToHilbertVectorL2‖)
      Filter.atTop (nhds 0) := by
  apply hgrad.congr'
  filter_upwards with n
  symm
  change ‖toHilbertVectorL2OfVecField
    ((u n) - ulim).grad_memVectorL2‖ = _
  rw [norm_toHilbertVectorL2OfVecField_eq_l2NormOn hWm
    ((u n) - ulim).grad_memVectorL2]
  congr 1
  funext x
  rw [H1Function.sub_grad]

/-- Full fixed-coefficient Dirichlet stability under convergence of `H¹`
boundary extensions.  The two conclusions are respectively convergence of
the value and gradient `L²` realizations, i.e. the two components needed for
the project's witness-based `H¹` carrier. -/
theorem tendsto_fixedCoefficientDirichletSolution_H1_of_boundaryData
    [NeZero d] {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {a : Vec d → ℝ} {lambda Lambda : ℝ}
    {u h : ℕ → H1Function W} {ulim hlim : H1Function W}
    (hlambda : 0 < lambda) (hLambda : 0 ≤ Lambda)
    (halow : ∀ x ∈ W, lambda ≤ a x) (haup : ∀ x ∈ W, a x ≤ Lambda)
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    (hu : ∀ n, IsWeaklyHarmonicOn a W (u n))
    (hulim : IsWeaklyHarmonicOn a W ulim)
    (huTrace : ∀ n, HasZeroTraceDifferenceOn W (u n) (h n))
    (hulimTrace : HasZeroTraceDifferenceOn W ulim hlim)
    (hhValue : Filter.Tendsto
      (fun n ↦ ‖((h n) - hlim).toScalarL2‖) Filter.atTop (nhds 0))
    (hhGrad : Filter.Tendsto
      (fun n ↦ Section5Support.l2NormOn W
        (fun x ↦ (h n).grad x - hlim.grad x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ ‖((u n) - ulim).toScalarL2‖)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n ↦ ‖((u n) - ulim).gradToHilbertVectorL2‖)
        Filter.atTop (nhds 0) := by
  have hWm : MeasurableSet W := hW.isOpen.measurableSet
  have huGradL2 := tendsto_l2NormOn_gradDifference_of_boundaryData
    hWm hlambda hLambda halow haup hEll hu hulim huTrace hulimTrace hhGrad
  have huGrad :=
    tendsto_norm_gradToHilbertVectorL2_sub_of_l2NormOn hWm huGradL2
  have hhGradHilbert :=
    tendsto_norm_gradToHilbertVectorL2_sub_of_l2NormOn hWm hhGrad
  exact ⟨tendsto_norm_toScalarL2_sub_of_boundaryData hW huTrace hulimTrace
    hhValue huGrad hhGradHilbert, huGrad⟩

/-- Full `H¹` stability for scalar Dirichlet solutions with one fixed boundary
datum and locally uniformly convergent coefficients.  This composes the
coefficient-perturbation energy estimate with zero-trace Poincare. -/
theorem tendsto_dirichletSolution_H1_of_tendstoUniformlyOn
    [NeZero d] {W K : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {a : ℕ → Vec d → ℝ} {alim : Vec d → ℝ}
    {u : ℕ → H1Function W} {ulim h : H1Function W}
    {lambda LambdaLim : ℝ} {Lambda : ℕ → ℝ}
    (hWK : W ⊆ K) (hlambda : 0 < lambda)
    (halow : ∀ n x, x ∈ W → lambda ≤ a n x)
    (haEll : ∀ n,
      IsEllipticFieldOn lambda (Lambda n) W (scalarCoeffField (a n)))
    (halimEll : IsEllipticFieldOn lambda LambdaLim W (scalarCoeffField alim))
    (haLim : TendstoUniformlyOn a alim Filter.atTop K)
    (huTrace : ∀ n, HasZeroTraceDifferenceOn W (u n) h)
    (hulimTrace : HasZeroTraceDifferenceOn W ulim h)
    (huHarm : ∀ n, IsWeaklyHarmonicOn (a n) W (u n))
    (hulimHarm : IsWeaklyHarmonicOn alim W ulim) :
    Filter.Tendsto (fun n ↦ ‖((u n) - ulim).toScalarL2‖)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n ↦ ‖((u n) - ulim).gradToHilbertVectorL2‖)
        Filter.atTop (nhds 0) := by
  have hWm : MeasurableSet W := hW.isOpen.measurableSet
  have huGradL2 := tendsto_l2NormOn_gradDifference_of_tendstoUniformlyOn
    hWm hWK hlambda halow haEll halimEll haLim huTrace hulimTrace
      huHarm hulimHarm
  have huGrad :=
    tendsto_norm_gradToHilbertVectorL2_sub_of_l2NormOn hWm huGradL2
  have hhValue : Filter.Tendsto
      (fun _n : ℕ ↦ ‖(h - h).toScalarL2‖) Filter.atTop (nhds 0) := by
    simp
  have hhGrad : Filter.Tendsto
      (fun _n : ℕ ↦ ‖(h - h).gradToHilbertVectorL2‖)
      Filter.atTop (nhds 0) := by
    simp
  exact ⟨tendsto_norm_toScalarL2_sub_of_boundaryData hW huTrace hulimTrace
    hhValue huGrad hhGrad, huGrad⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
