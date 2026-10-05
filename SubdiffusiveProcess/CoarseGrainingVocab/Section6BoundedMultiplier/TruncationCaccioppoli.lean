module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import Homogenization.Sobolev.Truncation.Basic
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1

@[expose] public section

/-!
# Truncation tests for scalar weakly harmonic functions

This file builds the exact `H¹₀` test used in the Caccioppoli step of Moser
iteration.  It uses only CoarseGraining's Sobolev API: positive-part
truncation, multiplication by a smooth compactly supported cutoff, and
uniqueness of the weak gradient of the chosen zero-trace representative.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Filter MeasureTheory Homogenization
open scoped ENNReal BigOperators Topology

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Pointwise Young inequality in the exact scaling used to absorb the cross
term in scalar Caccioppoli.  The deliberately crude right-hand side records
only `Lam / lam` dependence. -/
theorem truncationCrossTerm_young {lam Lam a eta value : ℝ}
    (hlam : 0 < lam) (hala : lam ≤ a) (haL : a ≤ Lam)
    (V Deta : Vec d) :
    |a * value * vecDot V ((2 * eta) • Deta)| ≤
      lam * eta ^ 2 * vecNormSq V / 2 +
        2 * Lam ^ 2 / lam * value ^ 2 * vecNormSq Deta := by
  have hsqrt : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hlam).ne'
  have hYoung := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    (Real.sqrt lam * eta) ((2 * a * value) / Real.sqrt lam) V Deta
  have hleft :
      |a * value * vecDot V ((2 * eta) • Deta)| =
        |(Real.sqrt lam * eta) * ((2 * a * value) / Real.sqrt lam) *
          vecDot V Deta| := by
    rw [vecDot_smul_right]
    field_simp
  rw [hleft]
  refine hYoung.trans ?_
  have hsqrtSq : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam.le
  have ha0 : 0 ≤ a := hlam.le.trans hala
  have hLam0 : 0 ≤ Lam := ha0.trans haL
  have haSq : a ^ 2 ≤ Lam ^ 2 := by nlinarith
  rw [mul_pow, hsqrtSq]
  have hdiv : ((2 * a * value) / Real.sqrt lam) ^ 2 =
      4 * a ^ 2 * value ^ 2 / lam := by
    rw [div_pow, hsqrtSq]
    ring
  rw [hdiv]
  have hsecond :
      (4 * a ^ 2 * value ^ 2 / lam) * vecNormSq Deta / 2 ≤
        2 * Lam ^ 2 / lam * value ^ 2 * vecNormSq Deta := by
    have hnonneg : 0 ≤ value ^ 2 * vecNormSq Deta :=
      mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    have := mul_le_mul_of_nonneg_right haSq hnonneg
    calc
      (4 * a ^ 2 * value ^ 2 / lam) * vecNormSq Deta / 2 =
          (2 / lam) * (a ^ 2 * (value ^ 2 * vecNormSq Deta)) := by ring
      _ ≤ (2 / lam) * (Lam ^ 2 * (value ^ 2 * vecNormSq Deta)) := by
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * Lam ^ 2 / lam * value ^ 2 * vecNormSq Deta := by ring
  exact add_le_add (le_refl _) hsecond

/-- Product-rule readout for the squared cutoff. -/
theorem fderiv_cutoff_sq_apply (eta : Vec d → ℝ)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) =
      2 * eta x * (fderiv ℝ eta x) (basisVec i) := by
  have hdiff : DifferentiableAt ℝ eta x :=
    heta.differentiable (by simp) x
  rw [show (fun y => eta y ^ 2) = eta * eta by
    funext y
    simp [pow_two], fderiv_mul hdiff hdiff]
  simp only [add_apply, smul_apply,
    smul_eq_mul]
  ring

/-- Abstract integral absorption used after the pointwise Young estimate. -/
theorem integral_le_two_mul_integral_of_eq_neg_of_abs_le
    {A cross remainder : Vec d → ℝ}
    (hA : IntegrableOn A U) (hcross : IntegrableOn cross U)
    (hremainder : IntegrableOn remainder U)
    (hidentity : ∫ x in U, A x ∂volume = -∫ x in U, cross x ∂volume)
    (hpoint : ∀ᵐ x ∂(volume.restrict U),
      |cross x| ≤ A x / 2 + remainder x) :
    ∫ x in U, A x ∂volume ≤ 2 * ∫ x in U, remainder x ∂volume := by
  have hhalf : IntegrableOn (fun x => A x / 2) U := hA.div_const 2
  have hsum : IntegrableOn (fun x => A x / 2 + remainder x) U :=
    hhalf.add hremainder
  have habs : |∫ x in U, cross x ∂volume| ≤
      ∫ x in U, |cross x| ∂volume := abs_integral_le_integral_abs
  have hmono : ∫ x in U, |cross x| ∂volume ≤
      ∫ x in U, (A x / 2 + remainder x) ∂volume :=
    setIntegral_mono_ae_restrict hcross.abs hsum hpoint
  have hsplit : ∫ x in U, (A x / 2 + remainder x) ∂volume =
      (∫ x in U, A x ∂volume) / 2 + ∫ x in U, remainder x ∂volume := by
    rw [integral_add hhalf hremainder, integral_div]
  have hle : ∫ x in U, A x ∂volume ≤
      (∫ x in U, A x ∂volume) / 2 + ∫ x in U, remainder x ∂volume := by
    calc
      ∫ x in U, A x ∂volume = -∫ x in U, cross x ∂volume := hidentity
      _ ≤ |∫ x in U, cross x ∂volume| := by
          simpa only [abs_neg] using
            (le_abs_self (-∫ x in U, cross x ∂volume))
      _ ≤ ∫ x in U, |cross x| ∂volume := habs
      _ ≤ ∫ x in U, (A x / 2 + remainder x) ∂volume := hmono
      _ = _ := hsplit
  linarith

/-- The square of a smooth compactly supported cutoff has the same properties
and remains supported in the same open window. -/
private theorem cutoff_sq_data {eta : Vec d → ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetac : HasCompactSupport eta)
    (hetasub : tsupport eta ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => eta x ^ 2) ∧
      HasCompactSupport (fun x => eta x ^ 2) ∧
      tsupport (fun x => eta x ^ 2) ⊆ U := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => eta x ^ 2) := by
    simpa only [pow_two] using heta.mul heta
  have hcompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using! hetac.mul_right
  refine ⟨hsmooth, hcompact, ?_⟩
  simpa only [pow_two] using
    (tsupport_mul_subset_left (f := eta) (g := eta)).trans hetasub

/-- **Localized positive-truncation identity.**

For `v = (u-c)₊` and a smooth compactly supported cutoff `eta`, the weak
equation may be tested against `eta² v`.  The result is returned together with
the exact a.e. truncation gradient, so the next module can estimate the main
and cross terms without any representative ambiguity. -/
theorem exists_truncation_caccioppoli_test
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ}
    (u : H1Function U) (hu : IsWeaklyHarmonicOn a U u) (c : ℝ)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U) :
    ∃ v : H1Function U,
      v.toFun = (fun x => max (u.toFun x - c) 0) ∧
      (∀ᵐ x ∂(volume.restrict U),
        v.grad x = {y | c < u.toFun y}.indicator u.grad x) ∧
      ∫ x in U, vecDot (a x • u.grad x)
          (fun i => eta x ^ 2 * v.grad x i +
            v.toFun x * (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i))
          ∂volume = 0 := by
  obtain ⟨v, hvfun, hvgrad⟩ := exists_h1_max_sub_const hU u c
  obtain ⟨hphis, hphic, hphisub⟩ := cutoff_sq_data heta hetac hetasub
  let phi : Vec d → ℝ := fun x => eta x ^ 2
  let psi : H10Function U :=
    v.mulContDiffHasCompactSupportToH10 hU hphis hphic hphisub
  have hpsiGrad :
      (fun x => psi.toH1Function.grad x) =ᵐ[volume.restrict U]
        fun x i => phi x * v.grad x i +
          v.toFun x * (fderiv ℝ phi x) (basisVec i) := by
    exact WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
      v hU hphis hphic hphisub
  refine ⟨v, hvfun, hvgrad, ?_⟩
  calc
    ∫ x in U, vecDot (a x • u.grad x)
          (fun i => eta x ^ 2 * v.grad x i +
            v.toFun x * (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i))
          ∂volume =
        ∫ x in U, vecDot (a x • u.grad x) (psi.toH1Function.grad x)
          ∂volume := by
            apply integral_congr_ae
            filter_upwards [hpsiGrad] with x hx
            rw [hx]
    _ = 0 := hu psi

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
