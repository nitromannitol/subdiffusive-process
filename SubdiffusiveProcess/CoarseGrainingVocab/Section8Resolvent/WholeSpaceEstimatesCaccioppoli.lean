module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra
public import Homogenization.Sobolev.Foundations.DifferenceQuotientH1
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

@[expose] public section

/-!
# Cutoff energy inequality for the massive divergence equation

This file proves the localized energy (Caccioppoli) inequality for the massive
weak equation `mu u - div (a grad u) = 0` on a bounded open convex domain: for
every smooth cutoff `chi` compactly supported in the domain,

```
mu * ∫ chi^2 * u^2  ≤  2 * ∫ a * u^2 * |grad chi|^2 .
```

Only nonnegativity and a local upper bound of the scalar coefficient are used;
no lower ellipticity bound enters the inequality (ellipticity is used solely to
know that the energy pairing is integrable).

The inequality is the deterministic engine behind the uniqueness clause : letting the cutoff run over an
exhaustion by balls converts a growth bound on `a * u^2` into vanishing of `u`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The support of a square is the support of the function. -/
private theorem support_sq_eq {f : Vec d → ℝ} :
    Function.support (fun x ↦ f x ^ 2) = Function.support f := by
  ext x
  simp [Function.mem_support]

/-- The differential of a square, evaluated on a coordinate direction. -/
private theorem fderiv_sq_apply {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y ↦ f y ^ 2) x) (basisVec i) =
      2 * f x * (fderiv ℝ f x) (basisVec i) := by
  have hdiff : DifferentiableAt ℝ f x :=
    hf.differentiable (by simp : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) x
  have h := (hdiff.hasFDerivAt).pow 2
  rw [h.fderiv]
  simp [mul_comm, mul_assoc]

/-- **Cutoff energy inequality for the massive equation.**

If `w` solves `mu w - div (a grad w) = 0` weakly on a bounded open convex
domain `W` and `chi` is a smooth cutoff compactly supported in `W`, then

```
mu * ∫_W chi^2 w^2 ≤ 2 * ∫_W a w^2 |grad chi|^2 .
```

Source: the localization step. -/
theorem massive_cutoff_sq_le_of_zero_forcing
    {a : Vec d → ℝ} {mu lam Lam : ℝ} {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x)
    (w : H1Function W)
    (hw : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu W w (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    {K : ℝ} (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K) :
    mu * ∫ x in W, chi x ^ 2 * w.toFun x ^ 2 ∂volume ≤
      2 * ∫ x in W, a x * w.toFun x ^ 2 *
          vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume := by
  classical
  set eta : Vec d → ℝ := fun x ↦ chi x ^ 2 with heta_def
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta := hchi.pow 2
  have hetaC : HasCompactSupport eta := by
    apply HasCompactSupport.intro hchiC.isCompact
    intro x hx
    have : chi x = 0 := by
      by_contra hne
      exact hx (subset_closure hne)
    simp [heta_def, this]
  have hetaS : tsupport eta ⊆ W := by
    refine le_trans (closure_mono ?_) hchiS
    exact le_of_eq (support_sq_eq (f := chi))
  set phi : H10Function W :=
    w.mulContDiffHasCompactSupportToH10 hW heta hetaC hetaS with hphi_def
  have hphi_toFun : phi.toH1Function.toFun = fun x ↦ eta x * w.toFun x :=
    H1Function.mulContDiffHasCompactSupportToH10_toFun w hW heta hetaC hetaS
  set psi : H1Function W := w.mulContDiffHasCompactSupport heta hetaC with hpsi_def
  have hpsi_toFun : psi.toFun = fun x ↦ eta x * w.toFun x := by
    simp [hpsi_def]
  have hpsi_grad : psi.grad =
      fun x i ↦ eta x * w.grad x i + w.toFun x * (fderiv ℝ eta x) (basisVec i) := by
    simp [hpsi_def]
  have hgrad : phi.toH1Function.grad =ᵐ[volume.restrict W] psi.grad := by
    refine Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hW.isOpen ?_
    filter_upwards with x
    rw [hphi_toFun, hpsi_toFun]
  have heq := hw phi
  set gchi : Vec d → Vec d := fun x i ↦ (fderiv ℝ chi x) (basisVec i) with hgchi_def
  have hgchi_cont : Continuous gchi := by
    refine continuous_pi fun i ↦ ?_
    exact ((hchi.continuous_fderiv (by simp : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const)
  have hK0 : (0 : ℝ) ≤ K := le_trans (vecNormSq_nonneg _) (hK 0)
  have hnorm_gchi : ∀ x, ‖gchi x‖ ≤ Real.sqrt K := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg K)).mpr fun i ↦ ?_
    have h1 : gchi x i ^ (2 : ℕ) ≤ K :=
      le_trans (sq_apply_le_vecNormSq (gchi x) i) (hK x)
    calc ‖gchi x i‖ = Real.sqrt (gchi x i ^ (2 : ℕ)) := by
          rw [Real.sqrt_sq_eq_abs]; rfl
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h1
  have hF : MemVectorL2 W (fun x ↦ w.toFun x • gchi x) := by
    refine MemLp.mono (w.memL2.const_mul (Real.sqrt K)) ?_ ?_
    · exact w.memL2.aestronglyMeasurable.smul
        hgchi_cont.aestronglyMeasurable
    · filter_upwards with x
      have hle : ‖w.toFun x • gchi x‖ = |w.toFun x| * ‖gchi x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      rw [hle]
      have : |w.toFun x| * ‖gchi x‖ ≤ |w.toFun x| * Real.sqrt K :=
        mul_le_mul_of_nonneg_left (hnorm_gchi x) (abs_nonneg _)
      refine this.trans ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg K)]
      exact le_of_eq (mul_comm _ _)
  have hint_min : IntegrableOn
      (fun x ↦ a x * w.toFun x ^ 2 * vecNormSq (gchi x)) W := by
    have hbase := integrableOn_energy_term hEll hF hF
    refine hbase.congr_fun (fun x _ ↦ ?_) hW.isOpen.measurableSet
    simp [vecDot, vecNormSq, Finset.mul_sum]
    ring_nf
  have hint_energy : IntegrableOn
      (fun x ↦ vecDot (a x • w.grad x) (psi.grad x)) W :=
    integrableOn_energy_term hEll w.grad_memVectorL2 psi.grad_memVectorL2
  have hptwise : ∀ x,
      -(2 * (a x * w.toFun x ^ 2 * vecNormSq (gchi x))) ≤
        vecDot (a x • w.grad x) (psi.grad x) := by
    intro x
    have hd : psi.grad x =
        fun i ↦ chi x ^ 2 * w.grad x i + w.toFun x * (2 * chi x * gchi x i) := by
      rw [hpsi_grad]
      funext i
      simp only [heta_def, hgchi_def, fderiv_sq_apply hchi x i]
    have hexp : vecDot (a x • w.grad x) (psi.grad x) =
        a x * (chi x ^ 2 * vecNormSq (w.grad x) +
          2 * chi x * w.toFun x * vecDot (w.grad x) (gchi x)) := by
      rw [hd]
      simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
      congr 1 <;> exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hyoung := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (chi x) (2 * w.toFun x) (w.grad x) (gchi x)
    have hyoung' : -(chi x ^ 2 * vecNormSq (w.grad x) / 2 +
          (2 * w.toFun x) ^ 2 * vecNormSq (gchi x) / 2) ≤
        chi x * (2 * w.toFun x) * vecDot (w.grad x) (gchi x) :=
      neg_le_of_abs_le hyoung
    have hGnn := vecNormSq_nonneg (w.grad x)
    have hgnn := vecNormSq_nonneg (gchi x)
    have hax := haNonneg x
    rw [hexp]
    nlinarith [mul_nonneg hax (mul_nonneg (sq_nonneg (chi x)) hGnn),
      mul_nonneg hax hgnn, hyoung']
  simp only [one_mul, zero_mul, integral_zero, hphi_toFun, heta_def] at heq
  have hmass : ∫ x in W, w.toFun x * (chi x ^ 2 * w.toFun x) ∂volume =
      ∫ x in W, chi x ^ 2 * w.toFun x ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  have henergy_eq : ∫ x in W, vecDot (a x • w.grad x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in W, vecDot (a x • w.grad x) (psi.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  have hminInt : Integrable
      (fun x ↦ -(2 * (a x * w.toFun x ^ 2 * vecNormSq (gchi x))))
      (volume.restrict W) := ((hint_min.const_mul 2).neg)
  have hmono : ∫ x in W, -(2 * (a x * w.toFun x ^ 2 * vecNormSq (gchi x))) ∂volume ≤
      ∫ x in W, vecDot (a x • w.grad x) (psi.grad x) ∂volume :=
    integral_mono hminInt hint_energy (fun x ↦ hptwise x)
  have hminEq : ∫ x in W, -(2 * (a x * w.toFun x ^ 2 * vecNormSq (gchi x))) ∂volume =
      -(2 * ∫ x in W, a x * w.toFun x ^ 2 * vecNormSq (gchi x) ∂volume) := by
    rw [integral_neg, integral_const_mul]
  rw [hmass, henergy_eq] at heq
  rw [hminEq] at hmono
  linarith


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
