module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TruncationCaccioppoli
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.EnergyIntegrand

@[expose] public section

/-!
# Cutoff energy for measurable scalar coefficients

Testing with `eta² u` gives Caccioppoli with the explicit factor
`4 * Lam / lam`. The product `eta u` then has gradient energy bounded by
`(8 * Lam / lam + 2) * ∫ u² |∇eta|²`. In particular this factor is `34`
when `1/2 ≤ a ≤ 2`. No regularity of the coefficient beyond measurability
is used, and all integrability requirements are proved from the `H¹` data.
-/

set_option autoImplicit false
noncomputable section

open Homogenization MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ} {U : Set (Vec d)}

private theorem integrable_mul_bounded {a f : Vec d → ℝ} {M : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict U))
    (hbound : ∀ᵐ x ∂volume.restrict U, |a x| ≤ M)
    (hf : IntegrableOn f U) : IntegrableOn (fun x => a x * f x) U := by
  refine (hf.abs.const_mul M).mono' (ha.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hbound] with x hx
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_right hx (abs_nonneg (f x))

private theorem cutoff_value_gradient_memVectorL2
    (u : H1Function U) {eta : Vec d → ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetac : HasCompactSupport eta) :
    MemVectorL2 U (fun x => u.toFun x • euclideanGradient eta x) := by
  rw [MemVectorL2]
  apply MemLp.of_eval
  intro i
  have hm : MemLp (fun x => euclideanGradient eta x i) ⊤ (volumeMeasureOn U) :=
    (contDiff_euclideanCoordDeriv heta i).continuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv hetac i) _
  change MemLp (fun x => u.toFun x * euclideanGradient eta x i) 2 (volumeMeasureOn U)
  simpa only [mul_comm] using u.memL2.mul' (r := 2) hm

/-- The squared-cutoff energy estimate, with linear ellipticity-ratio dependence. -/
theorem moser_caccioppoli_cutoff
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ} {lam Lam : ℝ}
    (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volume.restrict U))
    (habounds : ∀ᵐ x ∂volume.restrict U, lam ≤ a x ∧ a x ≤ Lam)
    (u : H1Function U) (hu : IsWeaklyHarmonicOn a U u)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    (hetaRange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    ∫ x in U, eta x ^ 2 * vecNormSq (u.grad x) ≤
      (4 * Lam / lam) *
        ∫ x in U, u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x) := by
  let E : Vec d → ℝ := fun x => eta x ^ 2 * vecNormSq (u.grad x)
  let A : Vec d → ℝ := fun x => a x * E x
  let B : Vec d → ℝ := fun x => u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)
  let T : Vec d → ℝ := fun x =>
    u.toFun x * vecDot (u.grad x) ((2 * eta x) • euclideanGradient eta x)
  have habs : ∀ᵐ x ∂volume.restrict U, |a x| ≤ Lam := by
    filter_upwards [habounds] with x hx
    rw [abs_of_nonneg (hlam.le.trans hx.1)]
    exact hx.2
  have hE : IntegrableOn E U := by
    apply integrable_mul_bounded (a := fun x => eta x ^ 2) (M := 1)
      (heta.continuous.aestronglyMeasurable.pow 2)
    · exact Eventually.of_forall fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hetaRange x).1, (hetaRange x).2]
    · exact integrableOn_vecNormSq_h1Grad u
  have hA : IntegrableOn A U := integrable_mul_bounded hameas habs hE
  have hB : IntegrableOn B U := by
    have hb := WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (continuous_vecNormSq_euclideanGradient_of_contDiff heta)
      (hasCompactSupport_vecNormSq_euclideanGradient hetac) u.memL2.integrable_sq
    exact hb.congr_fun (fun x _ => mul_comm _ _) hU.isOpen.measurableSet
  have hdot : IntegrableOn
      (fun x => vecDot (u.grad x) (u.toFun x • euclideanGradient eta x)) U :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2
      (cutoff_value_gradient_memVectorL2 u heta hetac)
  have hT : IntegrableOn T U := by
    have ht := integrable_mul_bounded
      (a := fun x => 2 * eta x) (M := 2)
      (aestronglyMeasurable_const.mul heta.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) (hetaRange x).1)]
        linarith [(hetaRange x).2]) hdot
    apply ht.congr_fun _ hU.isOpen.measurableSet
    intro x _
    dsimp only [T]
    rw [vecDot_smul_right, vecDot_smul_right]
    ring
  have haT : IntegrableOn (fun x => a x * T x) U :=
    integrable_mul_bounded hameas habs hT
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => eta x ^ 2) := heta.pow 2
  have hcompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using! hetac.mul_right (f' := eta)
  have hsupport : tsupport (fun x => eta x ^ 2) ⊆ U := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := eta) (g := eta)).trans hetasub
  let psi := u.mulContDiffHasCompactSupportToH10 hU hsmooth hcompact hsupport
  have hpsi := WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
    u hU hsmooth hcompact hsupport
  have hid : ∫ x in U, A x = -∫ x in U, a x * T x := by
    have hweak := hu psi
    have heq : (fun x => vecDot (a x • u.grad x) (psi.toH1Function.grad x))
        =ᵐ[volume.restrict U] fun x => A x + a x * T x := by
      filter_upwards [hpsi] with x hx
      rw [hx]
      simp_rw [Section6BoundedMultiplier.fderiv_cutoff_sq_apply eta heta]
      dsimp only [A, E, T]
      simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, euclideanGradient, euclideanCoordDeriv]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [integral_congr_ae heq, integral_add hA haT] at hweak
    linarith
  have hpoint : ∀ᵐ x ∂volume.restrict U,
      |a x * T x| ≤ A x / 2 + 2 * Lam * B x := by
    filter_upwards [habounds] with x hx
    have ha0 : 0 ≤ a x := hlam.le.trans hx.1
    have ht := WeakPoissonEquationOn.abs_sq_cutoff_error_integrand_le
      (eta x) (u.toFun x) (u.grad x) (euclideanGradient eta x)
    have ht' : |T x| ≤ E x / 2 + 2 * B x := by
      change |u.toFun x * vecDot (u.grad x)
        (fun j => 2 * eta x * euclideanGradient eta x j)| ≤ _
      simpa only [E, B, mul_assoc] using ht
    have hB0 : 0 ≤ B x := mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    calc
      |a x * T x| = a x * |T x| := by rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ a x * (E x / 2 + 2 * B x) := mul_le_mul_of_nonneg_left ht' ha0
      _ ≤ A x / 2 + 2 * Lam * B x := by
        dsimp only [A]
        nlinarith [mul_le_mul_of_nonneg_right hx.2 hB0]
  have hbound := Section6BoundedMultiplier.integral_le_two_mul_integral_of_eq_neg_of_abs_le
    hA haT (hB.const_mul (2 * Lam)) hid hpoint
  rw [integral_const_mul] at hbound
  have hlow : lam * ∫ x in U, E x ≤ ∫ x in U, A x := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hE.const_mul lam) hA
    filter_upwards [habounds] with x hx
    exact mul_le_mul_of_nonneg_right hx.1
      (mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
  have hresult : (∫ x in U, E x) ≤ (4 * Lam * ∫ x in U, B x) / lam := by
    apply (le_div_iff₀ hlam).mpr
    nlinarith
  simpa only [E, B, div_mul_eq_mul_div] using hresult

/-- The `H¹` cutoff product has controlled full gradient at ratio four. -/
theorem moser_cutoff_gradient_energy
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ}
    (hameas : AEStronglyMeasurable a (volume.restrict U))
    (habounds : ∀ᵐ x ∂volume.restrict U, 1 / 2 ≤ a x ∧ a x ≤ 2)
    (u : H1Function U) (hu : IsWeaklyHarmonicOn a U u)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    (hetaRange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    let w := u.mulContDiffHasCompactSupport heta hetac
    ∫ x in U, vecNormSq (w.grad x) ≤
      34 * ∫ x in U, u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x) := by
  dsimp only
  have hbase := moser_caccioppoli_cutoff hU (by norm_num : (0 : ℝ) < 1 / 2)
    hameas habounds u hu heta hetac hetasub hetaRange
  norm_num only [show (4 * (2 : ℝ) / (1 / 2)) = 16 by norm_num] at hbase
  have hE : IntegrableOn (fun x => eta x ^ 2 * vecNormSq (u.grad x)) U := by
    apply integrable_mul_bounded (a := fun x => eta x ^ 2) (M := 1)
      (heta.continuous.aestronglyMeasurable.pow 2)
    · exact Eventually.of_forall fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hetaRange x).1, (hetaRange x).2]
    · exact integrableOn_vecNormSq_h1Grad u
  have hB : IntegrableOn
      (fun x => u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) U := by
    have hb := WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (continuous_vecNormSq_euclideanGradient_of_contDiff heta)
      (hasCompactSupport_vecNormSq_euclideanGradient hetac) u.memL2.integrable_sq
    exact hb.congr_fun (fun x _ => mul_comm _ _) hU.isOpen.measurableSet
  have hprod := integral_mono_ae
    (integrableOn_vecNormSq_h1Grad (u.mulContDiffHasCompactSupport heta hetac))
    ((hE.const_mul 2).add (hB.const_mul 2))
    (Eventually.of_forall fun x => show
      vecNormSq ((u.mulContDiffHasCompactSupport heta hetac).grad x) ≤
        2 * (eta x ^ 2 * vecNormSq (u.grad x)) +
          2 * (u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) from by
      rw [H1Function.mulContDiffHasCompactSupport_grad]
      exact (vecNormSq_add_le (eta x • u.grad x)
        (u.toFun x • euclideanGradient eta x)).trans_eq (by
          rw [vecNormSq_smul, vecNormSq_smul]
          ring))
  simp only [Pi.add_apply] at hprod
  rw [integral_add (hE.const_mul 2) (hB.const_mul 2),
    integral_const_mul, integral_const_mul] at hprod
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
