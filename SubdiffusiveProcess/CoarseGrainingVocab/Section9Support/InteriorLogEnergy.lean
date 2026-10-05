module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.InteriorPositiveComposition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserCutoffEnergy

@[expose] public section

/-!
# The logarithmic Caccioppoli estimate

Testing a positive harmonic function with `eta²/u` bounds the energy of
`log u` by `4 * Lam / lam` times the cutoff energy. The auxiliary bounds
used to construct the logarithm and reciprocal disappear from this estimate.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

private theorem integrable_mul_bounded {d : ℕ} {U : Set (Vec d)}
    {a f : Vec d → ℝ} {M : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict U))
    (hbound : ∀ᵐ x ∂volume.restrict U, |a x| ≤ M)
    (hf : IntegrableOn f U) : IntegrableOn (fun x => a x * f x) U := by
  refine (hf.abs.const_mul M).mono' (ha.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hbound] with x hx
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_right hx (abs_nonneg (f x))

/-- The reciprocal test gives the logarithmic energy bound. Only the
ellipticity ratio occurs in the resulting constant. -/
theorem interior_log_caccioppoli_cutoff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ} {lam Lam : ℝ}
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict U))
    (hab : ∀ᵐ x ∂volume.restrict U, lam ≤ a x ∧ a x ≤ Lam)
    (u : H1Function U) (hu : IsWeaklyHarmonicOn a U u)
    {epsilon M : ℝ} (hepsilon : 0 < epsilon) (hM : 0 ≤ M)
    (hub : ∀ᵐ x ∂volume.restrict U, epsilon ≤ u.toFun x ∧ |u.toFun x| ≤ M)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    (hetaRange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    ∃ w : H1Function U,
      w.toFun = (fun x => Real.log (u.toFun x)) ∧
      w.grad = (fun x i => (u.toFun x)⁻¹ * u.grad x i) ∧
      (∫ x in U, eta x ^ 2 * vecNormSq (w.grad x)) ≤
        (4 * Lam / lam) * ∫ x in U, vecNormSq (euclideanGradient eta x) := by
  obtain ⟨w, f, hw, hf, hwg, hfg⟩ := exists_interior_log_reciprocal hU u hepsilon hM hub
  refine ⟨w, hw, hwg, ?_⟩
  let E : Vec d → ℝ := fun x => eta x ^ 2 * vecNormSq (w.grad x)
  let A : Vec d → ℝ := fun x => a x * E x
  let B : Vec d → ℝ := fun x => vecNormSq (euclideanGradient eta x)
  let T : Vec d → ℝ := fun x => vecDot (w.grad x) ((2 * eta x) • euclideanGradient eta x)
  have habs : ∀ᵐ x ∂volume.restrict U, |a x| ≤ Lam := by
    filter_upwards [hab] with x hx
    rw [abs_of_nonneg (hlam.le.trans hx.1)]
    exact hx.2
  have hE : IntegrableOn E U := by
    apply integrable_mul_bounded (a := fun x => eta x ^ 2) (M := 1)
      (heta.continuous.aestronglyMeasurable.pow 2)
    · exact Eventually.of_forall fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hetaRange x).1, (hetaRange x).2]
    · exact integrableOn_vecNormSq_h1Grad w
  have hA : IntegrableOn A U := integrable_mul_bounded ha habs hE
  have hB : IntegrableOn B U :=
    ((continuous_vecNormSq_euclideanGradient_of_contDiff heta).integrable_of_hasCompactSupport
      (hasCompactSupport_vecNormSq_euclideanGradient hetac)).integrableOn
  have hgradEta : MemVectorL2 U (euclideanGradient eta) := by
    rw [MemVectorL2]
    apply MemLp.of_eval
    intro i
    exact ((contDiff_euclideanCoordDeriv heta i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv hetac i)).restrict U
  have hT : IntegrableOn T U := by
    have hdot := integrableOn_vecDot_of_memVectorL2 w.grad_memVectorL2 hgradEta
    have ht := integrable_mul_bounded
      (a := fun x => 2 * eta x) (M := 2)
      (aestronglyMeasurable_const.mul heta.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) (hetaRange x).1)]
        linarith [(hetaRange x).2]) hdot
    simpa only [T, vecDot_smul_right] using ht
  have haT : IntegrableOn (fun x => a x * T x) U := integrable_mul_bounded ha habs hT
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => eta x ^ 2) := heta.pow 2
  have hcompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using! hetac.mul_right (f' := eta)
  have hsupport : tsupport (fun x => eta x ^ 2) ⊆ U := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := eta) (g := eta)).trans hetasub
  let psi := f.mulContDiffHasCompactSupportToH10 hU hsmooth hcompact hsupport
  have hpsi := WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
    f hU hsmooth hcompact hsupport
  have hid : (∫ x in U, A x) = ∫ x in U, a x * T x := by
    have hweak := hu psi
    have heq : (fun x => vecDot (a x • u.grad x) (psi.toH1Function.grad x))
        =ᵐ[volume.restrict U] fun x => -A x + a x * T x := by
      filter_upwards [hpsi] with x hx
      rw [hx]
      simp_rw [Section6BoundedMultiplier.fderiv_cutoff_sq_apply eta heta]
      dsimp only [A, E, T]
      rw [hwg, hf, hfg]
      simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, euclideanGradient, euclideanCoordDeriv]
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hAn : IntegrableOn (fun x => -A x) U := hA.neg
    rw [integral_congr_ae heq, integral_add hAn haT, integral_neg] at hweak
    linarith
  have hpoint : ∀ᵐ x ∂volume.restrict U,
      a x * T x ≤ A x / 2 + 2 * Lam * B x := by
    filter_upwards [hab] with x hx
    have ha0 : 0 ≤ a x := hlam.le.trans hx.1
    have ht := WeakPoissonEquationOn.abs_sq_cutoff_error_integrand_le
      (eta x) 1 (w.grad x) (euclideanGradient eta x)
    have ht' : |T x| ≤ E x / 2 + 2 * B x := by
      change |vecDot (w.grad x) (fun j => 2 * eta x * euclideanGradient eta x j)| ≤ _
      simpa only [E, B, one_mul, one_pow, mul_assoc] using ht
    calc
      a x * T x ≤ a x * |T x| := mul_le_mul_of_nonneg_left (le_abs_self _) ha0
      _ ≤ a x * (E x / 2 + 2 * B x) := mul_le_mul_of_nonneg_left ht' ha0
      _ ≤ A x / 2 + 2 * Lam * B x := by
        dsimp only [A]
        nlinarith [mul_le_mul_of_nonneg_right hx.2 (vecNormSq_nonneg (euclideanGradient eta x))]
  have hbound := integral_mono_ae haT ((hA.div_const 2).add (hB.const_mul (2 * Lam))) hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hA.div_const 2) (hB.const_mul (2 * Lam)),
    integral_div, integral_const_mul, ← hid] at hbound
  have hlow : lam * ∫ x in U, E x ≤ ∫ x in U, A x := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hE.const_mul lam) hA
    filter_upwards [hab] with x hx
    exact mul_le_mul_of_nonneg_right hx.1
      (mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
  have hresult : (∫ x in U, E x) ≤ (4 * Lam * ∫ x in U, B x) / lam := by
    apply (le_div_iff₀ hlam).mpr
    linarith
  simpa only [E, B, div_mul_eq_mul_div] using hresult

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
