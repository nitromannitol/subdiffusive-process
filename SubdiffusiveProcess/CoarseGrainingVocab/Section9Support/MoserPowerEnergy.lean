module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerTests

@[expose] public section

/-!
# Arbitrary-power Caccioppoli estimates

Testing with the nonlinear power pair gives cutoff gradient energy at most
`34 s²` times the cutoff error for `u₊^s`. The qualitative bound used to
construct the power pair has disappeared from the estimate.
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

/-- Caccioppoli for an arbitrary real power at ellipticity ratio four. -/
theorem moser_power_caccioppoli_cutoff
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ}
    (hameas : AEStronglyMeasurable a (volume.restrict U))
    (habounds : ∀ᵐ x ∂volume.restrict U, 1 / 2 ≤ a x ∧ a x ≤ 2)
    (u w f : H1Function U) (hu : IsWeaklyHarmonicOn a U u)
    {s : ℝ} (hs : 1 ≤ s) (hpair : MoserPowerPair u w f s)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    (hetaRange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    ∫ x in U, eta x ^ 2 * vecNormSq (w.grad x) ≤
      (16 * s ^ 2) * ∫ x in U, w.toFun x ^ 2 * vecNormSq (euclideanGradient eta x) := by
  let E : Vec d → ℝ := fun x => eta x ^ 2 * vecNormSq (w.grad x)
  let A : Vec d → ℝ := fun x => a x * ((2 * s - 1) * E x)
  let B : Vec d → ℝ := fun x => w.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)
  let T : Vec d → ℝ := fun x =>
    w.toFun x * vecDot (w.grad x) ((2 * eta x) • euclideanGradient eta x)
  have habs : ∀ᵐ x ∂volume.restrict U, |a x| ≤ 2 := by
    filter_upwards [habounds] with x hx
    rw [abs_of_nonneg (by linarith : 0 ≤ a x)]
    exact hx.2
  have hE : IntegrableOn E U := by
    apply integrable_mul_bounded (a := fun x => eta x ^ 2) (M := 1)
      (heta.continuous.aestronglyMeasurable.pow 2)
    · exact Eventually.of_forall fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hetaRange x).1, (hetaRange x).2]
    · exact integrableOn_vecNormSq_h1Grad w
  have hA : IntegrableOn A U := integrable_mul_bounded hameas habs (hE.const_mul _)
  have hB : IntegrableOn B U := by
    have hb := WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (continuous_vecNormSq_euclideanGradient_of_contDiff heta)
      (hasCompactSupport_vecNormSq_euclideanGradient hetac) w.memL2.integrable_sq
    exact hb.congr_fun (fun x _ => mul_comm _ _) hU.isOpen.measurableSet
  have hdot : IntegrableOn
      (fun x => vecDot (w.grad x) (w.toFun x • euclideanGradient eta x)) U :=
    integrableOn_vecDot_of_memVectorL2 w.grad_memVectorL2
      (cutoff_value_gradient_memVectorL2 w heta hetac)
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
  have haT : IntegrableOn (fun x => a x * (s * T x)) U :=
    integrable_mul_bounded hameas habs (hT.const_mul s)
  have hid : ∫ x in U, A x = -∫ x in U, a x * (s * T x) := by
    have hweak := moser_power_test_identity hU u w f hu hpair heta hetac hetasub
    change (∫ x in U, a x * ((2 * s - 1) * E x + s * T x)) = 0 at hweak
    simp_rw [mul_add] at hweak
    rw [integral_add hA haT] at hweak
    linarith
  have hpoint : ∀ᵐ x ∂volume.restrict U,
      |a x * (s * T x)| ≤ A x / 2 + (4 * s ^ 2) * B x := by
    filter_upwards [habounds] with x hx
    have ha0 : 0 ≤ a x := by linarith
    have ht := WeakPoissonEquationOn.abs_sq_cutoff_error_integrand_le
      (eta x) (s * w.toFun x) (w.grad x) (euclideanGradient eta x)
    have ht' : |s * T x| ≤ E x / 2 + (2 * s ^ 2) * B x := by
      change |s * (w.toFun x * vecDot (w.grad x)
        (fun j => 2 * eta x * euclideanGradient eta x j))| ≤ _
      simpa only [E, B, mul_pow, mul_assoc] using ht
    have hE0 : 0 ≤ E x := mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    have hB0 : 0 ≤ B x := mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    calc
      |a x * (s * T x)| = a x * |s * T x| := by rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ a x * (E x / 2 + (2 * s ^ 2) * B x) := mul_le_mul_of_nonneg_left ht' ha0
      _ ≤ A x / 2 + (4 * s ^ 2) * B x := by
        dsimp only [A]
        have h1 := mul_nonneg (by linarith : 0 ≤ s - 1) (mul_nonneg ha0 hE0)
        have h2 := mul_le_mul_of_nonneg_right hx.2 (mul_nonneg (sq_nonneg s) hB0)
        nlinarith only [h1, h2]
  have hbound := Section6BoundedMultiplier.integral_le_two_mul_integral_of_eq_neg_of_abs_le
    hA haT (hB.const_mul (4 * s ^ 2)) hid hpoint
  rw [integral_const_mul] at hbound
  have hlow : (1 / 2 : ℝ) * ∫ x in U, E x ≤ ∫ x in U, A x := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hE.const_mul _) hA
    filter_upwards [habounds] with x hx
    have hE0 : 0 ≤ E x := mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_right hx.1 hE0
    have h2 := mul_nonneg (by linarith : 0 ≤ s - 1)
      (mul_nonneg (by linarith : 0 ≤ a x) hE0)
    dsimp only [A]
    nlinarith only [h1, h2]
  change (∫ x in U, E x) ≤ (16 * s ^ 2) * ∫ x in U, B x
  linarith

/-- The full gradient of the cutoff power has a polynomial constant in the power. -/
theorem moser_power_cutoff_gradient_energy
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ}
    (hameas : AEStronglyMeasurable a (volume.restrict U))
    (habounds : ∀ᵐ x ∂volume.restrict U, 1 / 2 ≤ a x ∧ a x ≤ 2)
    (u w f : H1Function U) (hu : IsWeaklyHarmonicOn a U u)
    {s : ℝ} (hs : 1 ≤ s) (hpair : MoserPowerPair u w f s)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    (hetaRange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    ∫ x in U, vecNormSq ((w.mulContDiffHasCompactSupport heta hetac).grad x) ≤
      (34 * s ^ 2) * ∫ x in U, w.toFun x ^ 2 * vecNormSq (euclideanGradient eta x) := by
  have hbase := moser_power_caccioppoli_cutoff hU hameas habounds u w f hu hs hpair
    heta hetac hetasub hetaRange
  have hE : IntegrableOn (fun x => eta x ^ 2 * vecNormSq (w.grad x)) U := by
    apply integrable_mul_bounded (a := fun x => eta x ^ 2) (M := 1)
      (heta.continuous.aestronglyMeasurable.pow 2)
    · exact Eventually.of_forall fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hetaRange x).1, (hetaRange x).2]
    · exact integrableOn_vecNormSq_h1Grad w
  have hB : IntegrableOn
      (fun x => w.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) U := by
    have hb := WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (continuous_vecNormSq_euclideanGradient_of_contDiff heta)
      (hasCompactSupport_vecNormSq_euclideanGradient hetac) w.memL2.integrable_sq
    exact hb.congr_fun (fun x _ => mul_comm _ _) hU.isOpen.measurableSet
  have hprod := integral_mono_ae
    (integrableOn_vecNormSq_h1Grad (w.mulContDiffHasCompactSupport heta hetac))
    ((hE.const_mul 2).add (hB.const_mul 2))
    (Eventually.of_forall fun x => show
      vecNormSq ((w.mulContDiffHasCompactSupport heta hetac).grad x) ≤
        2 * (eta x ^ 2 * vecNormSq (w.grad x)) +
          2 * (w.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) from by
      rw [H1Function.mulContDiffHasCompactSupport_grad]
      exact (vecNormSq_add_le (eta x • w.grad x)
        (w.toFun x • euclideanGradient eta x)).trans_eq (by
          rw [vecNormSq_smul, vecNormSq_smul]
          ring))
  simp only [Pi.add_apply] at hprod
  rw [integral_add (hE.const_mul 2) (hB.const_mul 2),
    integral_const_mul, integral_const_mul] at hprod
  have hB0 : 0 ≤ ∫ x in U, w.toFun x ^ 2 * vecNormSq (euclideanGradient eta x) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
  have hsB := mul_nonneg (show 0 ≤ s ^ 2 - 1 by nlinarith) hB0
  nlinarith only [hbase, hprod, hsB]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
