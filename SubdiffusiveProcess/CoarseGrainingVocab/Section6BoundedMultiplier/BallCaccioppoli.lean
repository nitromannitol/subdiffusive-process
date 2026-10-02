import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TruncationCaccioppoli
import Homogenization.Sobolev.Foundations.QuantitativeCutoff
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.EnergyIntegrand

/-!
# Scalar Caccioppoli at contrast at most two

This is the energy input for the small-contrast replacement of the unit-scale
Moser step.  The coefficient has already been divided by its value at the
center, so only the crude bounds `1 ≤ a ≤ 2` are retained.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Filter MeasureTheory Homogenization
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

private def constantH1 (hU : IsOpenBoundedConvexDomain U) (c : ℝ) :
    H1Function U :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
    (contDiff_const : ContDiff ℝ 1 fun _ : Vec d ↦ c)

private theorem constantH1_toFun (hU : IsOpenBoundedConvexDomain U) (c : ℝ) :
    (constantH1 hU c).toFun = fun _ ↦ c := rfl

private theorem constantH1_grad (hU : IsOpenBoundedConvexDomain U) (c : ℝ) :
    (constantH1 hU c).grad = fun _ ↦ (0 : Vec d) := by
  funext x i
  show (fderiv ℝ (fun _ : Vec d ↦ c) x) (basisVec i) = 0
  rw [fderiv_fun_const]
  rfl

private theorem sub_constantH1_data (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    ((u - constantH1 hU c).toFun = fun x ↦ u.toFun x - c) ∧
      (u - constantH1 hU c).grad = u.grad := by
  constructor
  · funext x
    rw [H1Function.sub_toFun, constantH1_toFun]
  · rw [H1Function.sub_grad, constantH1_grad]
    funext x
    exact sub_zero _

private theorem memVectorL2_value_mul_cutoffGradient
    (v : H1Function U) {eta : Vec d → ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetac : HasCompactSupport eta) :
    MemVectorL2 U (fun x i ↦
      v.toFun x * (2 * eta x * euclideanGradient eta x i)) := by
  rw [MemVectorL2]
  apply MemLp.of_eval
  intro i
  have hcoordCont : Continuous (fun x : Vec d ↦
      2 * eta x * euclideanGradient eta x i) := by
    exact (continuous_const.mul heta.continuous).mul
      (contDiff_euclideanCoordDeriv heta i).continuous
  have hcoordCompact : HasCompactSupport (fun x : Vec d ↦
      2 * eta x * euclideanGradient eta x i) := by
    have hdcompact := hasCompactSupport_euclideanCoordDeriv hetac i
    have hleft : HasCompactSupport (fun x : Vec d ↦ 2 * eta x) := by
      simpa only [Pi.mul_apply] using
        (hetac.mul_left (f := fun _ : Vec d ↦ (2 : ℝ)))
    simpa only [Pi.mul_apply] using hleft.mul_right (f' := fun x ↦
      euclideanGradient eta x i)
  have htop : MemLp (fun x : Vec d ↦
      2 * eta x * euclideanGradient eta x i) ⊤ (volumeMeasureOn U) :=
    hcoordCont.memLp_top_of_hasCompactSupport hcoordCompact _
  simpa [MemScalarL2, volumeMeasureOn, mul_comm] using v.memL2.mul' htop

/-- Squared-cutoff Caccioppoli absorption for a scalar coefficient normalized
to lie between `1` and `2`. -/
theorem scalarCaccioppoli_cutoff_of_one_le_of_le_two
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ}
    (hameas : AEStronglyMeasurable a (volumeMeasureOn U))
    (habounds : ∀ᵐ x ∂(volumeMeasureOn U), 1 ≤ a x ∧ a x ≤ 2)
    (u : H1Function U) (hu : IsWeaklyHarmonicOn a U u) (c : ℝ)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    (hetaRange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    ∫ x in U, a x * eta x ^ 2 * vecNormSq (u.grad x) ∂volume ≤
      16 * ∫ x in U, (u.toFun x - c) ^ 2 *
        vecNormSq (euclideanGradient eta x) ∂volume := by
  let v : H1Function U := u - constantH1 hU c
  have hvfun : v.toFun = fun x ↦ u.toFun x - c :=
    (sub_constantH1_data hU u c).1
  have hvgrad : v.grad = u.grad := (sub_constantH1_data hU u c).2
  let A : Vec d → ℝ := fun x ↦
    a x * eta x ^ 2 * vecNormSq (u.grad x)
  let G : Vec d → Vec d := fun x ↦
    v.toFun x • ((2 * eta x) • euclideanGradient eta x)
  let cross : Vec d → ℝ := fun x ↦ a x * vecDot (u.grad x) (G x)
  let remainder : Vec d → ℝ := fun x ↦
    8 * v.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)
  have hgradSq : IntegrableOn (fun x ↦ vecNormSq (u.grad x)) U :=
    integrableOn_vecNormSq_h1Grad u
  have hA : IntegrableOn A U := by
    refine (hgradSq.const_mul 2).mono' ?_ ?_
    · simpa [A, Pi.mul_apply, mul_assoc] using (hameas.mul
        ((heta.continuous.aestronglyMeasurable.pow 2).mul
          hgradSq.aestronglyMeasurable))
    · filter_upwards [habounds] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
          (vecNormSq_nonneg _))]
      have hetaSq : eta x ^ 2 ≤ 1 := by nlinarith [(hetaRange x).1, (hetaRange x).2]
      have hnonneg : 0 ≤ vecNormSq (u.grad x) := vecNormSq_nonneg _
      change a x * eta x ^ 2 * vecNormSq (u.grad x) ≤
        2 * vecNormSq (u.grad x)
      have hcoeff : a x * eta x ^ 2 ≤ 2 := by
        calc
          a x * eta x ^ 2 ≤ a x * 1 :=
            mul_le_mul_of_nonneg_left hetaSq (by linarith)
          _ ≤ 2 := by simpa using hx.2
      exact mul_le_mul_of_nonneg_right hcoeff hnonneg
  have hG : MemVectorL2 U G := by
    simpa [G] using memVectorL2_value_mul_cutoffGradient v heta hetac
  have hdot : IntegrableOn (fun x ↦ vecDot (u.grad x) (G x)) U :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hG
  have hcross : IntegrableOn cross U := by
    refine (hdot.abs.const_mul 2).mono' ?_ ?_
    · simpa [cross, Pi.mul_apply] using hameas.mul hdot.aestronglyMeasurable
    · filter_upwards [habounds] with x hx
      change |a x * vecDot (u.grad x) (G x)| ≤
        2 * |vecDot (u.grad x) (G x)|
      rw [abs_mul]
      have ha : |a x| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; exact hx.2
      exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hvSq : IntegrableOn (fun x ↦ v.toFun x ^ 2) U := by
    simpa [IntegrableOn, volumeMeasureOn] using v.memL2.integrable_sq
  have hfactorCont : Continuous (fun x ↦
      8 * vecNormSq (euclideanGradient eta x)) :=
    continuous_const.mul (continuous_vecNormSq_euclideanGradient_of_contDiff heta)
  have hfactorCompact : HasCompactSupport (fun x ↦
      8 * vecNormSq (euclideanGradient eta x)) := by
    simpa only [Pi.mul_apply] using
      (hasCompactSupport_vecNormSq_euclideanGradient hetac).mul_left
        (f := fun _ : Vec d ↦ (8 : ℝ))
  have hremainder : IntegrableOn remainder U := by
    have hmul := WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      hfactorCont hfactorCompact hvSq
    apply hmul.congr_fun
    · intro x _hx
      dsimp [remainder]
      ring
    · exact hU.isOpen.measurableSet
  have hpoint : ∀ᵐ x ∂(volumeMeasureOn U),
      |cross x| ≤ A x / 2 + remainder x := by
    filter_upwards [habounds] with x hx
    have hyoung := truncationCrossTerm_young
      (lam := 1) (Lam := 2) (a := a x) (eta := eta x)
      (value := v.toFun x) (by norm_num) hx.1 hx.2
      (u.grad x) (euclideanGradient eta x)
    have hcrossEq : cross x =
        a x * v.toFun x * vecDot (u.grad x)
          ((2 * eta x) • euclideanGradient eta x) := by
      dsimp [cross, G]
      rw [vecDot_smul_right, vecDot_smul_right]
      ring
    rw [hcrossEq]
    have hmain : eta x ^ 2 * vecNormSq (u.grad x) / 2 ≤ A x / 2 := by
      dsimp [A]
      have hnn := mul_nonneg (sq_nonneg (eta x)) (vecNormSq_nonneg (u.grad x))
      nlinarith
    have hrem : 2 * 2 ^ 2 / 1 * v.toFun x ^ 2 *
        vecNormSq (euclideanGradient eta x) = remainder x := by
      dsimp [remainder]
      ring
    exact hyoung.trans (add_le_add (by simpa using hmain) hrem.le)
  have hidentity : ∫ x in U, A x ∂volume = -∫ x in U, cross x ∂volume := by
    have hphis : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ eta x ^ 2) := by
      simpa only [pow_two] using heta.mul heta
    have hphic : HasCompactSupport (fun x ↦ eta x ^ 2) := by
      simpa only [pow_two] using hetac.mul_right
    have hphisub : tsupport (fun x ↦ eta x ^ 2) ⊆ U := by
      simpa only [pow_two] using
        (tsupport_mul_subset_left (f := eta) (g := eta)).trans hetasub
    let psi : H10Function U :=
      v.mulContDiffHasCompactSupportToH10 hU hphis hphic hphisub
    have hpsiGrad :=
      WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
        v hU hphis hphic hphisub
    have hweak := hu psi
    have hrewrite : (∫ x in U, vecDot (a x • u.grad x)
          (psi.toH1Function.grad x) ∂volume) =
        ∫ x in U, (A x + cross x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hpsiGrad] with x hgrad
      rw [hgrad]
      simp_rw [fderiv_cutoff_sq_apply eta heta]
      dsimp [A, cross, G]
      rw [hvgrad]
      simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, euclideanGradient,
        euclideanCoordDeriv]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [hrewrite, integral_add hA hcross] at hweak
    linarith
  have habsorb := integral_le_two_mul_integral_of_eq_neg_of_abs_le
    hA hcross hremainder hidentity hpoint
  dsimp [A, remainder] at habsorb ⊢
  rw [hvfun] at habsorb
  have hremInt :
      (∫ x in U, 8 * (u.toFun x - c) ^ 2 *
        vecNormSq (euclideanGradient eta x) ∂volume) =
      8 * ∫ x in U, (u.toFun x - c) ^ 2 *
        vecNormSq (euclideanGradient eta x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hremInt] at habsorb
  convert habsorb using 1
  all_goals ring

private theorem isOpenBoundedConvexDomain_euclideanBall
    (z : Vec d) {R : ℝ} (hR : 0 < R) :
    IsOpenBoundedConvexDomain (euclideanBall z R) := by
  refine ⟨isOpen_euclideanBall z R, ?_, convex_euclideanBall z R⟩
  exact Bornology.IsBounded.isBoundedDomain
    (Metric.isBounded_ball.subset (euclideanBall_subset_metricBall hR))

/-- Euclidean-ball specialization with the canonical quantitative cutoff.
The inner radius is where the cutoff equals one; its support stays strictly
inside the outer open ball. -/
theorem scalarCaccioppoli_euclideanBall_of_one_le_of_le_two
    {z : Vec d} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {a : Vec d → ℝ}
    (hameas : AEStronglyMeasurable a
      (volumeMeasureOn (euclideanBall z R)))
    (habounds : ∀ᵐ x ∂(volumeMeasureOn (euclideanBall z R)),
      1 ≤ a x ∧ a x ≤ 2)
    (u : H1Function (euclideanBall z R))
    (hu : IsWeaklyHarmonicOn a (euclideanBall z R) u) (c : ℝ) :
    let eta := QuantitativeBallCutoff.canonical z r R hr hrR
    ∫ x in euclideanBall z R,
        a x * eta x ^ 2 * vecNormSq (u.grad x) ∂volume ≤
      16 * ∫ x in euclideanBall z R, (u.toFun x - c) ^ 2 *
        vecNormSq (euclideanGradient eta x) ∂volume := by
  let eta := QuantitativeBallCutoff.canonical z r R hr hrR
  exact scalarCaccioppoli_cutoff_of_one_le_of_le_two
    (isOpenBoundedConvexDomain_euclideanBall z (hr.trans hrR))
    hameas habounds u hu c eta.smooth eta.hasCompactSupport
    eta.support_subset (fun x ↦ ⟨eta.nonneg x, eta.le_one x⟩)

/-- Read the cutoff estimate as an unweighted energy estimate on the inner
ball.  This is the form consumed by the small-contrast rescaling. -/
theorem scalarCaccioppoli_innerBall_of_one_le_of_le_two
    {z : Vec d} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {a : Vec d → ℝ}
    (hameas : AEStronglyMeasurable a
      (volumeMeasureOn (euclideanBall z R)))
    (habounds : ∀ᵐ x ∂(volumeMeasureOn (euclideanBall z R)),
      1 ≤ a x ∧ a x ≤ 2)
    (u : H1Function (euclideanBall z R))
    (hu : IsWeaklyHarmonicOn a (euclideanBall z R) u) (c : ℝ) :
    let eta := QuantitativeBallCutoff.canonical z r R hr hrR
    ∫ x in euclideanBall z r, vecNormSq (u.grad x) ∂volume ≤
      16 * ∫ x in euclideanBall z R, (u.toFun x - c) ^ 2 *
        vecNormSq (euclideanGradient eta x) ∂volume := by
  let eta := QuantitativeBallCutoff.canonical z r R hr hrR
  let A : Vec d → ℝ := fun x ↦
    a x * eta x ^ 2 * vecNormSq (u.grad x)
  have hsub : euclideanBall z r ⊆ euclideanBall z R :=
    euclideanBall_subset_euclideanBall hr.le hrR
  have hgrad : IntegrableOn (fun x ↦ vecNormSq (u.grad x))
      (euclideanBall z R) := integrableOn_vecNormSq_h1Grad u
  have hA : IntegrableOn A (euclideanBall z R) := by
    refine (hgrad.const_mul 2).mono' ?_ ?_
    · simpa [A, Pi.mul_apply, mul_assoc] using hameas.mul
        ((eta.smooth.continuous.aestronglyMeasurable.pow 2).mul
          hgrad.aestronglyMeasurable)
    · filter_upwards [habounds] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
          (vecNormSq_nonneg _))]
      have hetaSq : eta x ^ 2 ≤ 1 := by
        nlinarith [eta.nonneg x, eta.le_one x]
      have hcoeff : a x * eta x ^ 2 ≤ 2 := by
        calc
          a x * eta x ^ 2 ≤ a x * 1 :=
            mul_le_mul_of_nonneg_left hetaSq (by linarith)
          _ ≤ 2 := by simpa using hx.2
      exact mul_le_mul_of_nonneg_right hcoeff (vecNormSq_nonneg _)
  have hboundsInner : ∀ᵐ x ∂(volumeMeasureOn (euclideanBall z r)),
      1 ≤ a x ∧ a x ≤ 2 :=
    habounds.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hlower : ∫ x in euclideanBall z r, vecNormSq (u.grad x) ∂volume ≤
      ∫ x in euclideanBall z r, A x ∂volume := by
    apply integral_mono_ae
    · exact hgrad.mono_set hsub
    · exact hA.mono_set hsub
    · filter_upwards [hboundsInner,
        ae_restrict_mem (isOpen_euclideanBall z r).measurableSet] with x hx hxball
      dsimp [A]
      rw [eta.eq_one_on_inner x hxball]
      simp only [one_pow, mul_one]
      simpa using mul_le_mul_of_nonneg_right hx.1 (vecNormSq_nonneg (u.grad x))
  have hmono : ∫ x in euclideanBall z r, A x ∂volume ≤
      ∫ x in euclideanBall z R, A x ∂volume := by
    apply setIntegral_mono_set hA
    · filter_upwards [habounds] with x hx
      exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
        (vecNormSq_nonneg _)
    · exact Filter.Eventually.of_forall hsub
  exact hlower.trans (hmono.trans
    (scalarCaccioppoli_euclideanBall_of_one_le_of_le_two
      hr hrR hameas habounds u hu c))

/-- Fully numerical ball Caccioppoli estimate.  All coefficient dependence has
disappeared after the normalization `1 ≤ a ≤ 2`. -/
theorem scalarCaccioppoli_innerBall_le_explicit
    {z : Vec d} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {a : Vec d → ℝ}
    (hameas : AEStronglyMeasurable a
      (volumeMeasureOn (euclideanBall z R)))
    (habounds : ∀ᵐ x ∂(volumeMeasureOn (euclideanBall z R)),
      1 ≤ a x ∧ a x ≤ 2)
    (u : H1Function (euclideanBall z R))
    (hu : IsWeaklyHarmonicOn a (euclideanBall z R) u) (c : ℝ) :
    ∫ x in euclideanBall z r, vecNormSq (u.grad x) ∂volume ≤
      (16 * (d : ℝ) *
        (quantitativeBallCutoffGradientConst d / (R - r)) ^ 2) *
      ∫ x in euclideanBall z R, (u.toFun x - c) ^ 2 ∂volume := by
  let eta := QuantitativeBallCutoff.canonical z r R hr hrR
  let K := quantitativeBallCutoffGradientConst d / (R - r)
  have hbase := scalarCaccioppoli_innerBall_of_one_le_of_le_two
    hr hrR hameas habounds u hu c
  dsimp only at hbase
  have hK : 0 ≤ K := by
    exact (norm_nonneg (fderiv ℝ eta.toFun (0 : Vec d))).trans
      (eta.gradient_bound 0)
  have hvSq : IntegrableOn (fun x ↦ (u.toFun x - c) ^ 2)
      (euclideanBall z R) := by
    let hDomain := isOpenBoundedConvexDomain_euclideanBall z (hr.trans hrR)
    let v : H1Function (euclideanBall z R) := u - constantH1 hDomain c
    simpa [v, (sub_constantH1_data hDomain u c).1] using
      v.memL2.integrable_sq
  have hfactorCont : Continuous (fun x ↦
      vecNormSq (euclideanGradient eta x)) :=
    continuous_vecNormSq_euclideanGradient_of_contDiff eta.smooth
  have hfactorCompact : HasCompactSupport (fun x ↦
      vecNormSq (euclideanGradient eta x)) :=
    hasCompactSupport_vecNormSq_euclideanGradient eta.hasCompactSupport
  have hproduct : IntegrableOn (fun x ↦ (u.toFun x - c) ^ 2 *
      vecNormSq (euclideanGradient eta x)) (euclideanBall z R) := by
    exact WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      hfactorCont hfactorCompact hvSq |>.congr_fun
        (fun x _hx ↦ by ring) (isOpen_euclideanBall z R).measurableSet
  have hupper : ∫ x in euclideanBall z R, (u.toFun x - c) ^ 2 *
        vecNormSq (euclideanGradient eta x) ∂volume ≤
      ((d : ℝ) * K ^ 2) *
        ∫ x in euclideanBall z R, (u.toFun x - c) ^ 2 ∂volume := by
    rw [← integral_const_mul]
    apply integral_mono_ae hproduct
    · exact hvSq.const_mul ((d : ℝ) * K ^ 2)
    · filter_upwards with x
      have hgradBase :=
        WeakPoissonEquationOn.vecNormSq_euclideanGradient_le_card_mul_fderiv_norm_sq
          eta x
      have hgradNorm := eta.gradient_bound x
      have hsq : ‖fderiv ℝ eta.toFun x‖ ^ 2 ≤ K ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hgradNorm 2
      have hgrad : vecNormSq (euclideanGradient eta x) ≤
          (d : ℝ) * K ^ 2 :=
        hgradBase.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d))
      calc
        (u.toFun x - c) ^ 2 * vecNormSq (euclideanGradient eta x) ≤
            (u.toFun x - c) ^ 2 * ((d : ℝ) * K ^ 2) :=
          mul_le_mul_of_nonneg_left hgrad (sq_nonneg _)
        _ = (d : ℝ) * K ^ 2 * (u.toFun x - c) ^ 2 := by ring
  calc
    ∫ x in euclideanBall z r, vecNormSq (u.grad x) ∂volume ≤
        16 * ∫ x in euclideanBall z R, (u.toFun x - c) ^ 2 *
          vecNormSq (euclideanGradient eta x) ∂volume := hbase
    _ ≤ 16 * (((d : ℝ) * K ^ 2) *
          ∫ x in euclideanBall z R, (u.toFun x - c) ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left hupper (by norm_num)
    _ = (16 * (d : ℝ) *
          (quantitativeBallCutoffGradientConst d / (R - r)) ^ 2) *
        ∫ x in euclideanBall z R, (u.toFun x - c) ^ 2 ∂volume := by
      simp only [K]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
