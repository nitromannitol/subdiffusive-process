import SubdiffusiveProcess.MeyersRegularity.Basic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.BallCaccioppoli
import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-! Interior Meyers regularity: Caccioppoli. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

private theorem unitBall_eq_euclideanBall (d : ℕ) (r : ℝ) :
    unitBall d r = euclideanBall (0 : Vec d) r := by
  ext x
  simp only [unitBall, Meyers.eBall, euclideanBall, euclideanSqDist, vecNormSq,
    vecDot, Pi.sub_apply, pow_two, Set.mem_setOf_eq]

private theorem unitBall_domain (d : ℕ) {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (unitBall d r) := by
  rw [unitBall_eq_euclideanBall]
  refine ⟨isOpen_euclideanBall _ _, ?_, convex_euclideanBall _ _⟩
  exact Bornology.IsBounded.isBoundedDomain
    (Metric.isBounded_ball.subset (euclideanBall_subset_metricBall hr))

theorem aux_dedup_d148_scalarEquation_restrict {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (a h : Vec d → ℝ) (u : H1Function U) (heq : ScalarEquation a h u) :
    ScalarEquation a h (u.restrict hV hVU) := by
  intro phi
  let psi := phi.extendByZeroToOpenSuperset hV.measurableSet hU hVU
  have hleft : (fun x => a x * vecDot (u.grad x) (psi.toH1Function.grad x)) =
      V.indicator (fun x => a x * vecDot (u.grad x) (phi.toH1Function.grad x)) := by
    funext x
    by_cases hx : x ∈ V
    · simp only [psi, H10Function.extendByZeroToOpenSuperset_grad,
        H10Function.zeroExtensionGrad_apply_of_mem _ hx, Set.indicator_of_mem hx]
    · simp only [psi, H10Function.extendByZeroToOpenSuperset_grad,
        H10Function.zeroExtensionGrad_apply_of_not_mem _ hx, Set.indicator_of_notMem hx,
        vecDot_zero_right, mul_zero]
  have hright : (fun x => h x * psi.toH1Function.toFun x) =
      V.indicator (fun x => h x * phi.toH1Function.toFun x) := by
    funext x
    by_cases hx : x ∈ V
    · simp only [psi, H10Function.extendByZeroToOpenSuperset_toFun,
        H10Function.zeroExtension_apply_of_mem _ hx, Set.indicator_of_mem hx]
    · simp only [psi, H10Function.extendByZeroToOpenSuperset_toFun,
        H10Function.zeroExtension_apply_of_not_mem _ hx, Set.indicator_of_notMem hx,
        mul_zero]
  have he := heq psi
  rw [hleft, hright, integral_indicator hV.measurableSet,
    integral_indicator hV.measurableSet, Measure.restrict_restrict_of_subset hVU] at he
  exact he

private theorem scalarEquation_restrict {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (a h : Vec d → ℝ) (u : H1Function U) (heq : ScalarEquation a h u) :
    ScalarEquation a h (u.restrict hV hVU) := by exact SubdiffusiveProcess.MeyersRegularity.aux_dedup_d148_scalarEquation_restrict (d := d) (U := U) (V := V) (hU := hU) (hV := hV) (hVU := hVU) (a := a) (h := h) (u := u) (heq := heq)

private theorem caccioppoli_cutoff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {a h : Vec d → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict U))
    (hab : ∀ᵐ x ∂volume.restrict U, 1/2 ≤ a x ∧ a x ≤ 3/2)
    (hh : MemLp h 2 (volume.restrict U)) (u : H1Function U)
    (heq : ScalarEquation a h u) {eta : Vec d → ℝ}
    (hs : ContDiff ℝ (⊤ : ℕ∞) eta) (hc : HasCompactSupport eta)
    (hsub : tsupport eta ⊆ U) (hrange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    (∫ x in U, a x * eta x ^ 2 * vecNormSq (u.grad x)) ≤
      (∫ x in U, h x ^ 2) + (∫ x in U, u.toFun x ^ 2) +
        18 * ∫ x in U, u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x) := by
  let A : Vec d → ℝ := fun x => a x * eta x ^ 2 * vecNormSq (u.grad x)
  let G : Vec d → Vec d := fun x => u.toFun x • ((2 * eta x) • euclideanGradient eta x)
  let cross : Vec d → ℝ := fun x => a x * vecDot (u.grad x) (G x)
  let remainder : Vec d → ℝ := fun x => 9 * u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)
  have hgradSq : IntegrableOn (fun x => vecNormSq (u.grad x)) U :=
    integrableOn_vecNormSq_h1Grad u
  have hA : IntegrableOn A U := by
    refine (hgradSq.const_mul (3/2)).mono' ?_ ?_
    · simpa [A, Pi.mul_apply, mul_assoc] using ha.mul
        ((hs.continuous.aestronglyMeasurable.pow 2).mul hgradSq.aestronglyMeasurable)
    · filter_upwards [hab] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (vecNormSq_nonneg _))]
      have hetaSq : eta x ^ 2 ≤ 1 := by nlinarith [(hrange x).1, (hrange x).2]
      have hcoeff : a x * eta x ^ 2 ≤ 3/2 := by
        calc
          a x * eta x ^ 2 ≤ a x * 1 := mul_le_mul_of_nonneg_left hetaSq (by linarith)
          _ ≤ 3/2 := by simpa using hx.2
      exact mul_le_mul_of_nonneg_right hcoeff (vecNormSq_nonneg _)
  have hG : MemVectorL2 U G := by
    apply MemLp.of_eval
    intro i
    have hcont : Continuous (fun x => 2 * eta x * euclideanGradient eta x i) :=
      (continuous_const.mul hs.continuous).mul (contDiff_euclideanCoordDeriv hs i).continuous
    have hcompact : HasCompactSupport (fun x => 2 * eta x * euclideanGradient eta x i) := by
      simpa only [Pi.mul_apply] using ((hc.mul_left (f := fun _ => (2 : ℝ))).mul_right
        (f' := fun x => euclideanGradient eta x i))
    have ht : MemLp (fun x => 2 * eta x * euclideanGradient eta x i) ⊤ (volume.restrict U) :=
      hcont.memLp_top_of_hasCompactSupport hcompact _
    simpa only [G, Pi.smul_apply, smul_eq_mul, mul_comm] using u.memL2.mul' ht
  have hdot : IntegrableOn (fun x => vecDot (u.grad x) (G x)) U :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hG
  have hcross : IntegrableOn cross U := by
    refine (hdot.abs.const_mul (3/2)).mono' ?_ ?_
    · simpa [cross, Pi.mul_apply] using ha.mul hdot.aestronglyMeasurable
    · filter_upwards [hab] with x hx
      change |a x * vecDot (u.grad x) (G x)| ≤ 3/2 * |vecDot (u.grad x) (G x)|
      rw [abs_mul]
      have hax : |a x| ≤ 3/2 := by rw [abs_of_nonneg (by linarith)]; exact hx.2
      exact mul_le_mul_of_nonneg_right hax (abs_nonneg _)
  have huSq : IntegrableOn (fun x => u.toFun x ^ 2) U := u.memL2.integrable_sq
  have hrem0 : IntegrableOn (fun x => u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) U := by
    have hm := WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (continuous_vecNormSq_euclideanGradient_of_contDiff hs)
      (hasCompactSupport_vecNormSq_euclideanGradient hc) huSq
    exact hm.congr_fun (fun x _ => mul_comm _ _) hU.isOpen.measurableSet
  have hrem : IntegrableOn remainder U := by
    simpa only [remainder, mul_assoc] using hrem0.const_mul 9
  have hpoint : (fun x => -cross x) ≤ᵐ[volume.restrict U] fun x => A x / 2 + remainder x := by
    filter_upwards [hab] with x hx
    have hy := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.truncationCrossTerm_young
      (lam := 1/2) (Lam := 3/2) (a := a x) (eta := eta x) (value := u.toFun x)
      (by norm_num) hx.1 hx.2 (u.grad x) (euclideanGradient eta x)
    have hcEq : cross x = a x * u.toFun x * vecDot (u.grad x) ((2 * eta x) • euclideanGradient eta x) := by
      dsimp [cross, G]
      rw [vecDot_smul_right]
      ring
    have hmain : (1/2 : ℝ) * eta x ^ 2 * vecNormSq (u.grad x) / 2 ≤ A x / 2 := by
      dsimp [A]
      have hn := mul_nonneg (sq_nonneg (eta x)) (vecNormSq_nonneg (u.grad x))
      nlinarith
    exact (neg_le_abs _).trans (by rw [hcEq]; exact hy.trans (by dsimp [remainder]; nlinarith [hmain]))
  have hphis : ContDiff ℝ (⊤ : ℕ∞) (fun x => eta x ^ 2) := hs.pow 2
  have hphic : HasCompactSupport (fun x => eta x ^ 2) := by simpa only [pow_two] using hc.mul_right
  have hphisub : tsupport (fun x => eta x ^ 2) ⊆ U := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := eta) (g := eta)).trans hsub
  let psi := u.mulContDiffHasCompactSupportToH10 hU hphis hphic hphisub
  have hpsiFun : psi.toH1Function.toFun = fun x => eta x ^ 2 * u.toFun x :=
    u.mulContDiffHasCompactSupportToH10_toFun hU hphis hphic hphisub
  have hpsiGrad := WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
    u hU hphis hphic hphisub
  have hidentity : (∫ x in U, A x + cross x) = -∫ x in U, h x * psi.toH1Function.toFun x := by
    rw [← heq psi]
    apply integral_congr_ae
    filter_upwards [hpsiGrad] with x hx
    rw [hx]
    simp_rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.fderiv_cutoff_sq_apply eta hs]
    dsimp [A, cross, G]
    simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      euclideanGradient, euclideanCoordDeriv]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have habsorb := WeakPoissonEquationOn.integral_half_main_le_scalar_rhs_add_error_of_add_energy_identity
    hidentity hpoint hA hcross hrem
  have hforce := WeakPoissonEquationOn.neg_integral_mul_le_half_integral_sq_add_half_integral_sq_of_memScalarL2
    hh psi.toH1Function.memL2
  have hpsiSq : (∫ x in U, psi.toH1Function.toFun x ^ 2) ≤ ∫ x in U, u.toFun x ^ 2 := by
    apply integral_mono_ae psi.toH1Function.memL2.integrable_sq huSq
    filter_upwards with x
    rw [hpsiFun]
    have he2 : eta x ^ 2 ≤ 1 := by nlinarith [(hrange x).1, (hrange x).2]
    have he : (eta x ^ 2) ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (sq_nonneg (eta x)) he2 2
    simpa only [mul_pow, one_mul] using mul_le_mul_of_nonneg_right he (sq_nonneg (u.toFun x))
  have hremEq : (∫ x in U, remainder x) = 9 * ∫ x in U, u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x) := by
    simp only [remainder, mul_assoc, integral_const_mul]
  dsimp only [A] at habsorb
  rw [hremEq] at habsorb
  linarith

private theorem l2_sq_eq_integral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ENNReal.toReal_ofReal (by positivity :
    0 ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹)]
  rw [show (2 : ℝ)⁻¹ = 1/2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

theorem exists_caccioppoli_value_estimate (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ a h : Vec d → ℝ,
      AEMeasurable a (volume.restrict (unitBall d 3)) →
      (∀ᵐ x ∂volume.restrict (unitBall d 3), |a x-1| ≤ 1/2) →
      MemLp h 2 (volume.restrict (unitBall d 2)) →
      ∀ u : H1Function (unitBall d 3), ScalarEquation a h u →
        (eLpNorm (gradientField u) 2 (volume.restrict (unitBall d (3/2)))).toReal ≤
          C * ((eLpNorm u.toFun 2 (volume.restrict (unitBall d 2))).toReal +
            (eLpNorm h 2 (volume.restrict (unitBall d 2))).toReal) := by
  let K : ℝ := quantitativeBallCutoffGradientConst d / (2 - 3/2)
  let D : ℝ := (d : ℝ) * K ^ 2
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  refine ⟨4 + 36 * D, by positivity, ?_⟩
  intro a h ha hclose hh u heq
  have h23 : unitBall d 2 ⊆ unitBall d 3 := Meyers.eBall_mono _ (by norm_num) (by norm_num)
  have h12 : unitBall d (3/2) ⊆ unitBall d 2 := Meyers.eBall_mono _ (by norm_num) (by norm_num)
  let v := u.restrict (Meyers.isOpen_eBall _ _) h23
  have hab : ∀ᵐ x ∂volume.restrict (unitBall d 2), 1/2 ≤ a x ∧ a x ≤ 3/2 := by
    filter_upwards [hclose.filter_mono (ae_mono (Measure.restrict_mono h23 le_rfl))] with x hx
    have hb := abs_le.mp hx
    constructor <;> linarith
  have ha2 : AEStronglyMeasurable a (volume.restrict (unitBall d 2)) :=
    (ha.mono_measure (Measure.restrict_mono h23 le_rfl)).aestronglyMeasurable
  have heq2 : ScalarEquation a h v := scalarEquation_restrict
    (Meyers.isOpen_eBall _ _) (Meyers.isOpen_eBall _ _) h23 a h u heq
  let eta := QuantitativeBallCutoff.canonical (0 : Vec d) (3/2) 2 (by norm_num) (by norm_num)
  have hsup : tsupport eta.toFun ⊆ unitBall d 2 := by
    rw [unitBall_eq_euclideanBall]; exact eta.support_subset
  have hbase := caccioppoli_cutoff (unitBall_domain d (by norm_num : (0 : ℝ) < 2))
    ha2 hab hh v heq2 eta.smooth eta.hasCompactSupport hsup
    (fun x => ⟨eta.nonneg x, eta.le_one x⟩)
  let A : Vec d → ℝ := fun x => a x * eta x ^ 2 * vecNormSq (u.grad x)
  have hgradSq : IntegrableOn (fun x => vecNormSq (u.grad x)) (unitBall d 2) :=
    integrableOn_vecNormSq_h1Grad v
  have hA : IntegrableOn A (unitBall d 2) := by
    refine (hgradSq.const_mul (3/2)).mono' ?_ ?_
    · simpa [A, Pi.mul_apply, mul_assoc] using ha2.mul
        ((eta.smooth.continuous.aestronglyMeasurable.pow 2).mul hgradSq.aestronglyMeasurable)
    · filter_upwards [hab] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (vecNormSq_nonneg _))]
      have hetaSq : eta x ^ 2 ≤ 1 := by nlinarith [eta.nonneg x, eta.le_one x]
      have hcoeff : a x * eta x ^ 2 ≤ 3/2 := by
        calc
          a x * eta x ^ 2 ≤ a x * 1 := mul_le_mul_of_nonneg_left hetaSq (by linarith)
          _ ≤ 3/2 := by simpa using hx.2
      exact mul_le_mul_of_nonneg_right hcoeff (vecNormSq_nonneg _)
  have hlower : (1/2 : ℝ) * (∫ x in unitBall d (3/2), vecNormSq (u.grad x)) ≤
      ∫ x in unitBall d 2, A x := by
    calc
      _ = ∫ x in unitBall d (3/2), (1/2 : ℝ) * vecNormSq (u.grad x) := (integral_const_mul _ _).symm
      _ ≤ ∫ x in unitBall d (3/2), A x := by
        apply integral_mono_ae ((hgradSq.mono_set h12).const_mul _) (hA.mono_set h12)
        filter_upwards [hab.filter_mono (ae_mono (Measure.restrict_mono h12 le_rfl)),
          ae_restrict_mem (Meyers.measurableSet_eBall _ _)] with x hx hxball
        dsimp only [A]
        rw [eta.eq_one_on_inner x (by rw [← unitBall_eq_euclideanBall]; exact hxball)]
        simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_right hx.1 (vecNormSq_nonneg _)
      _ ≤ ∫ x in unitBall d 2, A x := by
        apply setIntegral_mono_set hA
        · filter_upwards [hab] with x hx
          exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (vecNormSq_nonneg _)
        · exact Filter.Eventually.of_forall h12
  have huSq : IntegrableOn (fun x => u.toFun x ^ 2) (unitBall d 2) := v.memL2.integrable_sq
  have hproduct : IntegrableOn (fun x => u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) (unitBall d 2) := by
    exact (WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (continuous_vecNormSq_euclideanGradient_of_contDiff eta.smooth)
      (hasCompactSupport_vecNormSq_euclideanGradient eta.hasCompactSupport) huSq).congr_fun
        (fun x _ => mul_comm _ _) (Meyers.measurableSet_eBall _ _)
  have hupper : (∫ x in unitBall d 2, u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) ≤
      D * ∫ x in unitBall d 2, u.toFun x ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae hproduct (huSq.const_mul D)
    filter_upwards with x
    have hnorm := WeakPoissonEquationOn.vecNormSq_euclideanGradient_le_card_mul_fderiv_norm_sq eta x
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (eta.gradient_bound x) 2
    have hgrad : vecNormSq (euclideanGradient eta x) ≤ D :=
      hnorm.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d))
    calc
      _ ≤ u.toFun x ^ 2 * D := mul_le_mul_of_nonneg_left hgrad (sq_nonneg _)
      _ = D * u.toFun x ^ 2 := mul_comm _ _
  have henergy : (∫ x in unitBall d (3/2), vecNormSq (u.grad x)) ≤
      (2 + 36 * D) * (∫ x in unitBall d 2, u.toFun x ^ 2) + 2 * ∫ x in unitBall d 2, h x ^ 2 := by
    change (∫ x in unitBall d 2, A x) ≤
      (∫ x in unitBall d 2, h x ^ 2) + (∫ x in unitBall d 2, u.toFun x ^ 2) +
        18 * (∫ x in unitBall d 2, u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) at hbase
    linarith
  have hgmem := (gradientField_memLp_two u).mono_measure
    (Measure.restrict_mono (h12.trans h23) le_rfl)
  have hgsq : (eLpNorm (gradientField u) 2 (volume.restrict (unitBall d (3/2)))).toReal ^ 2 =
      ∫ x in unitBall d (3/2), vecNormSq (u.grad x) := by
    rw [l2_sq_eq_integral hgmem]
    apply integral_congr_ae
    filter_upwards with x
    rw [norm_gradientField]
    simpa only [vecNormSq, vecDot, pow_two] using
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (u.grad x i)))
  have husq : (eLpNorm u.toFun 2 (volume.restrict (unitBall d 2))).toReal ^ 2 =
      ∫ x in unitBall d 2, u.toFun x ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using l2_sq_eq_integral v.memL2
  have hhsq : (eLpNorm h 2 (volume.restrict (unitBall d 2))).toReal ^ 2 =
      ∫ x in unitBall d 2, h x ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using l2_sq_eq_integral hh
  rw [← hgsq, ← husq, ← hhsq] at henergy
  set G := (eLpNorm (gradientField u) 2 (volume.restrict (unitBall d (3/2)))).toReal
  set V := (eLpNorm u.toFun 2 (volume.restrict (unitBall d 2))).toReal
  set H := (eLpNorm h 2 (volume.restrict (unitBall d 2))).toReal
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hVH : V ^ 2 + H ^ 2 ≤ (V + H) ^ 2 := by nlinarith
  have hcoef : (2 + 36 * D) * V ^ 2 + 2 * H ^ 2 ≤ (4 + 36 * D) ^ 2 * (V + H) ^ 2 := by
    have h1 : (2 + 36 * D) ≤ (4 + 36 * D) ^ 2 := by nlinarith
    have h2 : (2 : ℝ) ≤ (4 + 36 * D) ^ 2 := by nlinarith
    have hsum := add_le_add (mul_le_mul_of_nonneg_right h1 (sq_nonneg V))
      (mul_le_mul_of_nonneg_right h2 (sq_nonneg H))
    exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_left hVH (sq_nonneg (4 + 36 * D))])
  have hbound := henergy.trans hcoef
  have hnonneg : 0 ≤ (4 + 36 * D) * (V + H) := by positivity
  nlinarith


end SubdiffusiveProcess.MeyersRegularity
