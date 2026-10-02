import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceEstimatesCaccioppoli
import SubdiffusiveProcess.Frozen.Section8.WholeSpaceDivergenceResolventSolution
import SubdiffusiveProcess.Assumptions.Cutoff
import Homogenization.Sobolev.Foundations.Cutoff.Ball
import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8

noncomputable section

variable {d : ℕ}

/-- Coordinate bound for the squared gradient of a function whose differential
has operator norm at most `B`. -/
private theorem vecNormSq_coordGradient_le {chi : Vec d → ℝ} {B : ℝ}
    (h : ∀ x, ‖fderiv ℝ chi x‖ ≤ B) (x : Vec d) :
    vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ (d : ℝ) * B ^ 2 := by
  have hcomp : ∀ i : Fin d, ((fderiv ℝ chi x) (basisVec i)) ^ 2 ≤ B ^ 2 := by
    intro i
    have h1 : ‖(fderiv ℝ chi x) (basisVec i)‖ ≤ B := by
      calc ‖(fderiv ℝ chi x) (basisVec i)‖
          ≤ ‖fderiv ℝ chi x‖ * ‖basisVec i‖ := (fderiv ℝ chi x).le_opNorm _
        _ = ‖fderiv ℝ chi x‖ := by simp
        _ ≤ B := h x
    have h0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) h1
    have := abs_le_of_sq_le_sq (a := (fderiv ℝ chi x) (basisVec i)) (b := B)
    nlinarith [abs_nonneg ((fderiv ℝ chi x) (basisVec i)),
      sq_abs ((fderiv ℝ chi x) (basisVec i)),
      (Real.norm_eq_abs ((fderiv ℝ chi x) (basisVec i))) ▸ h1]
  calc vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i))
      = ∑ i : Fin d, ((fderiv ℝ chi x) (basisVec i)) ^ 2 := by
        simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ _i : Fin d, B ^ 2 := Finset.sum_le_sum fun i _ ↦ hcomp i
    _ = (d : ℝ) * B ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The dimensional constant of the ball-cutoff energy inequality. -/
def wholeSpaceCutoffConstant (d : ℕ) : ℝ :=
  8 * (d : ℝ) ^ 3 * smoothTransitionProfile.quantitativeProfile.derivBound ^ 2

/-- **Ball form of the cutoff energy inequality.**

A massive weak solution with zero forcing on `B_{3n}(x0)` has
`L²` mass on the Euclidean ball of radius `n` controlled by `n⁻²` times the
coefficient-weighted mass on `B_{3n}(x0)`. -/
theorem massive_ball_sq_le_of_zero_forcing
    {a : Vec d → ℝ} {mu lam Lam : ℝ} {x0 : Vec d} {n : ℝ} (hn : 0 < n) (hmu : 0 ≤ mu)
    (hEll : IsEllipticFieldOn lam Lam (Metric.ball x0 (3 * n)) (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x)
    (haLe : ∀ x ∈ Metric.ball x0 (3 * n), a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict (Metric.ball x0 (3 * n))))
    (w : H1Function (Metric.ball x0 (3 * n)))
    (hw : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu (Metric.ball x0 (3 * n)) w
      (fun _ ↦ (0 : ℝ))) :
    mu * ∫ x in euclideanBall x0 n, w.toFun x ^ 2 ∂volume ≤
      wholeSpaceCutoffConstant d * (n ^ 2)⁻¹ *
        ∫ x in Metric.ball x0 (3 * n), a x * w.toFun x ^ 2 ∂volume := by
  classical
  have hWdom : IsOpenBoundedConvexDomain (Metric.ball x0 (3 * n)) :=
    isOpenBoundedConvexDomain_ball x0 (by linarith)
  set theta : QuantitativeTransitionProfile :=
    smoothTransitionProfile.quantitativeProfile with htheta_def
  have hn2 : n < 2 * n := by linarith
  set chi : Vec d → ℝ :=
    QuantitativeTransitionProfile.ballCutoff theta x0 n (2 * n) with hchi_def
  have hchi_smooth : ContDiff ℝ (⊤ : ℕ∞) chi :=
    QuantitativeTransitionProfile.ballCutoff_smooth theta x0 hn hn2
  have hchiC : HasCompactSupport chi :=
    QuantitativeTransitionProfile.ballCutoff_hasCompactSupport theta hn hn2
  have hchiS : tsupport chi ⊆ Metric.ball x0 (3 * n) := by
    refine le_trans
      (QuantitativeTransitionProfile.ballCutoff_tsupport_subset_euclideanClosedBall
        theta hn hn2) ?_
    refine le_trans (euclideanClosedBall_subset_metricClosedBall (by linarith)) ?_
    exact Metric.closedBall_subset_ball (by linarith)
  set B : ℝ := theta.derivBound * (2 * (d : ℝ) / (2 * n - n)) with hB_def
  have hB : ∀ x, ‖fderiv ℝ chi x‖ ≤ B := fun x ↦
    QuantitativeTransitionProfile.norm_fderiv_ballCutoff_le theta hn hn2 x
  have hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ (d : ℝ) * B ^ 2 :=
    fun x ↦ vecNormSq_coordGradient_le hB x
  have hmain := massive_cutoff_sq_le_of_zero_forcing hWdom hEll haNonneg w hw
    hchi_smooth hchiC hchiS hK
  have hw2 : IntegrableOn (fun x ↦ w.toFun x ^ 2) (Metric.ball x0 (3 * n)) volume :=
    w.memL2.integrable_sq
  have hchi01 : ∀ x, 0 ≤ chi x ∧ chi x ≤ 1 := fun x ↦
    ⟨QuantitativeTransitionProfile.ballCutoff_nonneg theta x0 n (2 * n) x,
      QuantitativeTransitionProfile.ballCutoff_le_one theta x0 n (2 * n) x⟩
  have hchi2int : IntegrableOn (fun x ↦ chi x ^ 2 * w.toFun x ^ 2)
      (Metric.ball x0 (3 * n)) volume := by
    refine Integrable.mono' hw2 ?_ ?_
    · exact ((hchi_smooth.continuous.pow 2).aestronglyMeasurable).mul
        (w.memL2.aestronglyMeasurable.pow 2)
    · filter_upwards with x
      have h1 := hchi01 x
      have hsq : chi x ^ 2 ≤ 1 := by nlinarith [h1.1, h1.2]
      have hw0 : (0 : ℝ) ≤ w.toFun x ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
  have hlow : ∫ x in euclideanBall x0 n, w.toFun x ^ 2 ∂volume ≤
      ∫ x in Metric.ball x0 (3 * n), chi x ^ 2 * w.toFun x ^ 2 ∂volume := by
    have hcongr : ∫ x in euclideanBall x0 n, w.toFun x ^ 2 ∂volume =
        ∫ x in euclideanBall x0 n, chi x ^ 2 * w.toFun x ^ 2 ∂volume := by
      refine setIntegral_congr_fun (isOpen_euclideanBall x0 n).measurableSet ?_
      intro x hx
      have h1 : chi x = 1 := by
        rw [hchi_def]
        exact QuantitativeTransitionProfile.ballCutoff_eq_one_of_mem_euclideanBall
          theta hn hn2 hx
      simp [h1]
    rw [hcongr]
    refine setIntegral_mono_set hchi2int ?_ ?_
    · filter_upwards with x
      have h1 := hchi01 x
      positivity
    · refine Filter.Eventually.of_forall ?_
      intro x hx
      exact Metric.ball_subset_ball (by linarith)
        (euclideanBall_subset_metricBall hn hx)
  have haw2 : IntegrableOn (fun x ↦ a x * w.toFun x ^ 2)
      (Metric.ball x0 (3 * n)) volume := by
    refine Integrable.mono' (hw2.const_mul Lam) ?_ ?_
    · exact hameas.mul (w.memL2.aestronglyMeasurable.pow 2)
    · filter_upwards [ae_restrict_mem (measurableSet_ball (x := x0) (ε := 3 * n))]
        with x hx
      have hax := haNonneg x
      have hle := haLe x hx
      have hw0 : (0 : ℝ) ≤ w.toFun x ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
  have hgcont : Continuous (fun x ↦ vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i))) := by
    have hc : ∀ i : Fin d, Continuous (fun x : Vec d ↦ (fderiv ℝ chi x) (basisVec i)) := by
      intro i
      exact ((hchi_smooth.continuous_fderiv
        (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).clm_apply continuous_const)
    simpa [vecNormSq, vecDot] using
      (continuous_finset_sum Finset.univ (fun i (_ : i ∈ Finset.univ) ↦ (hc i).mul (hc i)))
  have hdB : (0 : ℝ) ≤ (d : ℝ) * B ^ 2 := by positivity
  have hptb : ∀ x, a x * w.toFun x ^ 2 *
      vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤
      ((d : ℝ) * B ^ 2) * (a x * w.toFun x ^ 2) := by
    intro x
    have h0 : 0 ≤ a x * w.toFun x ^ 2 := mul_nonneg (haNonneg x) (sq_nonneg _)
    have := hK x
    nlinarith
  have hLHSint : IntegrableOn (fun x ↦ a x * w.toFun x ^ 2 *
      vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (Metric.ball x0 (3 * n)) volume := by
    refine Integrable.mono' (haw2.const_mul ((d : ℝ) * B ^ 2)) ?_ ?_
    · exact (hameas.mul (w.memL2.aestronglyMeasurable.pow 2)).mul
        hgcont.aestronglyMeasurable
    · filter_upwards with x
      have h0 : 0 ≤ a x * w.toFun x ^ 2 := mul_nonneg (haNonneg x) (sq_nonneg _)
      have hg0 : 0 ≤ vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) :=
        vecNormSq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa using hptb x
  have hup : ∫ x in Metric.ball x0 (3 * n), a x * w.toFun x ^ 2 *
        vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume ≤
      ((d : ℝ) * B ^ 2) *
        ∫ x in Metric.ball x0 (3 * n), a x * w.toFun x ^ 2 ∂volume := by
    have := integral_mono hLHSint (haw2.const_mul ((d : ℝ) * B ^ 2)) hptb
    rwa [integral_const_mul] at this
  have hconst : 2 * ((d : ℝ) * B ^ 2) = wholeSpaceCutoffConstant d * (n ^ 2)⁻¹ := by
    rw [hB_def, wholeSpaceCutoffConstant, htheta_def]
    have hne : n ≠ 0 := ne_of_gt hn
    field_simp
    ring
  calc mu * ∫ x in euclideanBall x0 n, w.toFun x ^ 2 ∂volume
      ≤ mu * ∫ x in Metric.ball x0 (3 * n), chi x ^ 2 * w.toFun x ^ 2 ∂volume :=
        mul_le_mul_of_nonneg_left hlow hmu
    _ ≤ 2 * ∫ x in Metric.ball x0 (3 * n), a x * w.toFun x ^ 2 *
          vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume := hmain
    _ ≤ 2 * (((d : ℝ) * B ^ 2) *
          ∫ x in Metric.ball x0 (3 * n), a x * w.toFun x ^ 2 ∂volume) := by
        linarith
    _ = wholeSpaceCutoffConstant d * (n ^ 2)⁻¹ *
          ∫ x in Metric.ball x0 (3 * n), a x * w.toFun x ^ 2 ∂volume := by
        rw [← hconst]; ring

/-- The cutoff energy inequality applied to the difference of two whole-space
divergence resolvent solutions with the same data. -/
theorem integral_sq_euclideanBall_le_of_wholeSpaceSolutions
    {a : Vec d → ℝ} {t : ℝ} {f : Vec d → ℝ} {x0 : Vec d} {n : ℝ}
    (ht : 0 < t) (hn : 0 < n)
    (haNonneg : ∀ x, 0 ≤ a x)
    (hameas : AEStronglyMeasurable a volume)
    (hfL2 : MemLp f 2 volume)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (Metric.ball x0 (3 * n)) (scalarCoeffField a))
    (haLe : ∀ x ∈ Metric.ball x0 (3 * n), a x ≤ Lam)
    (u v : WholeSpaceDivergenceResolventSolution a t f) :
    t⁻¹ * ∫ x in euclideanBall x0 n, (u.toFun x - v.toFun x) ^ 2 ∂volume ≤
      wholeSpaceCutoffConstant d * (n ^ 2)⁻¹ *
        ∫ x in Metric.ball x0 (3 * n), a x * (u.toFun x - v.toFun x) ^ 2 ∂volume := by
  classical
  have hWdom : IsOpenBoundedConvexDomain (Metric.ball x0 (3 * n)) :=
    isOpenBoundedConvexDomain_ball x0 (by linarith)
  obtain ⟨uW, huval, -, husol⟩ := u.locally_weak_solution _ hWdom
  obtain ⟨vW, hvval, -, hvsol⟩ := v.locally_weak_solution _ hWdom
  have hfW : MemL2On (Metric.ball x0 (3 * n)) (fun x ↦ t⁻¹ * f x) :=
    (hfL2.const_mul t⁻¹).restrict _
  have hsub := IsMassiveWeakSolutionOn.sub hEll
    (aestronglyMeasurable_const (b := (1 : ℝ)))
    (Filter.Eventually.of_forall fun _ ↦ (by norm_num : |(1 : ℝ)| ≤ 1))
    hfW hfW husol hvsol
  have hzero : ((fun x ↦ t⁻¹ * f x) - fun x ↦ t⁻¹ * f x) = fun _ : Vec d ↦ (0 : ℝ) := by
    funext x
    simp
  rw [hzero] at hsub
  have hball := massive_ball_sq_le_of_zero_forcing (mu := t⁻¹) hn
    (by positivity) hEll haNonneg haLe (hameas.restrict) (uW - vW) hsub
  have hvalue : ∀ x ∈ Metric.ball x0 (3 * n),
      (uW - vW).toFun x = u.toFun x - v.toFun x := by
    intro x hx
    rw [H1Function.sub_toFun]
    simp [huval x hx, hvval x hx]
  have heq1 : ∫ x in euclideanBall x0 n, (uW - vW).toFun x ^ 2 ∂volume =
      ∫ x in euclideanBall x0 n, (u.toFun x - v.toFun x) ^ 2 ∂volume := by
    refine setIntegral_congr_fun (isOpen_euclideanBall x0 n).measurableSet ?_
    intro x hx
    simp only [hvalue x (Metric.ball_subset_ball (by linarith)
      (euclideanBall_subset_metricBall hn hx))]
  have heq2 : ∫ x in Metric.ball x0 (3 * n), a x * (uW - vW).toFun x ^ 2 ∂volume =
      ∫ x in Metric.ball x0 (3 * n), a x * (u.toFun x - v.toFun x) ^ 2 ∂volume := by
    refine setIntegral_congr_fun measurableSet_ball ?_
    intro x hx
    simp only [hvalue x hx]
  rw [heq1, heq2] at hball
  exact hball

/-- A.e. equality is local: it suffices to have it on the pieces of a countable
cover by measurable sets. -/
private theorem ae_eq_of_ae_eq_restrict_cover {alpha : Type*} {g h : Vec d → alpha}
    {S : ℕ → Set (Vec d)} (hmeas : ∀ m, MeasurableSet (S m))
    (hcover : ∀ x, ∃ m, x ∈ S m)
    (H : ∀ m, g =ᵐ[volume.restrict (S m)] h) :
    g =ᵐ[volume] h := by
  have H' : ∀ m : ℕ, ∀ᵐ x ∂volume, x ∈ S m → g x = h x := fun m ↦
    (ae_restrict_iff' (hmeas m)).mp (H m)
  have hall : ∀ᵐ x ∂volume, ∀ m : ℕ, x ∈ S m → g x = h x :=
    (ae_all_iff (p := fun x m ↦ x ∈ S m → g x = h x)).mpr H'
  filter_upwards [hall] with x hx
  obtain ⟨m, hm⟩ := hcover x
  exact hx m hm



theorem wholeSpaceDivergenceResolventSolution_ae_eq_of_growth
    {a : Vec d → ℝ} {t : ℝ} {f : Vec d → ℝ} {x0 : Vec d}
    (ht : 0 < t)
    (haNonneg : ∀ x, 0 ≤ a x)
    (hameas : AEStronglyMeasurable a volume)
    (hfL2 : MemLp f 2 volume)
    (hloc : ∀ r : ℝ, 0 < r → ∃ lam Lam : ℝ,
      IsEllipticFieldOn lam Lam (Metric.ball x0 r) (scalarCoeffField a) ∧
      ∀ x ∈ Metric.ball x0 r, a x ≤ Lam)
    (u v : WholeSpaceDivergenceResolventSolution a t f)
    (hgrow : Filter.Tendsto
      (fun m : ℕ ↦ (((m : ℝ) + 1) ^ 2)⁻¹ *
        ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
          a x * (u.toFun x - v.toFun x) ^ 2 ∂volume)
      Filter.atTop (nhds 0)) :
    u.toFun =ᵐ[volume] v.toFun ∧ u.grad =ᵐ[volume] v.grad := by
  classical
  have hduv : Integrable (fun x ↦ (u.toFun x - v.toFun x) ^ 2) volume :=
    (u.memL2_toFun.sub v.memL2_toFun).integrable_sq
  have hkey : ∀ m : ℕ,
      t⁻¹ * ∫ x in euclideanBall x0 ((m : ℝ) + 1),
          (u.toFun x - v.toFun x) ^ 2 ∂volume ≤
        wholeSpaceCutoffConstant d * (((m : ℝ) + 1) ^ 2)⁻¹ *
          ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
            a x * (u.toFun x - v.toFun x) ^ 2 ∂volume := by
    intro m
    have hn : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    obtain ⟨lam, Lam, hEll, haLe⟩ := hloc (3 * ((m : ℝ) + 1)) (by linarith)
    exact integral_sq_euclideanBall_le_of_wholeSpaceSolutions ht hn haNonneg hameas
      hfL2 hEll haLe u v
  have hmono : ∀ m0 m : ℕ, m0 ≤ m →
      ∫ x in euclideanBall x0 ((m0 : ℝ) + 1), (u.toFun x - v.toFun x) ^ 2 ∂volume ≤
        ∫ x in euclideanBall x0 ((m : ℝ) + 1), (u.toFun x - v.toFun x) ^ 2 ∂volume := by
    intro m0 m hm
    refine setIntegral_mono_set hduv.integrableOn ?_ ?_
    · filter_upwards with x
      positivity
    · refine Filter.Eventually.of_forall ?_
      intro x hx
      change euclideanSqDist x x0 < ((m0 : ℝ) + 1) ^ 2 at hx
      change euclideanSqDist x x0 < ((m : ℝ) + 1) ^ 2
      have hle : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h0 : (0 : ℝ) ≤ (m0 : ℝ) := Nat.cast_nonneg m0
      nlinarith
  have hzero : ∀ m0 : ℕ,
      ∫ x in euclideanBall x0 ((m0 : ℝ) + 1),
        (u.toFun x - v.toFun x) ^ 2 ∂volume = 0 := by
    intro m0
    have hnonneg : 0 ≤ ∫ x in euclideanBall x0 ((m0 : ℝ) + 1),
        (u.toFun x - v.toFun x) ^ 2 ∂volume :=
      setIntegral_nonneg (isOpen_euclideanBall x0 _).measurableSet fun x _ ↦ sq_nonneg _
    have hlim : Filter.Tendsto
        (fun m : ℕ ↦ wholeSpaceCutoffConstant d * (((m : ℝ) + 1) ^ 2)⁻¹ *
          ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
            a x * (u.toFun x - v.toFun x) ^ 2 ∂volume)
        Filter.atTop (nhds 0) := by
      simpa [mul_assoc] using hgrow.const_mul (wholeSpaceCutoffConstant d)
    have hev : ∀ᶠ m : ℕ in Filter.atTop,
        t⁻¹ * ∫ x in euclideanBall x0 ((m0 : ℝ) + 1),
            (u.toFun x - v.toFun x) ^ 2 ∂volume ≤
          wholeSpaceCutoffConstant d * (((m : ℝ) + 1) ^ 2)⁻¹ *
            ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
              a x * (u.toFun x - v.toFun x) ^ 2 ∂volume := by
      filter_upwards [Filter.eventually_ge_atTop m0] with m hm
      have h1 := hkey m
      have h2 := mul_le_mul_of_nonneg_left (hmono m0 m hm)
        (le_of_lt (inv_pos.mpr ht))
      linarith
    have hle0 := ge_of_tendsto hlim hev
    have htinv : 0 < t⁻¹ := inv_pos.mpr ht
    nlinarith
  have haezero : ∀ m0 : ℕ,
      u.toFun =ᵐ[volume.restrict (euclideanBall x0 ((m0 : ℝ) + 1))] v.toFun := by
    intro m0
    have hint : IntegrableOn (fun x ↦ (u.toFun x - v.toFun x) ^ 2)
        (euclideanBall x0 ((m0 : ℝ) + 1)) volume := hduv.integrableOn
    have hnn : 0 ≤ᵐ[volume.restrict (euclideanBall x0 ((m0 : ℝ) + 1))]
        fun x ↦ (u.toFun x - v.toFun x) ^ 2 :=
      Filter.Eventually.of_forall fun x ↦ sq_nonneg _
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp (hzero m0)
    filter_upwards [hae] with x hx
    have hx0 : (u.toFun x - v.toFun x) ^ 2 = 0 := hx
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx0
    linarith
  have hu_eq : u.toFun =ᵐ[volume] v.toFun := by
    refine ae_eq_of_ae_eq_restrict_cover
      (S := fun m : ℕ ↦ euclideanBall x0 ((m : ℝ) + 1))
      (fun m ↦ (isOpen_euclideanBall x0 _).measurableSet) ?_ haezero
    intro x
    refine ⟨⌈euclideanSqDist x x0⌉₊, ?_⟩
    have hge : euclideanSqDist x x0 ≤ (⌈euclideanSqDist x x0⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hnn : (0 : ℝ) ≤ (⌈euclideanSqDist x x0⌉₊ : ℝ) := Nat.cast_nonneg _
    change euclideanSqDist x x0 < ((⌈euclideanSqDist x x0⌉₊ : ℝ) + 1) ^ 2
    nlinarith
  refine ⟨hu_eq, ?_⟩
  refine ae_eq_of_ae_eq_restrict_cover
    (S := fun m : ℕ ↦ Metric.ball x0 ((m : ℝ) + 1))
    (fun m ↦ measurableSet_ball) ?_ ?_
  · intro x
    refine ⟨⌈dist x x0⌉₊, ?_⟩
    have hge : dist x x0 ≤ (⌈dist x x0⌉₊ : ℝ) := Nat.le_ceil _
    simp only [Metric.mem_ball]
    linarith
  · intro m
    have hWdom : IsOpenBoundedConvexDomain (Metric.ball x0 ((m : ℝ) + 1)) :=
      isOpenBoundedConvexDomain_ball x0 (by positivity)
    obtain ⟨uW, huval, hugrad, -⟩ := u.locally_weak_solution _ hWdom
    obtain ⟨vW, hvval, hvgrad, -⟩ := v.locally_weak_solution _ hWdom
    have hvals : uW.toFun =ᵐ[volume.restrict (Metric.ball x0 ((m : ℝ) + 1))] vW.toFun := by
      filter_upwards [ae_restrict_of_ae hu_eq, ae_restrict_mem measurableSet_ball]
        with x hx hxmem
      rw [huval x hxmem, hvval x hxmem, hx]
    have hgrads := Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (U := Metric.ball x0 ((m : ℝ) + 1)) Metric.isOpen_ball hvals
    exact hugrad.symm.trans (hgrads.trans hvgrad)

/-- A globally continuous scalar coefficient with positive two-sided bounds on a
measurable window carries the matrix ellipticity used by the local theory. -/
private theorem isEllipticFieldOn_scalarCoeffField_of_continuous
    {W : Set (Vec d)} (hW : MeasurableSet W) {s : Vec d → ℝ} (hs : Continuous s)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hbounds : ∀ x ∈ W, lam ≤ s x ∧ s x ≤ Lam) :
    IsEllipticFieldOn lam Lam W (scalarCoeffField s) := by
  classical
  constructor
  · refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_
    by_cases hij : i = j
    · subst hij
      have hrw : (fun x : Vec d ↦ if x ∈ W then scalarCoeffField s x i i else 0)
          = fun x ↦ if x ∈ W then s x else 0 := by
        funext x
        by_cases hx : x ∈ W <;> simp [hx, scalarCoeffField, scalarMatrix]
      rw [hrw]
      exact Measurable.ite hW hs.measurable measurable_const
    · have hzero : (fun x : Vec d ↦ if x ∈ W then scalarCoeffField s x i j else 0)
          = fun _ ↦ (0 : ℝ) := by
        funext x
        simp [scalarCoeffField, scalarMatrix, hij]
      rw [hzero]
      exact measurable_const
  · intro x hx
    have hspos : 0 < s x := hlam.trans_le (hbounds x hx).1
    exact (isEllipticMatrix_scalarMatrix hspos).mono hlam
      (hbounds x hx).1 (hbounds x hx).2

/-- A continuous positive coefficient is uniformly elliptic on every ball. -/
theorem exists_isEllipticFieldOn_ball_of_continuous_pos
    {a : Vec d → ℝ} (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ lam Lam : ℝ,
      IsEllipticFieldOn lam Lam (Metric.ball x0 r) (scalarCoeffField a) ∧
      ∀ x ∈ Metric.ball x0 r, a x ≤ Lam := by
  classical
  have hK : IsCompact (Metric.closedBall x0 r) := isCompact_closedBall x0 r
  have hne : (Metric.closedBall x0 r).Nonempty := ⟨x0, Metric.mem_closedBall_self hr.le⟩
  obtain ⟨xmin, hxmin, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  refine ⟨a xmin, a xmax, ?_, ?_⟩
  · refine isEllipticFieldOn_scalarCoeffField_of_continuous measurableSet_ball hcont
      (hpos xmin) ?_
    intro x hx
    exact ⟨hmin (Metric.ball_subset_closedBall hx),
      hmax (Metric.ball_subset_closedBall hx)⟩
  · intro x hx
    exact hmax (Metric.ball_subset_closedBall hx)

/-- **Uniqueness for a continuous positive coefficient of subquadratic growth.**

If the coefficient is bounded by `A m` on `B_{3(m+1)}(x0)` and `A m = o(m^2)`,
the whole-space divergence resolvent solution is unique.  This is the concrete
form in which a coefficient growth estimate discharges the universal uniqueness
clause of `l.whole.space.resolvent.estimates`. -/
theorem wholeSpaceDivergenceResolventSolution_ae_eq_of_subquadratic_bound
    {a : Vec d → ℝ} {t : ℝ} {f : Vec d → ℝ} {x0 : Vec d} {A : ℕ → ℝ}
    (ht : 0 < t) (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    (hfL2 : MemLp f 2 volume)
    (hA : ∀ m : ℕ, ∀ x ∈ Metric.ball x0 (3 * ((m : ℝ) + 1)), a x ≤ A m)
    (hAlim : Filter.Tendsto (fun m : ℕ ↦ (((m : ℝ) + 1) ^ 2)⁻¹ * A m)
      Filter.atTop (nhds 0))
    (u v : WholeSpaceDivergenceResolventSolution a t f) :
    u.toFun =ᵐ[volume] v.toFun ∧ u.grad =ᵐ[volume] v.grad := by
  classical
  have hduv : Integrable (fun x ↦ (u.toFun x - v.toFun x) ^ 2) volume :=
    (u.memL2_toFun.sub v.memL2_toFun).integrable_sq
  set C : ℝ := ∫ x, (u.toFun x - v.toFun x) ^ 2 ∂volume with hC_def
  have hC0 : 0 ≤ C := integral_nonneg fun x ↦ sq_nonneg _
  have hAnonneg : ∀ m : ℕ, 0 ≤ A m := by
    intro m
    have hx0 : x0 ∈ Metric.ball x0 (3 * ((m : ℝ) + 1)) := by
      refine Metric.mem_ball_self ?_
      positivity
    exact le_trans (hpos x0).le (hA m x0 hx0)
  have hupper : ∀ m : ℕ,
      (((m : ℝ) + 1) ^ 2)⁻¹ *
          ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
            a x * (u.toFun x - v.toFun x) ^ 2 ∂volume ≤
        (((m : ℝ) + 1) ^ 2)⁻¹ * A m * C := by
    intro m
    have hint1 : IntegrableOn (fun x ↦ a x * (u.toFun x - v.toFun x) ^ 2)
        (Metric.ball x0 (3 * ((m : ℝ) + 1))) volume := by
      refine Integrable.mono' (hduv.integrableOn.const_mul (A m)) ?_ ?_
      · exact (hcont.aestronglyMeasurable.mul hduv.aestronglyMeasurable).restrict
      · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        have h1 := (hpos x).le
        have h2 := hA m x hx
        have h3 : (0 : ℝ) ≤ (u.toFun x - v.toFun x) ^ 2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith
    have hle : ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
          a x * (u.toFun x - v.toFun x) ^ 2 ∂volume ≤ A m * C := by
      have hstep1 : ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
            a x * (u.toFun x - v.toFun x) ^ 2 ∂volume ≤
          ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
            A m * (u.toFun x - v.toFun x) ^ 2 ∂volume := by
        refine integral_mono_ae hint1 (hduv.integrableOn.const_mul (A m)) ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        have h2 := hA m x hx
        nlinarith [sq_nonneg (u.toFun x - v.toFun x)]
      have hstep2 : ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
            A m * (u.toFun x - v.toFun x) ^ 2 ∂volume ≤ A m * C := by
        rw [integral_const_mul, hC_def]
        refine mul_le_mul_of_nonneg_left ?_ (hAnonneg m)
        refine setIntegral_le_integral hduv ?_
        filter_upwards with x
        positivity
      linarith
    have hpos' : (0 : ℝ) ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by positivity
    calc (((m : ℝ) + 1) ^ 2)⁻¹ *
          ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
            a x * (u.toFun x - v.toFun x) ^ 2 ∂volume
        ≤ (((m : ℝ) + 1) ^ 2)⁻¹ * (A m * C) := mul_le_mul_of_nonneg_left hle hpos'
      _ = (((m : ℝ) + 1) ^ 2)⁻¹ * A m * C := by ring
  have hlower : ∀ m : ℕ, (0 : ℝ) ≤ (((m : ℝ) + 1) ^ 2)⁻¹ *
      ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
        a x * (u.toFun x - v.toFun x) ^ 2 ∂volume := by
    intro m
    have : (0 : ℝ) ≤ ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
        a x * (u.toFun x - v.toFun x) ^ 2 ∂volume :=
      setIntegral_nonneg measurableSet_ball fun x _ ↦
        mul_nonneg (hpos x).le (sq_nonneg _)
    positivity
  have hgrow : Filter.Tendsto
      (fun m : ℕ ↦ (((m : ℝ) + 1) ^ 2)⁻¹ *
        ∫ x in Metric.ball x0 (3 * ((m : ℝ) + 1)),
          a x * (u.toFun x - v.toFun x) ^ 2 ∂volume)
      Filter.atTop (nhds 0) := by
    have hmaj : Filter.Tendsto (fun m : ℕ ↦ (((m : ℝ) + 1) ^ 2)⁻¹ * A m * C)
        Filter.atTop (nhds 0) := by
      simpa using hAlim.mul_const C
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj
      (fun m ↦ hlower m) (fun m ↦ hupper m)
  exact wholeSpaceDivergenceResolventSolution_ae_eq_of_growth ht
    (fun x ↦ (hpos x).le) hcont.aestronglyMeasurable hfL2
    (fun r hr ↦ exists_isEllipticFieldOn_ball_of_continuous_pos hcont hpos x0 hr)
    u v hgrow



theorem finiteCutoffWholeSpaceSolution_ae_eq_of_subquadratic_bound
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {t : ℝ} (ht : 0 < t) {f : Vec d → ℝ} (hf : MemLp f 2 volume)
    {x0 : Vec d} {A : ℕ → ℝ}
    (hA : ∀ m : ℕ, ∀ x ∈ Metric.ball x0 (3 * ((m : ℝ) + 1)),
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤ A m)
    (hAlim : Filter.Tendsto (fun m : ℕ ↦ (((m : ℝ) + 1) ^ 2)⁻¹ * A m)
      Filter.atTop (nhds 0))
    (u v : WholeSpaceDivergenceResolventSolution
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) t f) :
    u.toFun =ᵐ[volume] v.toFun ∧ u.grad =ᵐ[volume] v.grad :=
  wholeSpaceDivergenceResolventSolution_ae_eq_of_subquadratic_bound ht
    (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega) hf hA hAlim u v

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
