import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.ExpDecay




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory Set

noncomputable section

/-! ### The Hausdorff moment problem for continuous functions -/

/-- A continuous function on `[0,1]` orthogonal to every monomial is orthogonal
to every polynomial. -/
theorem setIntegral_polynomial_mul_eq_zero_of_forall_pow
    {phi : ℝ → ℝ} (hphi : Continuous phi)
    (h : ∀ n : ℕ, ∫ u in Icc (0:ℝ) 1, u ^ n * phi u = 0) (p : Polynomial ℝ) :
    ∫ u in Icc (0:ℝ) 1, p.eval u * phi u = 0 := by
  have hcont : ∀ g : ℝ → ℝ, Continuous g →
      IntegrableOn (fun u ↦ g u * phi u) (Icc (0:ℝ) 1) := fun g hg ↦
    (hg.mul hphi).continuousOn.integrableOn_compact isCompact_Icc
  have hsum : ∀ u : ℝ, p.eval u * phi u =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (u ^ i * phi u) := by
    intro u
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun u _ ↦ hsum u),
    integral_finset_sum _ (fun i _ ↦ ((hcont (fun u ↦ u ^ i) (continuous_pow i)).const_mul _))]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [integral_const_mul, h i, mul_zero]

/-- **The Hausdorff moment problem, uniqueness half.**  A continuous function on
`[0,1]` all of whose moments vanish is identically zero there. -/
theorem eqOn_zero_of_forall_setIntegral_pow_mul_eq_zero
    {phi : ℝ → ℝ} (hphi : Continuous phi)
    (h : ∀ n : ℕ, ∫ u in Icc (0:ℝ) 1, u ^ n * phi u = 0) :
    EqOn phi 0 (Icc (0:ℝ) 1) := by
  have hcont : ∀ g : ℝ → ℝ, Continuous g →
      IntegrableOn (fun u ↦ g u * phi u) (Icc (0:ℝ) 1) := fun g hg ↦
    (hg.mul hphi).continuousOn.integrableOn_compact isCompact_Icc
  have habs : IntegrableOn (fun u ↦ |phi u|) (Icc (0:ℝ) 1) :=
    (hphi.abs).continuousOn.integrableOn_compact isCompact_Icc
  set C : ℝ := ∫ u in Icc (0:ℝ) 1, |phi u| with hCdef
  have hCnonneg : 0 ≤ C := setIntegral_nonneg measurableSet_Icc fun u _ ↦ abs_nonneg _
  have hnonneg : 0 ≤ ∫ u in Icc (0:ℝ) 1, phi u * phi u :=
    setIntegral_nonneg measurableSet_Icc fun u _ ↦ mul_self_nonneg _
  have hzero : ∫ u in Icc (0:ℝ) 1, phi u * phi u = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun delta hdelta ↦ ?_) hnonneg
    have hpos : 0 < delta / (C + 1) := by positivity
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 phi hphi.continuousOn
      (delta / (C + 1)) hpos
    have hsplit : ∫ u in Icc (0:ℝ) 1, (phi u - p.eval u) * phi u =
        ∫ u in Icc (0:ℝ) 1, phi u * phi u := by
      have hsub : ∀ u : ℝ, (phi u - p.eval u) * phi u =
          phi u * phi u - p.eval u * phi u := fun u ↦ by ring
      rw [setIntegral_congr_fun measurableSet_Icc (fun u _ ↦ hsub u),
        integral_sub (hcont phi hphi) (hcont _ p.continuous),
        setIntegral_polynomial_mul_eq_zero_of_forall_pow hphi h p, sub_zero]
    have hmono : ∫ u in Icc (0:ℝ) 1, (phi u - p.eval u) * phi u ≤
        ∫ u in Icc (0:ℝ) 1, (delta / (C + 1)) * |phi u| := by
      refine setIntegral_mono_on (hcont (fun u ↦ phi u - p.eval u) (hphi.sub p.continuous))
        (habs.const_mul _) measurableSet_Icc fun u hu ↦ ?_
      calc (phi u - p.eval u) * phi u ≤ |(phi u - p.eval u) * phi u| := le_abs_self _
        _ = |phi u - p.eval u| * |phi u| := abs_mul _ _
        _ ≤ (delta / (C + 1)) * |phi u| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            rw [abs_sub_comm]
            exact (hp u hu).le
    rw [hsplit] at hmono
    refine hmono.trans ?_
    rw [integral_const_mul, ← hCdef, zero_add]
    calc delta / (C + 1) * C = delta * (C / (C + 1)) := by ring
      _ ≤ delta * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hdelta.le
          rw [div_le_one (by positivity)]
          linarith
      _ = delta := mul_one delta
  have hae : (fun u ↦ phi u * phi u) =ᵐ[volume.restrict (Icc (0:ℝ) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun u ↦ mul_self_nonneg _) (hcont phi hphi)).mp hzero
  have hae' : phi =ᵐ[volume.restrict (Icc (0:ℝ) 1)] 0 := by
    filter_upwards [hae] with u hu
    exact mul_self_eq_zero.mp hu
  refine Measure.eqOn_of_ae_eq hae' hphi.continuousOn continuousOn_const ?_
  rw [interior_Icc, closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]


/-! ### The substitution `u = exp (-t)` -/

/-- The exponential of the negative half line is the open unit interval. -/
theorem image_exp_neg_Ioi : (fun t : ℝ ↦ Real.exp (-t)) '' Ioi 0 = Ioo (0:ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.mpr (by simpa using ht)
  · rintro ⟨hu0, hu1⟩
    refine ⟨-Real.log u, ?_, ?_⟩
    · simpa using Real.log_neg hu0 hu1
    · show Real.exp (-(-Real.log u)) = u
      rw [neg_neg, Real.exp_log hu0]

/-! ### Uniqueness of the Laplace transform -/

/-- **A bounded continuous function on `[0, ∞)` with vanishing Laplace transform
vanishes.**  Mathlib has no Laplace-transform uniqueness theorem; this is the
case needed by the intrinsic time change. -/
theorem eq_zero_of_forall_integral_exp_neg_mul_eq_zero {h : ℝ → ℝ} (hcont : Continuous h)
    {C : ℝ} (hb : ∀ t, |h t| ≤ C)
    (hlap : ∀ mu : ℝ, 0 < mu → ∫ t in Ioi (0:ℝ), Real.exp (-(mu * t)) * h t = 0) :
    ∀ t : ℝ, 0 ≤ t → h t = 0 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  set phi : ℝ → ℝ := fun u ↦ if 0 < u then u * h (-Real.log u) else 0 with hphidef
  have hphi_exp : ∀ t : ℝ, phi (Real.exp (-t)) = Real.exp (-t) * h t := by
    intro t
    rw [hphidef]
    simp only [if_pos (Real.exp_pos (-t)), Real.log_exp, neg_neg]
  have hphi_bound : ∀ u : ℝ, ‖phi u‖ ≤ |u| * C := by
    intro u
    rw [hphidef]
    by_cases hu : 0 < u
    · simp only [if_pos hu, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)
    · simp only [if_neg hu, norm_zero]
      positivity
  have hphi : Continuous phi := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have heq : (fun _ : ℝ ↦ (0:ℝ)) =ᶠ[nhds x] phi := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        rw [hphidef]
        exact (if_neg (not_lt.mpr (le_of_lt hy))).symm
      exact continuousAt_const.congr heq
    · subst hx
      have h0 : phi 0 = 0 := by rw [hphidef]; simp
      rw [ContinuousAt, h0]
      refine squeeze_zero_norm hphi_bound ?_
      have hcabs : Continuous (fun y : ℝ ↦ |y| * C) := continuous_abs.mul continuous_const
      simpa using hcabs.tendsto (0 : ℝ)
    · have heq : (fun y : ℝ ↦ y * h (-Real.log y)) =ᶠ[nhds x] phi := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        rw [hphidef]
        exact (if_pos hy).symm
      refine ContinuousAt.congr ?_ heq
      exact continuousAt_id.mul
        (ContinuousAt.comp hcont.continuousAt ((Real.continuousAt_log (ne_of_gt hx)).neg))
  have hmom : ∀ n : ℕ, ∫ u in Icc (0:ℝ) 1, u ^ n * phi u = 0 := by
    intro n
    have hderiv : ∀ t ∈ Ioi (0:ℝ), HasDerivWithinAt (fun s : ℝ ↦ Real.exp (-s))
        (-Real.exp (-t)) (Ioi 0) t := by
      intro t _
      simpa using
        (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).hasDerivWithinAt (s := Ioi 0))
    have hinj : InjOn (fun s : ℝ ↦ Real.exp (-s)) (Ioi 0) := by
      intro s _ s' _ hss
      have := Real.exp_injective hss
      linarith
    have hsub := integral_image_eq_integral_abs_deriv_smul (f := fun s : ℝ ↦ Real.exp (-s))
      (f' := fun t ↦ -Real.exp (-t)) measurableSet_Ioi hderiv hinj (fun u ↦ u ^ n * phi u)
    rw [image_exp_neg_Ioi] at hsub
    rw [integral_Icc_eq_integral_Ioo, hsub]
    have hpt : ∀ t ∈ Ioi (0:ℝ),
        |(-Real.exp (-t))| • ((Real.exp (-t)) ^ n * phi (Real.exp (-t))) =
          Real.exp (-(((n : ℝ) + 2) * t)) * h t := by
      intro t _
      rw [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, hphi_exp t, ← Real.exp_nat_mul,
        show Real.exp (-t) * (Real.exp ((n : ℝ) * -t) * (Real.exp (-t) * h t)) =
          (Real.exp (-t) * Real.exp ((n : ℝ) * -t) * Real.exp (-t)) * h t by ring,
        ← Real.exp_add, ← Real.exp_add,
        show -t + (n : ℝ) * -t + -t = -(((n : ℝ) + 2) * t) by ring]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    exact hlap _ (by positivity)
  have hEq := eqOn_zero_of_forall_setIntegral_pow_mul_eq_zero hphi hmom
  intro t ht
  have hmem : Real.exp (-t) ∈ Icc (0:ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_le_exp.mpr (by simpa using ht)
  have hzero : Real.exp (-t) * h t = 0 := by
    rw [← hphi_exp t]
    simpa using hEq hmem
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (Real.exp_pos _))

/-- **Uniqueness of the Laplace transform on the half line.**  Two bounded
continuous functions whose Laplace transforms agree at every positive `μ` agree
on `[0, ∞)`. -/
theorem eq_of_forall_integral_exp_neg_mul_eq {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) {C : ℝ}
    (hFb : ∀ t, |F t| ≤ C) (hGb : ∀ t, |G t| ≤ C)
    (hlap : ∀ mu : ℝ, 0 < mu →
      ∫ t in Ioi (0:ℝ), Real.exp (-(mu * t)) * F t =
        ∫ t in Ioi (0:ℝ), Real.exp (-(mu * t)) * G t) :
    ∀ t : ℝ, 0 ≤ t → F t = G t := by
  have hint : ∀ (H : ℝ → ℝ), Continuous H → (∀ t, |H t| ≤ C) → ∀ mu : ℝ, 0 < mu →
      IntegrableOn (fun t ↦ Real.exp (-(mu * t)) * H t) (Ioi (0:ℝ)) := by
    intro H hH hHb mu hmu
    have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hHb 0)
    have hmeas : AEStronglyMeasurable (fun t ↦ Real.exp (-(mu * t)) * H t)
        (volume.restrict (Ioi (0:ℝ))) :=
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).mul
        hH).aestronglyMeasurable
    have hdom : IntegrableOn (fun t ↦ C * Real.exp (-(mu * t))) (Ioi (0:ℝ)) := by
      have hbase := (exp_neg_integrableOn_Ioi (b := mu) 0 hmu).const_mul C
      simpa [neg_mul] using hbase
    refine Integrable.mono hdom hmeas (Filter.Eventually.of_forall fun t ↦ ?_)
    have habs : |Real.exp (-(mu * t))| = Real.exp (-(mu * t)) := abs_of_pos (Real.exp_pos _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, habs, abs_of_nonneg hCnn,
      mul_comm C]
    exact mul_le_mul_of_nonneg_left (hHb t) (Real.exp_pos _).le
  have hdiff : ∀ mu : ℝ, 0 < mu →
      ∫ t in Ioi (0:ℝ), Real.exp (-(mu * t)) * (F t - G t) = 0 := by
    intro mu hmu
    have hsplit : ∀ t : ℝ, Real.exp (-(mu * t)) * (F t - G t) =
        Real.exp (-(mu * t)) * F t - Real.exp (-(mu * t)) * G t := fun t ↦ by ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ hsplit t),
      integral_sub (hint F hF hFb mu hmu) (hint G hG hGb mu hmu), hlap mu hmu, sub_self]
  have hbd : ∀ t : ℝ, |F t - G t| ≤ C + C := by
    intro t
    have h1 := abs_le.mp (hFb t)
    have h2 := abs_le.mp (hGb t)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  intro t ht
  have hzero := eq_zero_of_forall_integral_exp_neg_mul_eq_zero
    (hF.sub hG : Continuous fun t ↦ F t - G t) hbd hdiff t ht
  linarith [hzero]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
