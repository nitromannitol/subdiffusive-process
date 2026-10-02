import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletEnergyContinuity

/-!
# Energy identity for perturbations of scalar Dirichlet coefficients

This module records the same-trace energy identity used when passing
Dirichlet solutions to a locally uniform coefficient limit.  It is stated for
the section 6 scalar weak-harmonic carrier and is independent of any
probabilistic or cutoff construction.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- Two `H¹` functions with the same boundary datum have an `H¹₀`
difference with the literal pointwise value and gradient representatives. -/
theorem exists_h10Function_sub_of_same_trace {W : Set (Vec d)}
    {u v h : H1Function W}
    (hu : HasZeroTraceDifferenceOn W u h)
    (hv : HasZeroTraceDifferenceOn W v h) :
    ∃ w : H10Function W,
      (∀ x, w.toH1Function.toFun x = u.toFun x - v.toFun x) ∧
        ∀ x, w.toH1Function.grad x = u.grad x - v.grad x := by
  obtain ⟨wu, hwuf, hwug⟩ := hu
  obtain ⟨wv, hwvf, hwvg⟩ := hv
  refine ⟨wu - wv, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [show (wu - wv).toH1Function.toFun x =
        wu.toH1Function.toFun x - wv.toH1Function.toFun x by
      change (wu.toH1Function - wv.toH1Function).toFun x = _
      rw [H1Function.sub_toFun], hwuf x, hwvf x]
    ring
  · rw [show (wu - wv).toH1Function.grad x =
        wu.toH1Function.grad x - wv.toH1Function.grad x by
      change (wu.toH1Function - wv.toH1Function).grad x = _
      rw [H1Function.sub_grad], hwug x, hwvg x]
    abel

private theorem scalar_flux_sub_identity (a : ℝ) (p q : Vec d) :
    vecDot (a • p) (p - q) - vecDot (a • q) (p - q) =
      a * vecNormSq (p - q) := by
  classical
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem coefficient_difference_flux_identity
    (a b : ℝ) (p q : Vec d) :
    vecDot (b • q) (p - q) - vecDot (a • q) (p - q) =
      (b - a) * vecDot q (p - q) := by
  rw [vecDot_smul_left, vecDot_smul_left]
  ring

/-- **Same-trace coefficient-perturbation energy identity.**  If `u` is
`a`-harmonic, `v` is `b`-harmonic, and both have the same trace, then

`int a |grad u - grad v|² = int (b-a) grad v · (grad u-grad v)`.

The three explicit integrability hypotheses are exactly what local boundedness
of the coefficients supplies on a bounded cube. -/
theorem integral_coefficient_mul_gradDifference_sq_eq
    {W : Set (Vec d)} {a b : Vec d → ℝ} {u v h : H1Function W}
    (huTrace : HasZeroTraceDifferenceOn W u h)
    (hvTrace : HasZeroTraceDifferenceOn W v h)
    (huHarm : IsWeaklyHarmonicOn a W u)
    (hvHarm : IsWeaklyHarmonicOn b W v)
    (hau : IntegrableOn
      (fun x ↦ vecDot (a x • u.grad x) (u.grad x - v.grad x)) W)
    (hav : IntegrableOn
      (fun x ↦ vecDot (a x • v.grad x) (u.grad x - v.grad x)) W)
    (hbv : IntegrableOn
      (fun x ↦ vecDot (b x • v.grad x) (u.grad x - v.grad x)) W) :
    (∫ x in W, a x * vecNormSq (u.grad x - v.grad x) ∂volume) =
      ∫ x in W, (b x - a x) *
        vecDot (v.grad x) (u.grad x - v.grad x) ∂volume := by
  obtain ⟨w, _hwf, hwg⟩ :=
    exists_h10Function_sub_of_same_trace huTrace hvTrace
  have hua :
      (∫ x in W, vecDot (a x • u.grad x) (u.grad x - v.grad x) ∂volume) = 0 := by
    simpa only [hwg] using huHarm w
  have hvb :
      (∫ x in W, vecDot (b x • v.grad x) (u.grad x - v.grad x) ∂volume) = 0 := by
    simpa only [hwg] using hvHarm w
  calc
    (∫ x in W, a x * vecNormSq (u.grad x - v.grad x) ∂volume) =
        ∫ x in W,
          (vecDot (a x • u.grad x) (u.grad x - v.grad x) -
            vecDot (a x • v.grad x) (u.grad x - v.grad x)) ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        (scalar_flux_sub_identity (a x) (u.grad x) (v.grad x)).symm
    _ = (∫ x in W,
          vecDot (a x • u.grad x) (u.grad x - v.grad x) ∂volume) -
        ∫ x in W,
          vecDot (a x • v.grad x) (u.grad x - v.grad x) ∂volume :=
      integral_sub hau hav
    _ = -(∫ x in W,
          vecDot (a x • v.grad x) (u.grad x - v.grad x) ∂volume) := by
      rw [hua, zero_sub]
    _ = (∫ x in W,
          vecDot (b x • v.grad x) (u.grad x - v.grad x) ∂volume) -
        ∫ x in W,
          vecDot (a x • v.grad x) (u.grad x - v.grad x) ∂volume := by
      rw [hvb, zero_sub]
    _ = ∫ x in W,
          (vecDot (b x • v.grad x) (u.grad x - v.grad x) -
            vecDot (a x • v.grad x) (u.grad x - v.grad x)) ∂volume :=
      (integral_sub hbv hav).symm
    _ = ∫ x in W, (b x - a x) *
          vecDot (v.grad x) (u.grad x - v.grad x) ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        coefficient_difference_flux_identity (a x) (b x) (u.grad x) (v.grad x)

/-- The coefficient-error flux is bounded by the `L∞` coefficient error times
the two vector `L²` norms. -/
theorem abs_integral_coefficientDifference_flux_le
    {W : Set (Vec d)} {a b : Vec d → ℝ} {F G : Vec d → Vec d} {eta : ℝ}
    (hWm : MeasurableSet W) (heta : 0 ≤ eta)
    (hclose : ∀ x ∈ W, |b x - a x| ≤ eta)
    (hF : IntegrableOn (fun x ↦ vecNormSq (F x)) W)
    (hG : IntegrableOn (fun x ↦ vecNormSq (G x)) W)
    (hpair : IntegrableOn
      (fun x ↦ (b x - a x) * vecDot (F x) (G x)) W) :
    |∫ x in W, (b x - a x) * vecDot (F x) (G x) ∂volume| ≤
      eta * (Section5Support.l2NormOn W F *
        Section5Support.l2NormOn W G) := by
  have hproduct := Section5Support.integrableOn_sqrt_vecNormSq_mul hF hG
  have hpoint : ∀ x ∈ W,
      |(b x - a x) * vecDot (F x) (G x)| ≤
        eta * (Real.sqrt (vecNormSq (F x)) * Real.sqrt (vecNormSq (G x))) := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hclose x hx)
      (Section5Support.abs_vecDot_le_sqrt_mul_sqrt (F x) (G x))
      (abs_nonneg _) heta
  calc
    |∫ x in W, (b x - a x) * vecDot (F x) (G x) ∂volume| ≤
        ∫ x in W, |(b x - a x) * vecDot (F x) (G x)| ∂volume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in W,
        eta * (Real.sqrt (vecNormSq (F x)) * Real.sqrt (vecNormSq (G x)))
          ∂volume :=
      setIntegral_mono_on hpair.abs (hproduct.const_mul eta) hWm hpoint
    _ = eta * ∫ x in W,
        Real.sqrt (vecNormSq (F x)) * Real.sqrt (vecNormSq (G x)) ∂volume :=
      integral_const_mul _ _
    _ ≤ eta * (Section5Support.l2NormOn W F *
        Section5Support.l2NormOn W G) :=
      mul_le_mul_of_nonneg_left
        (Section5Support.integral_sqrt_vecNormSq_mul_le hF hG) heta

/-- **Strong-gradient stability under a scalar coefficient perturbation.**
Same-trace harmonic solutions for `a` and `b` differ in gradient by at most
`eta / lambda` times the reference gradient whenever `a ≥ lambda > 0` and
`|b-a| ≤ eta` on the domain. -/
theorem l2NormOn_gradDifference_le_of_coefficient_close
    {W : Set (Vec d)} {a b : Vec d → ℝ} {u v h : H1Function W}
    {lambda eta : ℝ}
    (hWm : MeasurableSet W) (hlambda : 0 < lambda) (heta : 0 ≤ eta)
    (halow : ∀ x ∈ W, lambda ≤ a x)
    (hclose : ∀ x ∈ W, |b x - a x| ≤ eta)
    (huTrace : HasZeroTraceDifferenceOn W u h)
    (hvTrace : HasZeroTraceDifferenceOn W v h)
    (huHarm : IsWeaklyHarmonicOn a W u)
    (hvHarm : IsWeaklyHarmonicOn b W v)
    (hau : IntegrableOn
      (fun x ↦ vecDot (a x • u.grad x) (u.grad x - v.grad x)) W)
    (hav : IntegrableOn
      (fun x ↦ vecDot (a x • v.grad x) (u.grad x - v.grad x)) W)
    (hbv : IntegrableOn
      (fun x ↦ vecDot (b x • v.grad x) (u.grad x - v.grad x)) W) :
    Section5Support.l2NormOn W (fun x ↦ u.grad x - v.grad x) ≤
      eta / lambda * Section5Support.l2NormOn W v.grad := by
  let D : Vec d → Vec d := fun x ↦ u.grad x - v.grad x
  have hD : IntegrableOn (fun x ↦ vecNormSq (D x)) W :=
    Section5Support.integrableOn_vecNormSq_sub_grad u v
  have hV : IntegrableOn (fun x ↦ vecNormSq (v.grad x)) W :=
    Section5Support.integrableOn_vecNormSq_of_memLp v.gradMemL2
  have henergy : IntegrableOn (fun x ↦ a x * vecNormSq (D x)) W := by
    exact (hau.sub hav).congr (Filter.Eventually.of_forall fun x ↦
      scalar_flux_sub_identity (a x) (u.grad x) (v.grad x))
  have hpair : IntegrableOn
      (fun x ↦ (b x - a x) * vecDot (v.grad x) (D x)) W := by
    exact (hbv.sub hav).congr (Filter.Eventually.of_forall fun x ↦
      coefficient_difference_flux_identity
        (a x) (b x) (u.grad x) (v.grad x))
  have hid := integral_coefficient_mul_gradDifference_sq_eq
    huTrace hvTrace huHarm hvHarm hau hav hbv
  have hlower : lambda * ∫ x in W, vecNormSq (D x) ∂volume ≤
      ∫ x in W, a x * vecNormSq (D x) ∂volume := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hD.const_mul lambda) henergy hWm fun x hx ↦
      mul_le_mul_of_nonneg_right (halow x hx) (vecNormSq_nonneg _)
  have hupper :
      |∫ x in W, (b x - a x) * vecDot (v.grad x) (D x) ∂volume| ≤
        eta * (Section5Support.l2NormOn W v.grad *
          Section5Support.l2NormOn W D) :=
    abs_integral_coefficientDifference_flux_le hWm heta hclose hV hD hpair
  have hmain : lambda * (Section5Support.l2NormOn W D) ^ 2 ≤
      eta * (Section5Support.l2NormOn W v.grad *
        Section5Support.l2NormOn W D) := by
    rw [Section5Support.sq_l2NormOn hWm]
    calc
      lambda * ∫ x in W, vecNormSq (D x) ∂volume ≤
          ∫ x in W, a x * vecNormSq (D x) ∂volume := hlower
      _ = ∫ x in W, (b x - a x) * vecDot (v.grad x) (D x) ∂volume := hid
      _ ≤ |∫ x in W, (b x - a x) * vecDot (v.grad x) (D x) ∂volume| :=
        le_abs_self _
      _ ≤ eta * (Section5Support.l2NormOn W v.grad *
          Section5Support.l2NormOn W D) := hupper
  have hDnonneg := Section5Support.l2NormOn_nonneg W D
  have hVnonneg := Section5Support.l2NormOn_nonneg W v.grad
  by_cases hDzero : Section5Support.l2NormOn W D = 0
  · rw [hDzero]
    exact mul_nonneg (div_nonneg heta hlambda.le) hVnonneg
  · have hDpos : 0 < Section5Support.l2NormOn W D :=
      lt_of_le_of_ne hDnonneg (Ne.symm hDzero)
    rw [show eta / lambda * Section5Support.l2NormOn W v.grad =
      (eta * Section5Support.l2NormOn W v.grad) / lambda by
        field_simp]
    apply (le_div_iff₀ hlambda).2
    nlinarith

/-- A locally uniform scalar-coefficient approximation with a common positive
lower ellipticity bound yields strong `L²` convergence of the gradients of
same-trace harmonic solutions. -/
theorem tendsto_l2NormOn_gradDifference_of_coefficient_close
    {W : Set (Vec d)} {a : ℕ → Vec d → ℝ} {alim : Vec d → ℝ}
    {u : ℕ → H1Function W} {ulim h : H1Function W}
    {lambda : ℝ} {eta : ℕ → ℝ}
    (hWm : MeasurableSet W) (hlambda : 0 < lambda)
    (heta : ∀ n, 0 ≤ eta n)
    (heta0 : Filter.Tendsto eta Filter.atTop (nhds 0))
    (halow : ∀ n x, x ∈ W → lambda ≤ a n x)
    (hclose : ∀ n x, x ∈ W → |alim x - a n x| ≤ eta n)
    (huTrace : ∀ n, HasZeroTraceDifferenceOn W (u n) h)
    (hulimTrace : HasZeroTraceDifferenceOn W ulim h)
    (huHarm : ∀ n, IsWeaklyHarmonicOn (a n) W (u n))
    (hulimHarm : IsWeaklyHarmonicOn alim W ulim)
    (hau : ∀ n, IntegrableOn
      (fun x ↦ vecDot (a n x • (u n).grad x)
        ((u n).grad x - ulim.grad x)) W)
    (hav : ∀ n, IntegrableOn
      (fun x ↦ vecDot (a n x • ulim.grad x)
        ((u n).grad x - ulim.grad x)) W)
    (hbv : ∀ n, IntegrableOn
      (fun x ↦ vecDot (alim x • ulim.grad x)
        ((u n).grad x - ulim.grad x)) W) :
    Filter.Tendsto
      (fun n ↦ Section5Support.l2NormOn W
        (fun x ↦ (u n).grad x - ulim.grad x))
      Filter.atTop (nhds 0) := by
  have hbound : ∀ n,
      Section5Support.l2NormOn W
          (fun x ↦ (u n).grad x - ulim.grad x) ≤
        eta n / lambda * Section5Support.l2NormOn W ulim.grad := by
    intro n
    exact l2NormOn_gradDifference_le_of_coefficient_close hWm hlambda
      (heta n) (halow n) (hclose n) (huTrace n) hulimTrace
      (huHarm n) hulimHarm (hau n) (hav n) (hbv n)
  have hscaled : Filter.Tendsto
      (fun n ↦ eta n / lambda * Section5Support.l2NormOn W ulim.grad)
      Filter.atTop (nhds 0) := by
    have h := heta0.const_mul
      (lambda⁻¹ * Section5Support.l2NormOn W ulim.grad)
    simpa only [zero_mul, mul_zero, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      using h
  refine squeeze_zero
    (fun n ↦ Section5Support.l2NormOn_nonneg W
      (fun x ↦ (u n).grad x - ulim.grad x)) hbound hscaled

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
