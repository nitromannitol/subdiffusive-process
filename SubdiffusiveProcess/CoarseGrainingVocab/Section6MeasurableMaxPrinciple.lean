import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.MaxPrinciple
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory
open Homogenization (Vec H1Function H10Function vecDot vecNormSq volumeMeasureOn
  IsOpenBoundedConvexDomain)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

noncomputable section

variable {d : ℕ}

/-! ### Pointwise algebra -/

/-- The flux pairing is homogeneous in the scalar coefficient. -/
theorem vecDot_smul_left (c : ℝ) (v w : Vec d) :
    vecDot (c • v) w = c * vecDot v w := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

/-! ### The tail of the energy argument

Once the truncation is known to have a vanishing weak gradient, the conclusion is
the zero-trace Poincaré inequality and does not mention the coefficient.  This is
the coefficient-free tail of `ae_le_of_isUnitWeaklyHarmonicOn`, isolated so that
the two maximum principles share it. -/
private theorem ae_le_of_truncation_grad_ae_zero [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {u : H1Function V} {M : ℝ}
    {ψ : H10Function V}
    (hψval : ψ.toH1Function.toFun = fun y => max (u.toFun y - M) 0)
    (hgradzero : ψ.toH1Function.grad =ᵐ[volumeMeasureOn V] 0) :
    ∀ᵐ y ∂(volumeMeasureOn V), u.toFun y ≤ M := by
  have hVL2 : ψ.toH1Function.gradToVectorL2 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [ψ.toH1Function.coeFn_gradToVectorL2, hgradzero] with y h1 h2
    rw [h1, h2]
  have hS :=
    Homogenization.H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      (Homogenization.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hV)
      ψ hVL2
  have hval : ψ.toH1Function.toFun =ᵐ[volumeMeasureOn V] 0 := by
    have hc := ψ.toH1Function.coeFn_toScalarL2
    rw [hS] at hc
    filter_upwards [hc, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volumeMeasureOn V)]
      with y h1 h2
    rw [← h1, h2]
  filter_upwards [hval] with y hy
  have hmax : max (u.toFun y - M) 0 = 0 := by
    rw [← congrFun hψval y]
    simpa using hy
  have hle : u.toFun y - M ≤ 0 := max_eq_right_iff.1 hmax
  linarith only [hle]

/-! ### The maximum principle -/

/-- **The weak maximum principle for a bounded measurable scalar coefficient.**

A weakly `a`-harmonic `H¹` function on an open bounded convex window, for a
coefficient with `0 < lam ≤ a ≤ Lam` almost everywhere, which is `≤ M` on the
boundary in the zero-trace sense of `HasBoundaryUpperBoundOn`, is `≤ M` almost
everywhere in the window. -/
theorem ae_le_of_isWeaklyHarmonicOn [NeZero d] {V : Set (Vec d)}
    {a : Vec d → ℝ} {lam Lam : ℝ}
    (hV : IsOpenBoundedConvexDomain V) (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volumeMeasureOn V))
    (hbounds : ∀ᵐ y ∂(volumeMeasureOn V), lam ≤ a y ∧ a y ≤ Lam)
    {u : H1Function V} {M : ℝ}
    (hu : IsWeaklyHarmonicOn a V u) (hM : HasBoundaryUpperBoundOn V u M) :
    ∀ᵐ y ∂(volumeMeasureOn V), u.toFun y ≤ M := by
  obtain ⟨ψ, hψval, hψgrad⟩ := hM
  -- The tested integrand collapses to `a · |∇ψ|²`.
  have hae : ∀ᵐ y ∂(volumeMeasureOn V),
      vecDot (a y • u.grad y) (ψ.toH1Function.grad y) =
        a y * vecNormSq (ψ.toH1Function.grad y) := by
    filter_upwards [hψgrad] with y hy
    by_cases hmem : y ∈ {p | M < u.toFun p}
    · rw [hy, Set.indicator_of_mem hmem, vecDot_smul_left, vecNormSq]
    · rw [hy, Set.indicator_of_notMem hmem, vecDot_smul_left]
      simp [vecDot, vecNormSq]
  have hzero : ∫ y in V, a y * vecNormSq (ψ.toH1Function.grad y) ∂volume = 0 := by
    rw [← integral_congr_ae hae]
    exact hu ψ
  -- `|∇ψ|²` is integrable, being a finite sum of products of `L²` coordinates.
  have hgint : Integrable (fun y => vecNormSq (ψ.toH1Function.grad y))
      (volumeMeasureOn V) := by
    have h := integrableOn_vecDot_grad ψ.toH1Function ψ.toH1Function
    simpa [IntegrableOn, volumeMeasureOn, vecNormSq] using h
  -- The upper ellipticity bound makes `a · |∇ψ|²` integrable.
  have hint : Integrable (fun y => a y * vecNormSq (ψ.toH1Function.grad y))
      (volumeMeasureOn V) := by
    refine Integrable.mono' (hgint.const_mul |Lam|)
      (hameas.mul hgint.aestronglyMeasurable) ?_
    filter_upwards [hbounds] with y hy
    have hpos : 0 < a y := lt_of_lt_of_le hlam hy.1
    have hnn : 0 ≤ vecNormSq (ψ.toH1Function.grad y) := Homogenization.vecNormSq_nonneg _
    have habs : |a y| ≤ |Lam| := by
      rw [abs_of_pos hpos]
      exact le_trans hy.2 (le_abs_self Lam)
    calc ‖a y * vecNormSq (ψ.toH1Function.grad y)‖
        = |a y| * vecNormSq (ψ.toH1Function.grad y) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      _ ≤ |Lam| * vecNormSq (ψ.toH1Function.grad y) := by
          exact mul_le_mul_of_nonneg_right habs hnn
  -- The lower ellipticity bound makes it nonnegative, hence a.e. zero.
  have hnonneg : ∀ᵐ y ∂(volumeMeasureOn V),
      0 ≤ a y * vecNormSq (ψ.toH1Function.grad y) := by
    filter_upwards [hbounds] with y hy
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le hlam hy.1))
      (Homogenization.vecNormSq_nonneg _)
  have hprod : (fun y => a y * vecNormSq (ψ.toH1Function.grad y))
      =ᵐ[volumeMeasureOn V] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).1 hzero
  have hgradzero : ψ.toH1Function.grad =ᵐ[volumeMeasureOn V] 0 := by
    filter_upwards [hprod, hbounds] with y hy hb
    have hpos : 0 < a y := lt_of_lt_of_le hlam hb.1
    have hz : vecNormSq (ψ.toH1Function.grad y) = 0 := by
      have := hy
      simp only [Pi.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_left (ne_of_gt hpos)
    refine Homogenization.vecNormSq_eq_zero ?_
    simpa using hz
  exact ae_le_of_truncation_grad_ae_zero hV hψval hgradzero

/-! ### The two-sided form -/

/-- Weak `a`-harmonicity is preserved by negation. -/
theorem isWeaklyHarmonicOn_neg {V : Set (Vec d)} {a : Vec d → ℝ} {u : H1Function V}
    (hu : IsWeaklyHarmonicOn a V u) : IsWeaklyHarmonicOn a V (-u) := by
  intro φ
  have hrw : ∀ y, vecDot (a y • (-u).grad y) (φ.toH1Function.grad y) =
      -vecDot (a y • u.grad y) (φ.toH1Function.grad y) := by
    intro y
    simp only [Homogenization.H1Function.neg_grad, vecDot, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul, mul_neg, neg_mul, Finset.sum_neg_distrib]
  calc
    ∫ y in V, vecDot (a y • (-u).grad y) (φ.toH1Function.grad y) ∂volume
        = ∫ y in V, -vecDot (a y • u.grad y) (φ.toH1Function.grad y) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => hrw y)
    _ = -∫ y in V, vecDot (a y • u.grad y) (φ.toH1Function.grad y) ∂volume := integral_neg _
    _ = 0 := by rw [hu φ, neg_zero]

/-- **The two-sided weak maximum principle for a bounded measurable scalar
coefficient**: `‖u‖_{L^∞(V)} ≤ M` for a weakly `a`-harmonic `u` whose boundary
datum is two-sidedly bounded by `M`. -/
theorem ae_abs_le_of_isWeaklyHarmonicOn [NeZero d] {V : Set (Vec d)}
    {a : Vec d → ℝ} {lam Lam : ℝ}
    (hV : IsOpenBoundedConvexDomain V) (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volumeMeasureOn V))
    (hbounds : ∀ᵐ y ∂(volumeMeasureOn V), lam ≤ a y ∧ a y ≤ Lam)
    {u : H1Function V} {M : ℝ}
    (hu : IsWeaklyHarmonicOn a V u)
    (hupper : HasBoundaryUpperBoundOn V u M)
    (hlower : HasBoundaryUpperBoundOn V (-u) M) :
    ∀ᵐ y ∂(volumeMeasureOn V), |u.toFun y| ≤ M := by
  have h1 := ae_le_of_isWeaklyHarmonicOn hV hlam hameas hbounds hu hupper
  have h2 := ae_le_of_isWeaklyHarmonicOn hV hlam hameas hbounds
    (isWeaklyHarmonicOn_neg hu) hlower
  filter_upwards [h1, h2] with y hy1 hy2
  have hy2' : -u.toFun y ≤ M := by
    simpa using hy2
  exact abs_le.2 ⟨by linarith only [hy2'], hy1⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab
