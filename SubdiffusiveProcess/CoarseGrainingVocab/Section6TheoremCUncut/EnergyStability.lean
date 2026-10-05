module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.UniformEllipticity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ComparisonConvergence

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Cauchy–Schwarz for the defect at one point -/

/-- The pointwise Cauchy–Schwarz bound of `EnergyIdentity.defect_le` with the
defect hypothesis at the single point where it is used. -/
theorem defect_le_at {a b : Vec d → ℝ} {K : ℝ} (hKnn : 0 ≤ K)
    (gu gw : Vec d → Vec d) {x : Vec d} (hx : |a x - b x| ≤ K) :
    (a x - b x) * vecDot (gu x) (gw x) ≤
      K * (euclideanNorm (gu x) * euclideanNorm (gw x)) := by
  have hprod : euclideanNorm (gu x) * euclideanNorm (gw x) =
      Real.sqrt (vecNormSq (gu x) * vecNormSq (gw x)) := by
    rw [euclideanNorm, euclideanNorm, ← Real.sqrt_mul (vecNormSq_nonneg _)]
  have habs_cs : |vecDot (gu x) (gw x)| ≤
      euclideanNorm (gu x) * euclideanNorm (gw x) := by
    rw [hprod, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq _ _)
  calc (a x - b x) * vecDot (gu x) (gw x)
      ≤ |(a x - b x) * vecDot (gu x) (gw x)| := le_abs_self _
    _ = |a x - b x| * |vecDot (gu x) (gw x)| := abs_mul _ _
    _ ≤ K * (euclideanNorm (gu x) * euclideanNorm (gw x)) :=
        mul_le_mul hx habs_cs (abs_nonneg _) hKnn

/-! ### The energy comparison with a window-local defect -/

/-- **The energy comparison, with the defect bound localized to the window.**
Identical to `Section6TheoremC.integral_vecNormSq_grad_le_on` except that the
coefficient defect is only assumed on `W`. -/
theorem integral_vecNormSq_grad_le_on_window {W : Set (Vec d)}
    {a b : Vec d → ℝ} {lam Lam lam' Lam' K : ℝ}
    {u v : H1Function W} {w : H10Function W}
    (hW : MeasurableSet W) (hlam : 0 < lam) (hKnn : 0 ≤ K)
    (hElla : IsEllipticFieldOn lam' Lam' W (scalarCoeffField a))
    (hEllb : IsEllipticFieldOn lam Lam W (scalarCoeffField b))
    (hb : ∀ x ∈ W, lam ≤ b x) (hK : ∀ x ∈ W, |a x - b x| ≤ K)
    (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn b W v)
    (hgrad : ∀ x, v.grad x = u.grad x + w.toH1Function.grad x) :
    ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume ≤
      (K / lam) ^ 2 * ∫ x in W, vecNormSq (u.grad x) ∂volume := by
  set Iw := ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume with hIwdef
  set Iu := ∫ x in W, vecNormSq (u.grad x) ∂volume with hIudef
  have hIw : IntegrableOn (fun x ↦ vecNormSq (w.toH1Function.grad x)) W :=
    integrableOn_vecNormSq_zeroTraceGrad w
  have hIu : IntegrableOn (fun x ↦ vecNormSq (u.grad x)) W :=
    integrableOn_vecNormSq_h1Grad u
  have hE : IntegrableOn
      (fun x ↦ b x * vecNormSq (w.toH1Function.grad x)) W :=
    integrableOn_mul_vecNormSq_grad hEllb w.toH1Function
  have hD : IntegrableOn
      (fun x ↦ (a x - b x) *
        vecDot (u.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_defect hElla hEllb u w.toH1Function
  have hintv : IntegrableOn
      (fun x ↦ vecDot (b x • v.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_vecDot_smul_grad hEllb v w.toH1Function
  have hintu : IntegrableOn
      (fun x ↦ vecDot (a x • u.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_vecDot_smul_grad hElla u w.toH1Function
  have hleft : lam * Iw ≤
      ∫ x in W, b x * vecNormSq (w.toH1Function.grad x) ∂volume := by
    rw [hIwdef, ← integral_const_mul]
    exact lower_bound_energy_on hW hb (hIw.const_mul lam) hE
  have hYoung : ∀ x ∈ W,
      (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x) ≤
        K ^ 2 / (2 * lam) * vecNormSq (u.grad x) +
          lam / 2 * vecNormSq (w.toH1Function.grad x) := by
    intro x hx
    refine (defect_le_at hKnn u.grad w.toH1Function.grad (hK x hx)).trans ?_
    have hy := young_pointwise (K := K) (A := euclideanNorm (u.grad x))
      (B := euclideanNorm (w.toH1Function.grad x)) hlam
    rwa [euclideanNorm_sq, euclideanNorm_sq] at hy
  have hRint : IntegrableOn
      (fun x ↦ K ^ 2 / (2 * lam) * vecNormSq (u.grad x) +
        lam / 2 * vecNormSq (w.toH1Function.grad x)) W :=
    (hIu.const_mul _).add (hIw.const_mul _)
  have hright : ∫ x in W, (a x - b x) *
        vecDot (u.grad x) (w.toH1Function.grad x) ∂volume ≤
      K ^ 2 / (2 * lam) * Iu + lam / 2 * Iw := by
    have hmono := setIntegral_mono_on hD hRint hW hYoung
    rwa [integral_add (hIu.const_mul _) (hIw.const_mul _),
      integral_const_mul, integral_const_mul] at hmono
  have hid := integral_energy_eq hu hv hgrad hintv hintu hE hD
  have hchain : lam * Iw ≤ K ^ 2 / (2 * lam) * Iu + lam / 2 * Iw := by
    rw [hid] at hleft; exact hleft.trans hright
  have hhalf : lam / 2 * Iw ≤ K ^ 2 / (2 * lam) * Iu := by linarith
  have key : lam ^ 2 * Iw ≤ K ^ 2 * Iu := by
    have h := mul_le_mul_of_nonneg_left hhalf (by linarith : (0 : ℝ) ≤ 2 * lam)
    calc lam ^ 2 * Iw = 2 * lam * (lam / 2 * Iw) := by ring
      _ ≤ 2 * lam * (K ^ 2 / (2 * lam) * Iu) := h
      _ = K ^ 2 * Iu := by field_simp
  rw [div_pow, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < lam ^ 2)]
  linarith [key]

/-! ### The limit along the cutoff sequence -/

/-- **The Dirichlet energy of the comparison difference vanishes.**  With the
ellipticity constants uniform in the cutoff and the coefficients converging
uniformly on the window, the energy of `u_J - u` tends to zero.   -/
theorem tendsto_integral_vecNormSq_grad_zero {W : Set (Vec d)}
    {a : Vec d → ℝ} {b : ℕ → Vec d → ℝ} {lam Lam lam' Lam' : ℝ}
    {u : H1Function W} {v : ℕ → H1Function W} {w : ℕ → H10Function W}
    (hW : MeasurableSet W) (hlam : 0 < lam)
    (hElla : IsEllipticFieldOn lam' Lam' W (scalarCoeffField a))
    (hEllb : ∀ j, IsEllipticFieldOn lam Lam W (scalarCoeffField (b j)))
    (hb : ∀ j, ∀ x ∈ W, lam ≤ b j x)
    (hu : IsWeaklyHarmonicOn a W u)
    (hv : ∀ j, IsWeaklyHarmonicOn (b j) W (v j))
    (hgrad : ∀ j, ∀ x, (v j).grad x = u.grad x + (w j).toH1Function.grad x)
    (hdefect : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x ∈ W, |a x - b j x| ≤ ε) :
    Tendsto (fun j ↦ ∫ x in W, vecNormSq ((w j).toH1Function.grad x) ∂volume)
      atTop (nhds 0) := by
  set Iu := ∫ x in W, vecNormSq (u.grad x) ∂volume with hIudef
  have hIunn : 0 ≤ Iu := by
    rw [hIudef]
    exact setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  set eta : ℝ := lam * Real.sqrt (ε / (Iu + 1)) with hetadef
  have hquot : 0 < ε / (Iu + 1) := div_pos hε (by linarith)
  have hetapos : 0 < eta := mul_pos hlam (Real.sqrt_pos.2 hquot)
  filter_upwards [hdefect eta hetapos] with j hj
  have hEnn : 0 ≤ ∫ x in W, vecNormSq ((w j).toH1Function.grad x) ∂volume :=
    setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
  have hbound := integral_vecNormSq_grad_le_on_window (u := u) (v := v j)
    (w := w j) hW hlam hetapos.le hElla (hEllb j) (hb j) hj hu (hv j) (hgrad j)
  have hratio : (eta / lam) ^ 2 = ε / (Iu + 1) := by
    have heq : eta / lam = Real.sqrt (ε / (Iu + 1)) := by
      rw [hetadef]; field_simp
    rw [heq, Real.sq_sqrt hquot.le]
  rw [hratio] at hbound
  have hlt : ε / (Iu + 1) * Iu < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < Iu + 1)]
    nlinarith
  have : ∫ x in W, vecNormSq ((w j).toH1Function.grad x) ∂volume < ε :=
    lt_of_le_of_lt hbound hlt
  rwa [Real.norm_eq_abs, abs_of_nonneg hEnn]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
