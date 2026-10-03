module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The `L^xi` moment `(∫ |X| ^ xi)^(1/xi)`. -/
def lpMoment (mu : Measure Omega) (xi : ℝ) (f : Omega → ℝ) : ℝ :=
  (∫ omega, |f omega| ^ xi ∂mu) ^ xi⁻¹

theorem lpMoment_nonneg (mu : Measure Omega) (xi : ℝ) (f : Omega → ℝ) :
    0 ≤ lpMoment mu xi f :=
  Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _) _

/-- The `eLpNorm` of a function in `L^xi` is the `ENNReal` image of its
`lpMoment`. -/
theorem eLpNorm_eq_ofReal_lpMoment {f : Omega → ℝ} {xi : ℝ} (hxi : 0 < xi)
    (hf : MemLp f (ENNReal.ofReal xi) mu) :
    eLpNorm f (ENNReal.ofReal xi) mu = ENNReal.ofReal (lpMoment mu xi f) := by
  have h := hf.eLpNorm_eq_integral_rpow_norm
    (by simpa using (ENNReal.ofReal_pos.mpr hxi).ne') ENNReal.ofReal_ne_top
  rw [h, ENNReal.toReal_ofReal hxi.le]
  simp only [lpMoment, Real.norm_eq_abs]

/-- Minkowski's inequality for `lpMoment`. -/
theorem lpMoment_add_le {f g : Omega → ℝ} {xi : ℝ} (hxi : 1 ≤ xi)
    (hf : MemLp f (ENNReal.ofReal xi) mu) (hg : MemLp g (ENNReal.ofReal xi) mu) :
    lpMoment mu xi (fun omega => f omega + g omega) ≤
      lpMoment mu xi f + lpMoment mu xi g := by
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal xi := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hxi
  have hsum : MemLp (fun omega => f omega + g omega) (ENNReal.ofReal xi) mu :=
    hf.add hg
  have htri := eLpNorm_add_le (f := f) (g := g) hone (μ := mu)
  rw [show (f + g) = fun omega => f omega + g omega from rfl] at htri
  rw [eLpNorm_eq_ofReal_lpMoment hxi0 hsum, eLpNorm_eq_ofReal_lpMoment hxi0 hf,
    eLpNorm_eq_ofReal_lpMoment hxi0 hg,
    ← ENNReal.ofReal_add (lpMoment_nonneg mu xi f) (lpMoment_nonneg mu xi g)] at htri
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (lpMoment_nonneg mu xi f) (lpMoment_nonneg mu xi g))).1 htri

/-- Minkowski's inequality for a finite sum. -/
theorem lpMoment_finsetSum_le {iota : Type*} (s : Finset iota)
    {F : iota → Omega → ℝ} {xi : ℝ} (hxi : 1 ≤ xi)
    (hF : ∀ i ∈ s, MemLp (F i) (ENNReal.ofReal xi) mu) :
    lpMoment mu xi (fun omega => ∑ i ∈ s, F i omega) ≤
      ∑ i ∈ s, lpMoment mu xi (F i) := by
  classical
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have hzero : lpMoment mu xi (fun _ : Omega => (0 : ℝ)) = 0 := by
        simp only [lpMoment, abs_zero]
        rw [Real.zero_rpow hxi0.ne', integral_zero,
          Real.zero_rpow (inv_ne_zero hxi0.ne')]
      rw [hzero]
  | insert i s hi ih =>
      have hFi : MemLp (F i) (ENNReal.ofReal xi) mu :=
        hF i (Finset.mem_insert_self i s)
      have hFs : ∀ j ∈ s, MemLp (F j) (ENNReal.ofReal xi) mu :=
        fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have hsum : MemLp (fun omega => ∑ j ∈ s, F j omega)
          (ENNReal.ofReal xi) mu :=
        memLp_finset_sum s hFs
      have hstep := lpMoment_add_le (mu := mu) hxi hFi hsum
      have hrw : (fun omega => ∑ j ∈ insert i s, F j omega) =
          fun omega => F i omega + ∑ j ∈ s, F j omega := by
        funext omega
        rw [Finset.sum_insert hi]
      rw [hrw, Finset.sum_insert hi]
      exact hstep.trans (by linarith [ih hFs])

/-- Monotonicity of `lpMoment` under a pointwise bound on absolute values. -/
theorem lpMoment_mono {f g : Omega → ℝ} {xi : ℝ} (hxi : 0 < xi)
    (hfint : Integrable (fun omega => |f omega| ^ xi) mu)
    (hg : Integrable (fun omega => |g omega| ^ xi) mu)
    (hfg : ∀ omega, |f omega| ≤ |g omega|) :
    lpMoment mu xi f ≤ lpMoment mu xi g := by
  have hf : ∀ omega, |f omega| ^ xi ≤ |g omega| ^ xi := fun omega =>
    Real.rpow_le_rpow (abs_nonneg _) (hfg omega) hxi.le
  have hint := integral_mono hfint hg (fun omega => hf omega)
  exact Real.rpow_le_rpow
    (integral_nonneg fun omega => Real.rpow_nonneg (abs_nonneg _) _) hint
    (by positivity)

/-- Membership in `L^xi` gives integrability of the `xi`-th absolute power. -/
theorem integrable_abs_rpow_of_memLp {f : Omega → ℝ} {xi : ℝ} (hxi : 0 < xi)
    (hf : MemLp f (ENNReal.ofReal xi) mu) :
    Integrable (fun omega => |f omega| ^ xi) mu := by
  have hint := hf.integrable_norm_rpow
    (by simpa using (ENNReal.ofReal_pos.mpr hxi).ne') ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hxi.le] at hint
  simpa only [Real.norm_eq_abs] using hint

/-- `lpMoment` is absolutely homogeneous. -/
theorem lpMoment_const_mul {f : Omega → ℝ} {xi : ℝ} (hxi : 0 < xi) (c : ℝ) :
    lpMoment mu xi (fun omega => c * f omega) = |c| * lpMoment mu xi f := by
  have hrw : ∀ omega, |c * f omega| ^ xi = |c| ^ xi * |f omega| ^ xi := by
    intro omega
    rw [abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg (f omega))]
  simp only [lpMoment, hrw]
  rw [integral_const_mul,
    Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) xi)
      (integral_nonneg fun omega => Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg c), mul_inv_cancel₀ hxi.ne', Real.rpow_one]

/-- `lpMoment` of a constant on a probability measure. -/
theorem lpMoment_const [IsProbabilityMeasure mu] {xi : ℝ} (hxi : 0 < xi)
    (c : ℝ) : lpMoment mu xi (fun _ => c) = |c| := by
  simp only [lpMoment, integral_const, probReal_univ, smul_eq_mul,
    one_mul]
  rw [← Real.rpow_mul (abs_nonneg c), mul_inv_cancel₀ hxi.ne', Real.rpow_one]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
