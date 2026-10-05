module

public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.WeakTesting
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveContraction
@[expose] public section

/-! Uniform coefficient contrast controls normalized weighted torsion. The actual forcing discrepancy b-1 and the flux discrepancy are both retained in the energy identity. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter Set SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
private theorem abs_sq_eq_sq (a : ℝ) : |a| ^ 2 = a ^ 2 := by
  by_cases h : 0 ≤ a
  · rw [abs_of_nonneg h]
  · have h' : a ≤ 0 := le_of_lt (not_le.mp h)
    rw [abs_of_nonpos h']
    ring

private theorem vecDot_self_eq_vecNormSq {d : ℕ} (v : Vec d) :
    vecDot v v = vecNormSq v := by
  simp only [vecDot, vecNormSq]

private theorem vecDot_sub_left' {d : ℕ} (a b c : Vec d) :
    vecDot (a - b) c = vecDot a c - vecDot b c := by
  have h : (a - b) = a + (-b) := sub_eq_add_neg a b
  rw [h, vecDot_add_left, vecDot_neg_left]
  abel

private theorem vecDot_sub_right' {d : ℕ} (v a b : Vec d) :
    vecDot v (a - b) = vecDot v a - vecDot v b := by
  rw [vecDot_comm v (a - b), vecDot_sub_left' a b v, vecDot_comm a v, vecDot_comm b v]

private theorem vecDot_smul_right' {d : ℕ} (v : Vec d) (c : ℝ) (w : Vec d) :
    vecDot v (c • w) = c * vecDot v w := by
  rw [vecDot_comm v (c • w), vecDot_smul_left, vecDot_comm w v]

private theorem vecNormSq_smul' {d : ℕ} (c : ℝ) (v : Vec d) :
    vecNormSq (c • v) = c ^ 2 * vecNormSq v := by
  simp only [vecNormSq, vecDot_smul_left, vecDot_smul_right']
  ring

private theorem matVecMul_scalarCoeffField' {d : ℕ} (b : Vec d → ℝ) (x v : Vec d) :
    matVecMul (scalarCoeffField b x) v = b x • v := by
  exact matVecMul_scalarMatrix (b x) v

private theorem fluxSplit {d : ℕ} (A B : Vec d) (c : ℝ) :
    c * vecNormSq (A - B) =
      vecDot (c • A) (A - B) - vecDot (c • B) (A - B) := by
  have e1 : vecDot (c • A) (A - B) = c * vecDot A A - c * vecDot A B := by
    rw [vecDot_sub_right', vecDot_smul_left, vecDot_smul_left]
  have e2 : vecDot (c • B) (A - B) = c * vecDot B A - c * vecDot B B := by
    rw [vecDot_sub_right', vecDot_smul_left, vecDot_smul_left]
  have e3 : vecNormSq (A - B) =
      vecDot A A - vecDot A B - (vecDot B A - vecDot B B) := by
    rw [← vecDot_self_eq_vecNormSq (A - B), vecDot_sub_right', vecDot_sub_left',
      vecDot_sub_left', vecDot_comm B A]
  rw [e1, e2, e3, vecDot_comm B A]
  ring

private theorem integral_le_vol_sqrt {d : ℕ} {W : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)] {f : Vec d → ℝ}
    (_hWm : MeasurableSet W)
    (_hf1 : IntegrableOn f W) (hf2 : IntegrableOn (fun x => f x ^ 2) W) :
    ∫ x in W, f x ∂volume ≤
      Real.sqrt ((volume W).toReal) * Real.sqrt (∫ x in W, f x ^ 2 ∂volume) := by
  have hstep : ∫ x in W, f x ∂volume ≤ ∫ x in W, |f x| ∂volume := by
    calc ∫ x in W, f x ∂volume ≤ |∫ x in W, f x ∂volume| := le_abs_self _
      _ ≤ ∫ x in W, |f x| ∂volume := abs_integral_le_integral_abs
  have habs2 : (fun x => |f x| ^ 2) = fun x => f x ^ 2 := by
    funext x
    rw [abs_sq_eq_sq]
  have hf2abs : IntegrableOn (fun x => |f x| ^ 2) W := by
    rw [habs2]; exact hf2
  have hcs :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      (μ := volume.restrict W) (X := fun x => |f x|) (Y := fun _ : Vec d => (1 : ℝ))
      hf2abs (integrable_const ((1 : ℝ) ^ 2))
      (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
      (Filter.Eventually.of_forall fun x => by norm_num)
  have hone : ∫ x in W, (1 : ℝ) ^ 2 ∂volume = (volume W).toReal := by
    simp only [one_pow, setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  calc ∫ x in W, f x ∂volume ≤ ∫ x in W, |f x| ∂volume := hstep
    _ = ∫ x in W, |f x| * 1 ∂volume := by simp only [mul_one]
    _ ≤ Real.sqrt (∫ x in W, |f x| ^ 2 ∂volume) *
          Real.sqrt (∫ x in W, (1 : ℝ) ^ 2 ∂volume) := hcs
    _ = Real.sqrt (∫ x in W, f x ^ 2 ∂volume) *
          Real.sqrt (∫ x in W, (1 : ℝ) ^ 2 ∂volume) := by rw [habs2]
    _ = Real.sqrt ((volume W).toReal) *
          Real.sqrt (∫ x in W, f x ^ 2 ∂volume) := by rw [hone, mul_comm]

theorem goodCube_weightedTorsion_l2_comparison_of_uniform_contrast
    {d : ℕ} {W : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    {b : Vec d → ℝ} {Lam eps P : ℝ}
    (hW : MeasurableSet W)
    (hEll : IsEllipticFieldOn (1 / 2) Lam W (scalarCoeffField b))
    (hbL2 : MemL2On W b)
    (hcontrast : ∀ x ∈ W, |b x - 1| ≤ eps)
    (heps : 0 ≤ eps) (hP : 0 ≤ P)
    (hPoincare : ∀ f : H10Function W,
      Real.sqrt (∫ x in W, (f.toH1Function.toFun x)^2 ∂volume) ≤
        P * Real.sqrt (∫ x in W, vecNormSq (f.toH1Function.grad x) ∂volume))
    (u w : H10Function W)
    (hu : IsMassiveWeakSolutionOn b b 0 W u.toH1Function (fun _ => 1))
    (hw : IsMassiveWeakSolutionOn (fun _ => 1) (fun _ => 1) 0 W
      w.toH1Function (fun _ => 1)) :
    Real.sqrt (∫ x in W, ((u - w).toH1Function.toFun x)^2 ∂volume) ≤
      4 * P^2 * eps * Real.sqrt ((volume W).toReal) := by
  have hscalar : ∀ x v : Vec d, matVecMul (scalarCoeffField b x) v = b x • v :=
    fun x v => matVecMul_scalarCoeffField' b x v
  have hgradR : ∀ x : Vec d, (u - w).toH1Function.grad x =
      u.toH1Function.grad x - w.toH1Function.grad x := by
    intro x
    change (u.toH1Function - w.toH1Function).grad x = _
    rw [H1Function.sub_grad]
  have hUg : MemVectorL2 W u.toH1Function.grad := u.toH1Function.grad_memVectorL2
  have hWg : MemVectorL2 W w.toH1Function.grad := w.toH1Function.grad_memVectorL2
  have hRg : MemVectorL2 W (u - w).toH1Function.grad :=
    (u - w).toH1Function.grad_memVectorL2
  have hb2 : MemLp b 2 (volume.restrict W) := hbL2
  have hRto2 : MemLp (u - w).toH1Function.toFun 2 (volume.restrict W) :=
    (u - w).toH1Function.memL2
  have hWto2 : MemLp w.toH1Function.toFun 2 (volume.restrict W) :=
    w.toH1Function.memL2
  have hRtoInt : IntegrableOn (fun x => (u - w).toH1Function.toFun x) W :=
    hRto2.integrable (by norm_num)
  have hWtoInt : IntegrableOn (fun x => w.toH1Function.toFun x) W :=
    hWto2.integrable (by norm_num)
  have hRtoSq : IntegrableOn (fun x => (u - w).toH1Function.toFun x ^ 2) W :=
    hRto2.integrable_sq
  have hWtoSq : IntegrableOn (fun x => w.toH1Function.toFun x ^ 2) W :=
    hWto2.integrable_sq
  have hRgSq : IntegrableOn (fun x => vecNormSq ((u - w).toH1Function.grad x)) W :=
    integrableOn_vecNormSq_of_memVectorL2 hRg
  have hWgSq : IntegrableOn (fun x => vecNormSq (w.toH1Function.grad x)) W :=
    integrableOn_vecNormSq_of_memVectorL2 hWg
  have hBU : MemVectorL2 W (fun x => matVecMul (scalarCoeffField b x)
      (u.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hUg
  have hBW : MemVectorL2 W (fun x => matVecMul (scalarCoeffField b x)
      (w.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hWg
  have hBR : MemVectorL2 W (fun x => matVecMul (scalarCoeffField b x)
      ((u - w).toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hRg
  have hBWm : MemVectorL2 W (fun x => (b x - 1) • w.toH1Function.grad x) := by
    have heq : (fun x => (b x - 1) • w.toH1Function.grad x) =
        fun x => matVecMul (scalarCoeffField b x) (w.toH1Function.grad x) -
          w.toH1Function.grad x := by
      funext x
      rw [hscalar x, sub_smul, one_smul]
    rw [heq]
    exact hBW.sub hWg
  have hEqU : ∀ phi : H10Function W,
      ∫ x in W, vecDot (matVecMul (scalarCoeffField b x) (u.toH1Function.grad x))
          (phi.toH1Function.grad x) ∂volume
        = ∫ x in W, b x * phi.toH1Function.toFun x ∂volume := by
    intro phi
    have h := hu phi
    simp_rw [← hscalar] at h
    simpa only [Pi.mul_apply, zero_mul, zero_add, mul_one, one_mul, add_zero] using h
  have hEqW : ∀ phi : H10Function W,
      ∫ x in W, vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume
        = ∫ x in W, phi.toH1Function.toFun x ∂volume := by
    intro phi
    have h := hw phi
    simpa only [Pi.mul_apply, zero_mul, zero_add, mul_one, one_mul, add_zero, one_smul] using h
  set X : ℝ := Real.sqrt (∫ x in W, vecNormSq ((u - w).toH1Function.grad x) ∂volume) with hXdef
  set Y : ℝ := Real.sqrt (∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume) with hYdef
  set Vol : ℝ := Real.sqrt ((volume W).toReal) with hVoldef
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact Real.sqrt_nonneg _
  have hVol0 : 0 ≤ Vol := by rw [hVoldef]; exact Real.sqrt_nonneg _
  have hYsq : Y * Y = ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume := by
    rw [hYdef, ← pow_two, Real.sq_sqrt (integral_nonneg fun x => vecNormSq_nonneg _)]
  have hXsq : X * X = ∫ x in W, vecNormSq ((u - w).toH1Function.grad x) ∂volume := by
    rw [hXdef, ← pow_two, Real.sq_sqrt (integral_nonneg fun x => vecNormSq_nonneg _)]
  have hYeq : ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume
      = ∫ x in W, w.toH1Function.toFun x ∂volume := by
    have h := hEqW w
    simp_rw [vecDot_self_eq_vecNormSq] at h
    exact h
  have hYbound : ∫ x in W, w.toH1Function.toFun x ∂volume ≤ Vol * (P * Y) := by
    have h1 := integral_le_vol_sqrt hW hWtoInt hWtoSq
    rw [← hVoldef] at h1
    have h2 : Real.sqrt (∫ x in W, w.toH1Function.toFun x ^ 2 ∂volume) ≤ P * Y := by
      have h := hPoincare w
      rw [← hYdef] at h
      exact h
    calc ∫ x in W, w.toH1Function.toFun x ∂volume
        ≤ Vol * Real.sqrt (∫ x in W, w.toH1Function.toFun x ^ 2 ∂volume) := h1
      _ ≤ Vol * (P * Y) := mul_le_mul_of_nonneg_left h2 hVol0
  have hYle : Y ≤ P * Vol := by
    rcases lt_or_eq_of_le hY0 with hYpos | hYz
    · have h : Y * Y ≤ P * Vol * Y := by
        rw [hYsq]
        calc ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume
            = ∫ x in W, w.toH1Function.toFun x ∂volume := hYeq
          _ ≤ Vol * (P * Y) := hYbound
          _ = P * Vol * Y := by ring
      exact le_of_mul_le_mul_right h hYpos
    · rw [← hYz]
      exact mul_nonneg hP hVol0
  have hB1 : |∫ x in W, (b x - 1) * (u - w).toH1Function.toFun x ∂volume|
      ≤ eps * Vol * (P * X) := by
    have hbm1 : MemLp (fun x => b x - 1) 2 (volume.restrict W) :=
      hb2.sub (memLp_const (1 : ℝ))
    have hBm1R : IntegrableOn (fun x => (b x - 1) * (u - w).toH1Function.toFun x) W := by
      have h := (hbm1.mul (r := 1) hRto2).integrable (by norm_num)
      simpa only [Pi.mul_def, IntegrableOn] using! h
    have habsint : ∫ x in W, |(u - w).toH1Function.toFun x| ∂volume
        ≤ Vol * Real.sqrt (∫ x in W, (u - w).toH1Function.toFun x ^ 2 ∂volume) := by
      have hf2abs : IntegrableOn (fun x => |(u - w).toH1Function.toFun x| ^ 2) W := by
        refine Integrable.congr hRtoSq ?_
        filter_upwards with x
        rw [abs_sq_eq_sq]
      have h0 := integral_le_vol_sqrt hW hRtoInt.abs hf2abs
      rw [← hVoldef] at h0
      have hsq2 : ∫ x in W, |(u - w).toH1Function.toFun x| ^ 2 ∂volume
          = ∫ x in W, (u - w).toH1Function.toFun x ^ 2 ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [abs_sq_eq_sq]
      rw [hsq2] at h0
      exact h0
    have h3 : Real.sqrt (∫ x in W, (u - w).toH1Function.toFun x ^ 2 ∂volume) ≤ P * X := by
      have h := hPoincare (u - w)
      rw [← hXdef] at h
      exact h
    calc |∫ x in W, (b x - 1) * (u - w).toH1Function.toFun x ∂volume|
        ≤ ∫ x in W, |(b x - 1) * (u - w).toH1Function.toFun x| ∂volume :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x in W, eps * |(u - w).toH1Function.toFun x| ∂volume := by
          apply setIntegral_mono_on hBm1R.abs (hRtoInt.abs.const_mul eps) hW
          intro x hx
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hcontrast x hx) (abs_nonneg _)
      _ = eps * ∫ x in W, |(u - w).toH1Function.toFun x| ∂volume := integral_const_mul _ _
      _ ≤ eps * (Vol * Real.sqrt (∫ x in W, (u - w).toH1Function.toFun x ^ 2 ∂volume)) :=
          mul_le_mul_of_nonneg_left habsint heps
      _ ≤ eps * (Vol * (P * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hVol0) heps
      _ = eps * Vol * (P * X) := by ring
  have hBWmSq : IntegrableOn (fun x => vecNormSq ((b x - 1) • w.toH1Function.grad x)) W :=
    integrableOn_vecNormSq_of_memVectorL2 hBWm
  have hsqrt : Real.sqrt (∫ x in W, vecNormSq ((b x - 1) • w.toH1Function.grad x) ∂volume)
      ≤ eps * Y := by
    have hmono : ∫ x in W, vecNormSq ((b x - 1) • w.toH1Function.grad x) ∂volume
        ≤ eps ^ 2 * ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on hBWmSq (hWgSq.const_mul (eps ^ 2)) hW
      intro x hx
      rw [vecNormSq_smul', ← abs_sq_eq_sq (b x - 1)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg (b x - 1)) (hcontrast x hx) 2) (vecNormSq_nonneg _)
    have h1 := Real.sqrt_le_sqrt hmono
    rw [Real.sqrt_mul (sq_nonneg eps), Real.sqrt_sq heps, ← hYdef] at h1
    exact h1
  have hB2 : |∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
        ((u - w).toH1Function.grad x) ∂volume|
      ≤ eps * Y * X := by
    have hcs := abs_integral_vecDot_le_sqrt_energy_mul_sqrt_energy hBWm hRg
    rw [← hXdef] at hcs
    calc |∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
            ((u - w).toH1Function.grad x) ∂volume|
        ≤ Real.sqrt (∫ x in W, vecNormSq ((b x - 1) • w.toH1Function.grad x) ∂volume) * X := hcs
      _ ≤ eps * Y * X := mul_le_mul_of_nonneg_right hsqrt hX0
  have hI1i : IntegrableOn (fun x => vecDot (matVecMul (scalarCoeffField b x)
        (u.toH1Function.grad x)) ((u - w).toH1Function.grad x)) W :=
    integrableOn_vecDot_of_memVectorL2 hBU hRg
  have hI2i : IntegrableOn (fun x => vecDot (matVecMul (scalarCoeffField b x)
        (w.toH1Function.grad x)) ((u - w).toH1Function.grad x)) W :=
    integrableOn_vecDot_of_memVectorL2 hBW hRg
  have h2i : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        ((u - w).toH1Function.grad x)) W :=
    integrableOn_vecDot_of_memVectorL2 hWg hRg
  have hI3i : IntegrableOn (fun x => vecDot ((b x - 1) • w.toH1Function.grad x)
        ((u - w).toH1Function.grad x)) W := by
    have heq : (fun x => vecDot ((b x - 1) • w.toH1Function.grad x)
          ((u - w).toH1Function.grad x)) =
        fun x => vecDot (matVecMul (scalarCoeffField b x) (w.toH1Function.grad x) -
          w.toH1Function.grad x) ((u - w).toH1Function.grad x) := by
      funext x
      rw [hscalar x, sub_smul, one_smul]
    have heq2 : (fun x => vecDot (matVecMul (scalarCoeffField b x) (w.toH1Function.grad x) -
          w.toH1Function.grad x) ((u - w).toH1Function.grad x)) =
        fun x => vecDot (matVecMul (scalarCoeffField b x) (w.toH1Function.grad x))
            ((u - w).toH1Function.grad x) -
          vecDot (w.toH1Function.grad x) ((u - w).toH1Function.grad x) := by
      funext x
      rw [vecDot_sub_left']
    rw [heq, heq2]
    exact Integrable.sub hI2i h2i
  have hBtoR : IntegrableOn (fun x => b x * (u - w).toH1Function.toFun x) W := by
    have h := (hb2.mul (r := 1) hRto2).integrable (by norm_num)
    simpa only [Pi.mul_def, IntegrableOn] using! h
  have hAeq : ∫ x in W, (b x - 1) * (u - w).toH1Function.toFun x ∂volume
      = (∫ x in W, b x * (u - w).toH1Function.toFun x ∂volume
          - ∫ x in W, (u - w).toH1Function.toFun x ∂volume) := by
    rw [← integral_sub hBtoR hRtoInt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hI2eq : ∫ x in W, vecDot (matVecMul (scalarCoeffField b x) (w.toH1Function.grad x))
        ((u - w).toH1Function.grad x) ∂volume
      = ∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
          ((u - w).toH1Function.grad x) ∂volume
        + ∫ x in W, (u - w).toH1Function.toFun x ∂volume := by
    calc ∫ x in W, vecDot (matVecMul (scalarCoeffField b x) (w.toH1Function.grad x))
          ((u - w).toH1Function.grad x) ∂volume
        = ∫ x in W, (vecDot ((b x - 1) • w.toH1Function.grad x)
            ((u - w).toH1Function.grad x)
            + vecDot (w.toH1Function.grad x) ((u - w).toH1Function.grad x)) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hscalar x, vecDot_smul_left, vecDot_smul_left]
          ring
      _ = (∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
            ((u - w).toH1Function.grad x) ∂volume)
          + ∫ x in W, vecDot (w.toH1Function.grad x)
            ((u - w).toH1Function.grad x) ∂volume := integral_add hI3i h2i
      _ = (∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
            ((u - w).toH1Function.grad x) ∂volume)
          + ∫ x in W, (u - w).toH1Function.toFun x ∂volume := by
          rw [hEqW (u - w)]
  have hid : ∫ x in W, b x * vecNormSq ((u - w).toH1Function.grad x) ∂volume
      = ∫ x in W, (b x - 1) * (u - w).toH1Function.toFun x ∂volume
        - ∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
          ((u - w).toH1Function.grad x) ∂volume := by
    calc ∫ x in W, b x * vecNormSq ((u - w).toH1Function.grad x) ∂volume
        = ∫ x in W, (vecDot (matVecMul (scalarCoeffField b x) (u.toH1Function.grad x))
            ((u - w).toH1Function.grad x)
            - vecDot (matVecMul (scalarCoeffField b x) (w.toH1Function.grad x))
            ((u - w).toH1Function.grad x)) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hgradR x, hscalar x, hscalar x]
          exact fluxSplit (u.toH1Function.grad x) (w.toH1Function.grad x) (b x)
      _ = (∫ x in W, vecDot (matVecMul (scalarCoeffField b x) (u.toH1Function.grad x))
            ((u - w).toH1Function.grad x) ∂volume)
          - ∫ x in W, vecDot (matVecMul (scalarCoeffField b x) (w.toH1Function.grad x))
            ((u - w).toH1Function.grad x) ∂volume := integral_sub hI1i hI2i
      _ = (∫ x in W, b x * (u - w).toH1Function.toFun x ∂volume)
          - (∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
            ((u - w).toH1Function.grad x) ∂volume
            + ∫ x in W, (u - w).toH1Function.toFun x ∂volume) := by
          rw [hEqU (u - w), hI2eq]
      _ = (∫ x in W, b x * (u - w).toH1Function.toFun x ∂volume
            - ∫ x in W, (u - w).toH1Function.toFun x ∂volume)
          - ∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
            ((u - w).toH1Function.grad x) ∂volume := by ring
      _ = ∫ x in W, (b x - 1) * (u - w).toH1Function.toFun x ∂volume
          - ∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
            ((u - w).toH1Function.grad x) ∂volume := by rw [hAeq]
  have hcoerc : (∫ x in W, vecNormSq ((u - w).toH1Function.grad x) ∂volume) / 2
      ≤ ∫ x in W, b x * vecNormSq ((u - w).toH1Function.grad x) ∂volume := by
    have hleft : IntegrableOn (fun x => (1 / 2 : ℝ) *
        vecNormSq ((u - w).toH1Function.grad x)) W := hRgSq.const_mul _
    have hright : IntegrableOn (fun x => vecDot ((u - w).toH1Function.grad x)
        (matVecMul (scalarCoeffField b x) ((u - w).toH1Function.grad x))) W :=
      integrableOn_vecDot_of_memVectorL2 hRg hBR
    have hc := setIntegral_mono_on hleft hright hW
      (fun x hx => (hEll.2 x hx).2.2.1 ((u - w).toH1Function.grad x))
    calc (∫ x in W, vecNormSq ((u - w).toH1Function.grad x) ∂volume) / 2
        = ∫ x in W, (1 / 2 : ℝ) * vecNormSq ((u - w).toH1Function.grad x) ∂volume := by
          rw [integral_const_mul]; ring
      _ ≤ ∫ x in W, vecDot ((u - w).toH1Function.grad x)
            (matVecMul (scalarCoeffField b x) ((u - w).toH1Function.grad x)) ∂volume := hc
      _ = ∫ x in W, b x * vecNormSq ((u - w).toH1Function.grad x) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hscalar x, vecDot_smul_right', vecDot_self_eq_vecNormSq]
  have hmid : ∫ x in W, b x * vecNormSq ((u - w).toH1Function.grad x) ∂volume
      ≤ |∫ x in W, (b x - 1) * (u - w).toH1Function.toFun x ∂volume|
        + |∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
          ((u - w).toH1Function.grad x) ∂volume| := by
    rw [hid]
    linarith [le_abs_self (∫ x in W, (b x - 1) * (u - w).toH1Function.toFun x ∂volume),
      neg_le_abs (∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
        ((u - w).toH1Function.grad x) ∂volume)]
  have hcomb : X * X / 2 ≤ 2 * eps * P * Vol * X := by
    calc X * X / 2 = (∫ x in W, vecNormSq ((u - w).toH1Function.grad x) ∂volume) / 2 := by
          rw [hXsq]
      _ ≤ ∫ x in W, b x * vecNormSq ((u - w).toH1Function.grad x) ∂volume := hcoerc
      _ ≤ |∫ x in W, (b x - 1) * (u - w).toH1Function.toFun x ∂volume|
            + |∫ x in W, vecDot ((b x - 1) • w.toH1Function.grad x)
            ((u - w).toH1Function.grad x) ∂volume| := hmid
      _ ≤ eps * Vol * (P * X) + eps * Y * X := by linarith [hB1, hB2]
      _ ≤ eps * Vol * (P * X) + eps * (P * Vol) * X := by
          refine add_le_add (le_refl _) ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYle heps) hX0
      _ = 2 * eps * P * Vol * X := by ring
  have hXsq4 : X * X ≤ 4 * eps * P * Vol * X := by
    have h6 : X * X = 2 * (X * X / 2) := by ring
    calc X * X = 2 * (X * X / 2) := h6
      _ ≤ 2 * (2 * eps * P * Vol * X) := mul_le_mul_of_nonneg_left hcomb (by norm_num)
      _ = 4 * eps * P * Vol * X := by ring
  by_cases hXz : X = 0
  · have hPu := hPoincare (u - w)
    rw [← hXdef] at hPu
    rw [hXz, mul_zero] at hPu
    have hL : Real.sqrt (∫ x in W, ((u - w).toH1Function.toFun x) ^ 2 ∂volume) = 0 :=
      le_antisymm hPu (Real.sqrt_nonneg _)
    rw [hL]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg P)) heps)
      hVol0
  · have hXpos : 0 < X := lt_of_le_of_ne hX0 (Ne.symm hXz)
    have hXle : X ≤ 4 * eps * P * Vol := le_of_mul_le_mul_right hXsq4 hXpos
    have hPu := hPoincare (u - w)
    rw [← hXdef] at hPu
    calc Real.sqrt (∫ x in W, ((u - w).toH1Function.toFun x) ^ 2 ∂volume) ≤ P * X := hPu
      _ ≤ P * (4 * eps * P * Vol) := mul_le_mul_of_nonneg_left hXle hP
      _ = 4 * P ^ 2 * eps * Vol := by ring
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
