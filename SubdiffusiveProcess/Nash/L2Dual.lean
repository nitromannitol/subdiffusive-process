module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- Finite-measure set tests characterize an essential bound on a sigma-finite space. -/
theorem eLpNorm_top_le_of_setIntegral {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [SigmaFinite mu] (f : Lp ℝ 2 mu) (A : ℝ)
    (h : ∀ s, MeasurableSet s → mu s < ∞ → |∫ x in s, f x ∂mu| ≤ A * mu.real s) :
    eLpNorm (f : X → ℝ) ∞ mu ≤ ENNReal.ofReal A := by
  have hloc (s : Set X) (hs : mu s < ∞) : IntegrableOn (f : X → ℝ) s mu :=
    integrableOn_Lp_of_measure_ne_top f (by norm_num) hs.ne
  have hupper : ∀ᵐ x ∂mu, 0 ≤ A - f x :=
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun s _ hs => (integrableOn_const (C := A) hs.ne).sub (hloc s hs)) (fun s hs hms => by
        rw [integral_sub (integrableOn_const (C := A) hms.ne) (hloc s hms), setIntegral_const,
          smul_eq_mul, mul_comm (mu.real s)]
        linarith [le_abs_self (∫ x in s, f x ∂mu), h s hs hms])
  have hlower : ∀ᵐ x ∂mu, 0 ≤ A + f x :=
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun s _ hs => (integrableOn_const (C := A) hs.ne).add (hloc s hs)) (fun s hs hms => by
        rw [integral_add (integrableOn_const (C := A) hms.ne) (hloc s hms), setIntegral_const,
          smul_eq_mul, mul_comm (mu.real s)]
        linarith [neg_abs_le (∫ x in s, f x ∂mu), h s hs hms])
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [hupper, hlower] with x hx hy
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Symmetry turns an L1-to-L2 estimate into the corresponding L2-to-L∞ estimate. -/
theorem symmetric_L2_top_bound {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [SigmaFinite mu] (T : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (M : ℝ) 
    (hsym : ∀ f g, ⟪T f, g⟫ = ⟪f, T g⟫)
    (h12 : ∀ g : Lp ℝ 2 mu, Integrable (g : X → ℝ) mu →
      ‖T g‖ ≤ M * (eLpNorm (g : X → ℝ) 1 mu).toReal) (f : Lp ℝ 2 mu) :
    eLpNorm (T f : X → ℝ) ∞ mu ≤ ENNReal.ofReal (M * ‖f‖) := by
  apply eLpNorm_top_le_of_setIntegral mu (T f) (M * ‖f‖)
  intro s hs hms
  let g : Lp ℝ 2 mu := indicatorConstLp 2 hs hms.ne 1
  have hgEq : (g : X → ℝ) =ᵐ[mu] s.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
  have hg1 : eLpNorm (g : X → ℝ) 1 mu = mu s := by
    rw [eLpNorm_congr_ae hgEq, eLpNorm_indicator_const hs.nullMeasurableSet (by norm_num) (by norm_num)]
    simp
  have hgI : Integrable (g : X → ℝ) mu :=
    memLp_one_iff_integrable.mp (by
      change eLpNorm (g : X → ℝ) 1 mu < ∞
      rw [hg1]
      exact hms)
  calc
    _ = |⟪T f, g⟫| := by rw [real_inner_comm, L2.inner_indicatorConstLp_one hs hms.ne]
    _ = |⟪f, T g⟫| := congrArg abs (hsym f g)
    _ ≤ ‖f‖ * ‖T g‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * (M * (eLpNorm (g : X → ℝ) 1 mu).toReal) :=
      mul_le_mul_of_nonneg_left (h12 g hgI) (norm_nonneg f)
    _ = M * ‖f‖ * mu.real s := by rw [hg1, measureReal_def]; ring

end SubdiffusiveProcess.Nash
