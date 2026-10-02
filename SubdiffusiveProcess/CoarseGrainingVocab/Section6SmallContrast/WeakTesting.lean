import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.HarmonicReplacement
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.IntegratedCoercivity
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.EnergyArithmetic
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities

/-!
# Weak testing for the small-contrast harmonic comparison

This file supplies the measure-theoretic part of `e.harmapprox.Schauder`.
The project's bare `CoeffField` is only a function type, so the standard
`IsEllipticFieldOn` certificate is retained to carry measurability and local
`L²` flux integrability.  All quantitative constants below come exclusively
from the operator-norm distance to the identity.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory Homogenization Homogenization.Book.Ch02
open Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

/-- Squared Euclidean magnitude is integrable for a vector `L²` field. -/
theorem integrableOn_vecNormSq_of_memVectorL2
    {W : Set (Vec d)} {F : Vec d → Vec d} (hF : MemVectorL2 W F) :
    IntegrableOn (fun x => vecNormSq (F x)) W := by
  simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF hF

private theorem memLp_euclideanNorm_of_memVectorL2
    {W : Set (Vec d)} {F : Vec d → Vec d} (hF : MemVectorL2 W F) :
    MemLp (fun x => euclideanNorm (F x)) 2 (volume.restrict W) := by
  have hh := (memHilbertVectorL2_hilbertifyVecField hF).norm
  simpa [hilbertifyVecField, euclideanNorm_eq_norm_ofVec] using hh

private theorem vecNorm_eq_euclideanNorm (v : Vec d) :
    vecNorm v = euclideanNorm v := by
  rw [← sq_eq_sq₀ (vecNorm_nonneg v) (euclideanNorm_nonneg v),
    vecNorm_sq_eq_vecNormSq, euclideanNorm_sq]

/-- Euclidean Cauchy--Schwarz for two vector `L²` fields, expressed in the
square-energy language used by the harmonic comparison. -/
theorem abs_integral_vecDot_le_sqrt_energy_mul_sqrt_energy
    {W : Set (Vec d)} {F G : Vec d → Vec d}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) :
    |∫ x in W, vecDot (F x) (G x) ∂volume| ≤
      Real.sqrt (∫ x in W, vecNormSq (F x) ∂volume) *
        Real.sqrt (∫ x in W, vecNormSq (G x) ∂volume) := by
  let X : Vec d → ℝ := fun x => euclideanNorm (F x)
  let Y : Vec d → ℝ := fun x => euclideanNorm (G x)
  have hX : MemLp X 2 (volume.restrict W) := by
    simpa [X] using memLp_euclideanNorm_of_memVectorL2 hF
  have hY : MemLp Y 2 (volume.restrict W) := by
    simpa [Y] using memLp_euclideanNorm_of_memVectorL2 hG
  have hdot : IntegrableOn (fun x => vecDot (F x) (G x)) W :=
    integrableOn_vecDot_of_memVectorL2 hF hG
  have hXY : IntegrableOn (fun x => X x * Y x) W := by
    have hmem : MemLp (fun x => X x * Y x) 1 (volume.restrict W) := by
      have h := hY.mul (r := 1) hX
      simpa only [Pi.mul_apply] using h
    exact hmem.integrable (by norm_num)
  have habs :
      |∫ x in W, vecDot (F x) (G x) ∂volume| ≤
        ∫ x in W, X x * Y x ∂volume := by
    calc
      |∫ x in W, vecDot (F x) (G x) ∂volume| ≤
          ∫ x in W, |vecDot (F x) (G x)| ∂volume := abs_integral_le_integral_abs
      _ ≤ ∫ x in W, X x * Y x ∂volume := by
        apply setIntegral_mono_ae hdot.abs hXY
        filter_upwards with x
        simpa [X, Y, ← vecNorm_eq_euclideanNorm] using
          abs_vecDot_le_vecNorm_mul_vecNorm (F x) (G x)
  have hcs :=
    integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      (μ := volume.restrict W)
      hX.integrable_sq hY.integrable_sq
      (Filter.Eventually.of_forall fun x => euclideanNorm_nonneg (F x))
      (Filter.Eventually.of_forall fun x => euclideanNorm_nonneg (G x))
  have hXsq : (fun x => X x ^ 2) = fun x => vecNormSq (F x) := by
    funext x
    dsimp [X]
    rw [euclideanNorm_sq]
  have hYsq : (fun x => Y x ^ 2) = fun x => vecNormSq (G x) := by
    funext x
    dsimp [Y]
    rw [euclideanNorm_sq]
  rw [hXsq, hYsq] at hcs
  exact habs.trans hcs

/-- The perturbation field `(a-Id)H` has the sharp `delta` energy bound. -/
theorem integral_vecNormSq_coefficientSubIdentity_mul_le
    {W : Set (Vec d)} {a : CoeffField d} {H : Vec d → Vec d}
    {lam Lam delta : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W a)
    (ha : CoefficientIdentityDistanceLE W a delta)
    (hH : MemVectorL2 W H) :
    ∫ x in W, vecNormSq (matVecMul (a x - 1) (H x)) ∂volume ≤
      delta ^ 2 * ∫ x in W, vecNormSq (H x) ∂volume := by
  let P : Vec d → Vec d := fun x => matVecMul (a x - 1) (H x)
  have haH : MemVectorL2 W (fun x => matVecMul (a x) (H x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hH
  have hP : MemVectorL2 W P := by
    have heq : P = fun x => matVecMul (a x) (H x) - H x := by
      funext x
      classical
      dsimp [P]
      change (a x - 1).mulVec (H x) = (a x).mulVec (H x) - H x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [heq]
    exact haH.sub hH
  have hleft := integrableOn_vecNormSq_of_memVectorL2 hP
  have hright :=
    (integrableOn_vecNormSq_of_memVectorL2 hH).const_mul (delta ^ 2)
  calc
    ∫ x in W, vecNormSq (matVecMul (a x - 1) (H x)) ∂volume =
        ∫ x in W, vecNormSq (P x) ∂volume := rfl
    _ ≤ ∫ x in W, delta ^ 2 * vecNormSq (H x) ∂volume := by
      apply integral_mono_ae hleft hright
      filter_upwards [ha] with x hx
      exact (vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
        (a x - 1) (H x)).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
            (matrixOperatorNorm_nonneg (a x - 1)) hx 2) (vecNormSq_nonneg (H x)))
    _ = delta ^ 2 * ∫ x in W, vecNormSq (H x) ∂volume :=
      integral_const_mul _ _

/-- Square-root version of the sharp perturbation-field estimate. -/
theorem sqrt_integral_vecNormSq_coefficientSubIdentity_mul_le
    {W : Set (Vec d)} {a : CoeffField d} {H : Vec d → Vec d}
    {lam Lam delta : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W a)
    (ha : CoefficientIdentityDistanceLE W a delta)
    (hdelta : 0 ≤ delta) (hH : MemVectorL2 W H) :
    Real.sqrt (∫ x in W, vecNormSq (matVecMul (a x - 1) (H x)) ∂volume) ≤
      delta * Real.sqrt (∫ x in W, vecNormSq (H x) ∂volume) := by
  have h := Real.sqrt_le_sqrt
    (integral_vecNormSq_coefficientSubIdentity_mul_le hEll ha hH)
  rw [Real.sqrt_mul (sq_nonneg delta), Real.sqrt_sq hdelta] at h
  exact h

private theorem integral_vecDot_sub_left
    {W : Set (Vec d)} {F G H : Vec d → Vec d}
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G)
    (hH : MemVectorL2 W H) :
    ∫ x in W, vecDot (F x - G x) (H x) ∂volume =
      (∫ x in W, vecDot (F x) (H x) ∂volume) -
        ∫ x in W, vecDot (G x) (H x) ∂volume := by
  have hFH := integrableOn_vecDot_of_memVectorL2 hF hH
  have hGH := integrableOn_vecDot_of_memVectorL2 hG hH
  have heq : (fun x => vecDot (F x - G x) (H x)) =
      fun x => vecDot (F x) (H x) - vecDot (G x) (H x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  rw [heq, integral_sub hFH hGH]

/-- The fully tested harmonic comparison on an arbitrary finite window.  The
zero-trace witness is retained explicitly so no boundary equality is hidden. -/
theorem harmonicComparison_gradientEnergy
    {W : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    {a : CoeffField d} {u h : H1Function W} {rho : H10Function W}
    {f : Vec d → Vec d} {lam Lam delta alpha : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W a)
    (ha : CoefficientIdentityDistanceLE W a delta)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hu : IsMatrixDivFormWeakSolutionOn a W u f)
    (hf : MemVectorL2 W f)
    (hh : SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.IsUnitWeaklyHarmonicOn W h)
    (hgrad : ∀ x, h.grad x = u.grad x + rho.toH1Function.grad x) :
    Real.sqrt (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume) ≤
      2 * delta * Real.sqrt (∫ x in W, vecNormSq (h.grad x) ∂volume) +
        2 * Real.sqrt (∫ x in W, vecNormSq (f x) ∂volume) := by
  let R : Vec d → Vec d := fun x => rho.toH1Function.grad x
  let H : Vec d → Vec d := fun x => h.grad x
  let U : Vec d → Vec d := fun x => u.grad x
  let P : Vec d → Vec d := fun x => matVecMul (a x - 1) (H x)
  have hR : MemVectorL2 W R := by
    simpa [R] using rho.toH1Function.grad_memVectorL2
  have hH : MemVectorL2 W H := by
    simpa [H] using h.grad_memVectorL2
  have hU : MemVectorL2 W U := by
    simpa [U] using u.grad_memVectorL2
  have haR : MemVectorL2 W (fun x => matVecMul (a x) (R x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hR
  have haH : MemVectorL2 W (fun x => matVecMul (a x) (H x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hH
  have hP : MemVectorL2 W P := by
    have heq : P = fun x => matVecMul (a x) (H x) - H x := by
      funext x
      classical
      dsimp [P]
      change (a x - 1).mulVec (H x) = (a x).mulVec (H x) - H x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [heq]
    exact haH.sub hH
  let E : ℝ := ∫ x in W, vecNormSq (R x) ∂volume
  let HH : ℝ := ∫ x in W, vecNormSq (H x) ∂volume
  let FF : ℝ := ∫ x in W, vecNormSq (f x) ∂volume
  let I : ℝ := ∫ x in W, vecDot (R x) (matVecMul (a x) (R x)) ∂volume
  let perturb : ℝ := ∫ x in W, vecDot (P x) (R x) ∂volume
  let forcing : ℝ := ∫ x in W, vecDot (f x) (R x) ∂volume
  have hE0 : 0 ≤ E := by
    exact integral_nonneg fun x => vecNormSq_nonneg (R x)
  have hHH0 : 0 ≤ HH := by
    exact integral_nonneg fun x => vecNormSq_nonneg (H x)
  have hFF0 : 0 ≤ FF := by
    exact integral_nonneg fun x => vecNormSq_nonneg (f x)
  have hcoercive : E / 2 ≤ I := by
    have haThreshold :
        CoefficientIdentityDistanceLE W a (smallContrastThreshold d alpha) := by
      filter_upwards [ha] with x hx
      exact hx.trans hdelta
    have hleft : IntegrableOn (fun x => (1 / 2 : ℝ) * vecNormSq (R x)) W :=
      (integrableOn_vecNormSq_of_memVectorL2 hR).const_mul _
    have hright : IntegrableOn
        (fun x => vecDot (R x) (matVecMul (a x) (R x))) W :=
      integrableOn_vecDot_of_memVectorL2 hR haR
    have hc := integral_half_vecNormSq_le_coefficientEnergy
      halpha0 halpha1 haThreshold hleft hright
    dsimp [E, I]
    calc
      (∫ x in W, vecNormSq (R x) ∂volume) / 2 =
          ∫ x in W, (1 / 2 : ℝ) * vecNormSq (R x) ∂volume := by
        rw [integral_const_mul]
        ring
      _ ≤ ∫ x in W, vecDot (R x) (matVecMul (a x) (R x)) ∂volume := hc
  have hunit : ∫ x in W, vecDot (H x) (R x) ∂volume = 0 := by
    simpa [H, R] using hh rho
  have hweak := hu rho
  have hUeq : ∀ x, U x = H x - R x := by
    intro x
    dsimp [U, H, R]
    exact (eq_sub_iff_add_eq).2 (hgrad x).symm
  have hsplitA :
      ∫ x in W, vecDot (matVecMul (a x) (U x)) (R x) ∂volume =
        (∫ x in W, vecDot (matVecMul (a x) (H x)) (R x) ∂volume) - I := by
    calc
      ∫ x in W, vecDot (matVecMul (a x) (U x)) (R x) ∂volume =
          ∫ x in W,
            vecDot (matVecMul (a x) (H x) - matVecMul (a x) (R x)) (R x)
              ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hUeq x]
        exact congrArg (fun v => vecDot v (R x))
          (Matrix.mulVec_sub (a x) (H x) (R x))
      _ = (∫ x in W, vecDot (matVecMul (a x) (H x)) (R x) ∂volume) - I := by
        have hbase := integral_vecDot_sub_left haH haR hR
        have hcomm :
            ∫ x in W, vecDot (matVecMul (a x) (R x)) (R x) ∂volume = I := by
          dsimp [I]
          apply integral_congr_ae
          filter_upwards with x
          exact vecDot_comm _ _
        rw [hcomm] at hbase
        exact hbase
  have hsplitPerturb :
      ∫ x in W, vecDot (matVecMul (a x) (H x)) (R x) ∂volume = perturb := by
    have hHR := integrableOn_vecDot_of_memVectorL2 hH hR
    have hPR := integrableOn_vecDot_of_memVectorL2 hP hR
    have hadd :
        ∫ x in W, vecDot (H x + P x) (R x) ∂volume =
          (∫ x in W, vecDot (H x) (R x) ∂volume) +
            ∫ x in W, vecDot (P x) (R x) ∂volume := by
      have hfun : (fun x => vecDot (H x + P x) (R x)) =
          fun x => vecDot (H x) (R x) + vecDot (P x) (R x) := by
        funext x
        rw [vecDot_add_left]
      rw [hfun, integral_add hHR hPR]
    calc
      ∫ x in W, vecDot (matVecMul (a x) (H x)) (R x) ∂volume =
          ∫ x in W, vecDot (H x + P x) (R x) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        apply congrArg (fun v => vecDot v (R x))
        classical
        dsimp [P]
        change (a x).mulVec (H x) = H x + (a x - 1).mulVec (H x)
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      _ = perturb := by
        rw [hadd, hunit, zero_add]
  have hidentity : I = -(-perturb) - (-forcing) := by
    have hw :
        ∫ x in W, vecDot (matVecMul (a x) (U x)) (R x) ∂volume = -forcing := by
      simpa [U, R, forcing] using hweak
    rw [hsplitA, hsplitPerturb] at hw
    linarith
  have hperturb : |-perturb| ≤ delta * Real.sqrt E * Real.sqrt HH := by
    rw [abs_neg]
    have hcs := abs_integral_vecDot_le_sqrt_energy_mul_sqrt_energy hP hR
    have hPbound := sqrt_integral_vecNormSq_coefficientSubIdentity_mul_le
      hEll ha hdelta0 hH
    dsimp [perturb, P, R, H, E, HH] at hcs hPbound ⊢
    calc
      _ ≤ (delta * Real.sqrt (∫ x in W, vecNormSq (h.grad x) ∂volume)) *
          Real.sqrt (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume) :=
        hcs.trans (mul_le_mul_of_nonneg_right hPbound (Real.sqrt_nonneg _))
      _ = delta * Real.sqrt (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume) *
          Real.sqrt (∫ x in W, vecNormSq (h.grad x) ∂volume) := by ring
  have hforcing : |-forcing| ≤ Real.sqrt FF * Real.sqrt E := by
    rw [abs_neg]
    have hcs := abs_integral_vecDot_le_sqrt_energy_mul_sqrt_energy hf hR
    simpa [forcing, FF, E, R, mul_comm] using hcs
  have hmain := harmonicComparison_energy hE0 hHH0 hFF0 hdelta0
    hcoercive hidentity hperturb hforcing
  simpa [E, HH, FF, R, H] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
