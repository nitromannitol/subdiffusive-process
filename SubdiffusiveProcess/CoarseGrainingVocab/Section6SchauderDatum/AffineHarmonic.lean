import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.MaxPrinciple
import Homogenization.Sobolev.Foundations.MeanZero

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitLift.lean
-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitHarmonic.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitLift.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitHarmonic.lean

/-!
# Affine functions are weakly harmonic, and harmonicity is closed under differences

The datum split's competitor `V_odd = v - ℓ_h - v₁` is weakly harmonic because each
of its three summands is: `v` and `v₁` by construction, and the affine lift `ℓ_h`
because its weak gradient is constant.

The constant-gradient case rests on the **weak divergence theorem for `H¹₀`**
(`integral_grad_coord_h10_eq_zero`): each coordinate of the weak gradient of a
zero-trace function integrates to zero.  Its proof tests the weak-gradient
identity of the *constant* `H¹` function against the smooth compactly supported
approximants of the test function and passes to the limit through their `L²`
convergence on the finite-measure window.

`affineLiftH1` is the `H¹` realization of `Section6ExcessDecay.affineLift` on a
Sobolev-regular domain; `affineLiftH1_toFun` identifies the two pointwise, so the
zero-trace supplier of `ZeroTrace` reads it directly.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open Homogenization MeasureTheory Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay (affineLift)

noncomputable section

variable {d : ℕ}

/-- The dot product is additive on the right. -/
private theorem vecDot_sub_right (A B C : Vec d) :
    vecDot A (B - C) = vecDot A B - vecDot A C := by
  simp only [vecDot, Pi.sub_apply]
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The `H¹` realization of the affine lift on a Sobolev-regular domain. -/
def affineLiftH1 {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (x : Vec d) (c : ℝ) (A : Vec d) :
    H1Function U :=
  (H1Function.affineOnIsSobolevRegularDomain hU A).addConst (c - vecDot A x)

@[simp] theorem affineLiftH1_toFun {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsSobolevRegularDomain U)
    (x : Vec d) (c : ℝ) (A : Vec d) :
    (affineLiftH1 hU x c A).toFun = affineLift x c A := by
  funext y
  rw [affineLift, affineLiftH1]
  show (H1Function.affineOnIsSobolevRegularDomain hU A) y + (c - vecDot A x) = _
  rw [H1Function.affineOnIsSobolevRegularDomain_apply, vecDot_sub_right]
  show (∑ i : Fin d, A i * y i) + (c - vecDot A x) = c + (vecDot A y - vecDot A x)
  rw [show vecDot A y = ∑ i : Fin d, A i * y i from rfl]
  ring

@[simp] theorem affineLiftH1_grad {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsSobolevRegularDomain U)
    (x : Vec d) (c : ℝ) (A : Vec d) (y : Vec d) :
    (affineLiftH1 hU x c A).grad y = A := by
  rw [affineLiftH1, H1Function.grad_addConst,
    H1Function.affineOnIsSobolevRegularDomain_grad]

/-- Gradient coordinates of an `H¹` function are integrable on the domain. -/
theorem integrableOn_grad_coord {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (u : H1Function U) (i : Fin d) :
    IntegrableOn (fun y => u.grad y i) U volume := by
  simpa [IntegrableOn, volumeMeasureOn] using
    (u.gradMemL2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)

/-! ## 1. The weak divergence theorem for `H¹₀` -/

private theorem integrable_approx_deriv {U : Set (Vec d)} (φ : H10Function U)
    (n : ℕ) (i : Fin d) :
    Integrable (fun y => (fderiv ℝ (φ.approx n) y) (basisVec i))
      (volume.restrict U) := by
  have hcont : Continuous fun y => (fderiv ℝ (φ.approx n) y) (basisVec i) :=
    ((φ.approx_smooth n).continuous_fderiv (by exact_mod_cast le_top)).clm_apply
      continuous_const
  have hcs0 : HasCompactSupport (fderiv ℝ (φ.approx n)) :=
    (φ.approx_hasCompactSupport n).fderiv ℝ
  have hcs : HasCompactSupport fun y => (fderiv ℝ (φ.approx n) y) (basisVec i) := by
    refine HasCompactSupport.intro hcs0 fun y hy => ?_
    rw [image_eq_zero_of_notMem_tsupport hy]
    rfl
  exact (hcont.integrable_of_hasCompactSupport hcs).restrict

/-- **The weak divergence theorem for `H¹₀`.**  Each coordinate of the weak
gradient of a zero-trace function integrates to zero over the domain.

The proof tests the weak-gradient identity of the *constant* `H¹` function
against the smooth compactly supported approximants of `φ`, and passes to the
limit through the `L²` convergence of the approximate gradients (the
`H10Function` package's `tendsto_approx_grad`) on the finite-measure window. -/
theorem integral_grad_coord_h10_eq_zero {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (φ : H10Function U) (i : Fin d) :
    ∫ y in U, φ.toH1Function.grad y i ∂volume = 0 := by
  set f : Vec d → ℝ := fun y => φ.toH1Function.grad y i with hfdef
  set F : ℕ → Vec d → ℝ := fun n y => (fderiv ℝ (φ.approx n) y) (basisVec i) with hFdef
  have hzero : ∀ n, ∫ y in U, F n y ∂volume = 0 := by
    intro n
    have hw := (H1Function.const (U := U) (1 : ℝ)).hasWeakGradient i
      (φ.approx n) (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
      (φ.approx_support_subset n)
    simpa [hFdef] using hw
  have hfi : Integrable f (volume.restrict U) := by
    simpa [hfdef, IntegrableOn, volumeMeasureOn] using
      integrableOn_grad_coord (U := U) φ.toH1Function i
  have hFi : ∀ n, Integrable (F n) (volume.restrict U) := fun n =>
    integrable_approx_deriv φ n i
  have hmeas : ∀ n, AEStronglyMeasurable (fun y => F n y - f y) (volume.restrict U) :=
    fun n => (hFi n).1.sub hfi.1
  set cst : ENNReal :=
    ((volume.restrict U) Set.univ) ^
      (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) with hcstdef
  have huniv : (volume.restrict U) Set.univ ≠ ⊤ := measure_ne_top _ _
  have hcoef : cst ≠ ⊤ := by
    rw [hcstdef]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) huniv
  have hbound : ∀ n, ∫⁻ y, ‖F n y - f y‖ₑ ∂(volume.restrict U) ≤
      eLpNorm (fun y => F n y - f y) 2 (volume.restrict U) * cst := by
    intro n
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := (1 : ENNReal)) (q := (2 : ENNReal)) (μ := volume.restrict U)
      (f := fun y => F n y - f y) (by norm_num) (hmeas n)
    rwa [eLpNorm_one_eq_lintegral_enorm] at h
  have hgrad := φ.tendsto_approx_grad i
  have hmul : Tendsto (fun n =>
      eLpNorm (fun y => F n y - f y) 2 (volume.restrict U) * cst) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hgrad (Or.inr hcoef)
    rw [zero_mul] at h
    exact h
  have hL1 : Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ ∂(volume.restrict U)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
      (fun n => zero_le _) hbound
  have htend := tendsto_integral_of_L1 (μ := volume.restrict U) f hfi
    (Eventually.of_forall hFi) hL1
  have hconst : Tendsto (fun n => ∫ y in U, F n y ∂volume) atTop (𝓝 (0 : ℝ)) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique hconst htend).symm

/-! ## 2. Affine functions are weakly harmonic -/

/-- An `H¹` function with constant weak gradient is weakly harmonic: the tested
integral is a finite combination of the vanishing gradient integrals of the test
function. -/
theorem isUnitWeaklyHarmonicOn_of_grad_const {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] {u : H1Function V} {A : Vec d}
    (hgrad : ∀ y, u.grad y = A) : IsUnitWeaklyHarmonicOn V u := by
  intro φ
  have hint : ∀ i : Fin d,
      Integrable (fun y => A i * φ.toH1Function.grad y i) (volume.restrict V) := by
    intro i
    have h : Integrable (fun y => φ.toH1Function.grad y i) (volume.restrict V) := by
      simpa [IntegrableOn, volumeMeasureOn] using
        integrableOn_grad_coord (U := V) φ.toH1Function i
    exact h.const_mul (A i)
  have hrw : ∀ y, vecDot (u.grad y) (φ.toH1Function.grad y) =
      ∑ i : Fin d, A i * φ.toH1Function.grad y i := by
    intro y
    rw [hgrad y, vecDot]
  calc
    ∫ y in V, vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume
        = ∫ y in V, ∑ i : Fin d, A i * φ.toH1Function.grad y i ∂volume := by
          exact integral_congr_ae (Eventually.of_forall fun y => hrw y)
    _ = ∑ i : Fin d, ∫ y in V, A i * φ.toH1Function.grad y i ∂volume :=
          integral_finset_sum _ fun i _ => hint i
    _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [integral_const_mul, integral_grad_coord_h10_eq_zero φ i, mul_zero]

/-- The affine lift `ℓ_h` is weakly harmonic on the window. -/
theorem isUnitWeaklyHarmonicOn_affineLiftH1 {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] (hV : IsSobolevRegularDomain V)
    (x : Vec d) (c : ℝ) (A : Vec d) :
    IsUnitWeaklyHarmonicOn V (affineLiftH1 hV x c A) :=
  isUnitWeaklyHarmonicOn_of_grad_const (affineLiftH1_grad hV x c A)

/-! ## 3. Harmonicity under differences -/


theorem isUnitWeaklyHarmonicOn_sub {V : Set (Vec d)} {u v : H1Function V}
    (hu : IsUnitWeaklyHarmonicOn V u) (hv : IsUnitWeaklyHarmonicOn V v) :
    IsUnitWeaklyHarmonicOn V (u - v) := by
  intro φ
  have hrw : ∀ y, vecDot ((u - v).grad y) (φ.toH1Function.grad y) =
      vecDot (u.grad y) (φ.toH1Function.grad y) -
        vecDot (v.grad y) (φ.toH1Function.grad y) := by
    intro y
    rw [H1Function.sub_grad, vecDot, vecDot, vecDot, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.sub_apply]
      ring
  calc
    ∫ y in V, vecDot ((u - v).grad y) (φ.toH1Function.grad y) ∂volume
        = ∫ y in V, (vecDot (u.grad y) (φ.toH1Function.grad y) -
            vecDot (v.grad y) (φ.toH1Function.grad y)) ∂volume := by
          exact integral_congr_ae (Eventually.of_forall fun y => hrw y)
    _ = (∫ y in V, vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume) -
          ∫ y in V, vecDot (v.grad y) (φ.toH1Function.grad y) ∂volume :=
          integral_sub (integrableOn_vecDot_grad u φ.toH1Function)
            (integrableOn_vecDot_grad v φ.toH1Function)
    _ = 0 := by rw [hu φ, hv φ, sub_zero]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
