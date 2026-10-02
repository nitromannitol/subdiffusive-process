import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution

/-!
# Law-free ingredients for the massive interior estimate

Sobolev plus Dirichlet Poincare gives a pure energy Sobolev inequality.
If a variational Green solution `g` to `H g = u` has been constructed,
then `u + mu g` is weakly harmonic whenever `(mu + H) u = 0`.
Neither statement uses a diffusion law. These results do not construct
the Green operator or establish its `Lᵖ → Lᑫ` smoothing estimate.
-/

set_option autoImplicit false
noncomputable section

open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The two frozen form assumptions imply a pure Dirichlet Sobolev bound. -/
theorem sobolev_energy_bound_of_sobolevAssumption_poincareAssumption
    {d : ℕ} {U : Set (Vec d)} {c rho : Vec d → ℝ} {p A F : ℝ}
    (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hc : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x)
    (hSob : SobolevAssumption c rho U p A F)
    (hPoi : PoincareAssumption c rho U A F) (v : H10Function U) :
    lpSq rho U p v.toH1Function.toFun ≤
      ENNReal.ofReal (A * (A + 1) * F *
        ((weightedMeasure rho U).toReal) ^ (-(1 - 2 / p))) *
          ENNReal.ofReal (energy c U v.toH1Function) := by
  have hE : 0 ≤ energy c U v.toH1Function := by
    apply integral_nonneg_of_ae
    filter_upwards [hc] with x hx
    exact mul_nonneg hx (vecNormSq_nonneg _)
  have hAF : 0 ≤ A * F := mul_nonneg hA hF
  have hweight : 0 ≤ ((weightedMeasure rho U).toReal) ^ (-(1 - 2 / p)) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  calc
    lpSq rho U p v.toH1Function.toFun ≤
        ENNReal.ofReal (A * ((weightedMeasure rho U).toReal) ^ (-(1 - 2 / p))) *
          (lpSq rho U 2 v.toH1Function.toFun + ENNReal.ofReal (F * energy c U v.toH1Function)) :=
      hSob v
    _ ≤ ENNReal.ofReal (A * ((weightedMeasure rho U).toReal) ^ (-(1 - 2 / p))) *
          (ENNReal.ofReal (A * F * energy c U v.toH1Function) +
            ENNReal.ofReal (F * energy c U v.toH1Function)) :=
      mul_le_mul' le_rfl (add_le_add (hPoi v) le_rfl)
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg hAF hE) (mul_nonneg hF hE),
        ← ENNReal.ofReal_mul (mul_nonneg hA hweight),
        ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hA (by positivity)) hF) hweight)]
      congr 1
      ring

/-- The signed massive solution has a harmonic variational correction.

`hgreen` is the actual zero-mass weak Green equation, not a smoothing estimate.
The existence of such a `g` remains a separate variational construction. -/
theorem isWeaklyHarmonicOn_add_green_correction
    {d : ℕ} {U : Set (Vec d)} {c rho : Vec d → ℝ} {mu lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    (u g : H1Function U)
    (hu : IsMassiveWeakSolutionOn c rho mu U u (fun _ => 0))
    (hgreen : IsMassiveWeakSolutionOn c rho 0 U g u.toFun) :
    IsWeaklyHarmonicOn c U (u + mu • g) := by
  intro phi
  have huEq := hu phi
  have hgEq := hgreen phi
  simp only [mul_zero, integral_zero, zero_mul, zero_add] at huEq hgEq
  have huInt := integrableOn_energy_term hEll u.grad_memVectorL2
    phi.toH1Function.grad_memVectorL2
  have hgInt := integrableOn_energy_term hEll g.grad_memVectorL2
    phi.toH1Function.grad_memVectorL2
  have hsplit :
      (∫ x in U, vecDot (c x • (u + mu • g).grad x) (phi.toH1Function.grad x)) =
        (∫ x in U, vecDot (c x • u.grad x) (phi.toH1Function.grad x)) +
          mu * ∫ x in U, vecDot (c x • g.grad x) (phi.toH1Function.grad x) := by
    have heq : (fun x => vecDot (c x • (u + mu • g).grad x) (phi.toH1Function.grad x)) =
        fun x => vecDot (c x • u.grad x) (phi.toH1Function.grad x) +
          mu * vecDot (c x • g.grad x) (phi.toH1Function.grad x) := by
      funext x
      rw [H1Function.add_grad, H1Function.smul_grad]
      simp only [smul_add, vecDot_add_left, vecDot_smul_left]
      ring
    rw [heq, integral_add huInt (hgInt.const_mul mu), integral_const_mul]
  rw [hsplit, hgEq]
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
