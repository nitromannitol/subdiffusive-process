import SubdiffusiveProcess.Section10.PhysicalTightnessAffine

/-! The local weighted Moser estimate is transported to the physical chart.
The same positive spatial constant that changes the speed appears in the
Jacobian. No smoothness, law equality or Feller premise enters this transport. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped Pointwise ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- Exact weighted L2 lower integral in an affine chart. -/
theorem affine_weighted_square {d : ℕ} {V : Set (Vec d)} {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) (z : Vec d) {rho b : Vec d → ℝ}
    (hrho : ∀ x, rho (r • x + z) = c * b x)
    (w : H1Function (translateSet z (r • V))) :
    (∫⁻ y in translateSet z (r • V), ENNReal.ofReal (w.toFun y ^ 2 * rho y)) =
      ENNReal.ofReal (r ^ d * c) *
        ∫⁻ x in V, ENNReal.ofReal ((affineH1Pullback hr z w).toFun x ^ 2 * b x) := by
  rw [affine_lintegral hr]
  simp_rw [hrho]
  have hpoint : (fun x : Vec d => ENNReal.ofReal (w.toFun (r • x + z) ^ 2 * (c * b x))) =
      fun x => ENNReal.ofReal c *
        ENNReal.ofReal ((affineH1Pullback hr z w).toFun x ^ 2 * b x) := by
    funext x
    rw [affineH1Pullback_toFun, ← ENNReal.ofReal_mul hc.le]
    congr 1
    ring
  rw [hpoint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (pow_nonneg hr.le d)]

/-- The local square integral is the physical one divided by the exact
positive volume/speed factor, even when an integral is infinite. -/
theorem affine_weighted_square_pullback {d : ℕ} {V : Set (Vec d)} {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) (z : Vec d) {rho b : Vec d → ℝ}
    (hrho : ∀ x, rho (r • x + z) = c * b x)
    (w : H1Function (translateSet z (r • V))) :
    (∫⁻ x in V, ENNReal.ofReal ((affineH1Pullback hr z w).toFun x ^ 2 * b x)) =
      ENNReal.ofReal ((r ^ d * c)⁻¹) *
        ∫⁻ y in translateSet z (r • V), ENNReal.ofReal (w.toFun y ^ 2 * rho y) := by
  rw [affine_weighted_square hr hc z hrho w, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_nonneg (pow_nonneg hr.le d) hc.le)),
    inv_mul_cancel₀ (mul_pos (pow_pos hr d) hc).ne', ENNReal.ofReal_one, one_mul]

/-- A local Moser constant becomes `Km * sqrt((r^d*c)^-1)` in the physical
chart. The actual subsolution and all a.e. hypotheses are pulled back. -/
theorem moser_affine_transport {d : ℕ} {V W : Set (Vec d)} {r c gamma Km : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hgamma : 0 < gamma) (hKm : 0 ≤ Km)
    (z : Vec d) {rho b coefficient a : Vec d → ℝ}
    (hrho : ∀ x, rho (r • x + z) = c * b x)
    (hcoeff : ∀ x, coefficient (r • x + z) = gamma * a x)
    (hmoser : ∀ w : H1Function V,
      (∀ᵐ x ∂volume.restrict V, 0 ≤ w.toFun x) →
      (∃ Mw : ℝ, ∀ᵐ x ∂volume.restrict V, w.toFun x ≤ Mw) →
      IsWeakSubSolutionOn a V w →
      ∀ᵐ x ∂volume.restrict W,
        ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal Km *
          (∫⁻ y in V, ENNReal.ofReal (w.toFun y ^ 2 * b y)) ^ (1 / 2 : ℝ)) :
    ∀ w : H1Function (translateSet z (r • V)),
      (∀ᵐ y ∂volume.restrict (translateSet z (r • V)), 0 ≤ w.toFun y) →
      (∃ Mw : ℝ, ∀ᵐ y ∂volume.restrict (translateSet z (r • V)), w.toFun y ≤ Mw) →
      IsWeakSubSolutionOn coefficient (translateSet z (r • V)) w →
      ∀ᵐ y ∂volume.restrict (translateSet z (r • W)),
        ENNReal.ofReal (w.toFun y) ≤ ENNReal.ofReal (Km * Real.sqrt ((r ^ d * c)⁻¹)) *
          (∫⁻ q in translateSet z (r • V), ENNReal.ofReal (w.toFun q ^ 2 * rho q)) ^
            (1 / 2 : ℝ) := by
  intro w hw0 hwB hwsub
  obtain ⟨Mw, hwM⟩ := hwB
  have h0 : ∀ᵐ x ∂volume.restrict V, 0 ≤ (affineH1Pullback hr z w).toFun x :=
    (affine_ae_iff hr z _).mp hw0
  have hM : ∀ᵐ x ∂volume.restrict V, (affineH1Pullback hr z w).toFun x ≤ Mw :=
    (affine_ae_iff hr z _).mp hwM
  have hs := subsolution_affine_pullback hr hgamma z hcoeff w hwsub
  have hm := hmoser (affineH1Pullback hr z w) h0 ⟨Mw, hM⟩ hs
  rw [affine_weighted_square_pullback hr hc z hrho w,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← Real.sqrt_eq_rpow, ← mul_assoc, ← ENNReal.ofReal_mul hKm] at hm
  exact (affine_ae_iff hr z _).mpr hm

/-- The exact sup-norm cube chart, including arbitrary positive radii. -/
theorem affine_ball_eq {d : ℕ} {r : ℝ} (hr : 0 < r) (z : Vec d) (R : ℝ) :
    translateSet z (r • Metric.ball (0 : Vec d) R) = Metric.ball z (r * R) := by
  rw [_root_.smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr]
  ext y
  simp only [mem_translateSet_iff_sub_mem, Metric.mem_ball, dist_eq_norm, sub_zero]

end SubdiffusiveProcess.Section10.PhysicalTightness
