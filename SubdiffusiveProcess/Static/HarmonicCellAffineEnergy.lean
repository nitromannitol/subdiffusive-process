module

public import SubdiffusiveProcess.Static.HarmonicCellSmallContrastEnergy
public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastBallRescaling

@[expose] public section

/-! # Exact physical-ball energy scaling for harmonic cutoff cells -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Affine lower-integral change of variables on any measurable window. -/
theorem lintegral_window_affine {d : ℕ} (z : Vec d) {rho : ℝ} (hrho : 0 < rho)
    {W : Set (Vec d)} (hW : MeasurableSet W) (g : Vec d → ℝ≥0∞) :
    (∫⁻ x in W, g x) = ENNReal.ofReal (rho ^ d) *
      ∫⁻ y in (fun y => z + rho • y) ⁻¹' W, g (z + rho • y) := by
  have hchart : cubeDilation z (0 : Vec d) rho = fun y => z + rho • y := by
    funext y i
    simp [cubeDilation_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hmap : Measure.map (cubeDilation z (0 : Vec d) rho)
      (volume.restrict ((cubeDilation z (0 : Vec d) rho) ⁻¹' W)) =
      ENNReal.ofReal |(rho ^ d)⁻¹| • volume.restrict W := by
    rw [← Measure.restrict_map (continuous_cubeDilation _ _ _).measurable hW,
      map_cubeDilation_volume _ _ hrho.ne', Measure.restrict_smul]
  have hcoe : ⇑(cubeDilationEquiv z (0 : Vec d) hrho.ne') =
      cubeDilation z (0 : Vec d) rho := rfl
  have h := lintegral_map_equiv
    (μ := volume.restrict ((cubeDilation z (0 : Vec d) rho) ⁻¹' W))
    g (cubeDilationEquiv z (0 : Vec d) hrho.ne')
  rw [hcoe, hmap, lintegral_smul_measure, hchart, smul_eq_mul] at h
  rw [← h, ← mul_assoc]
  have hcancel : ENNReal.ofReal (rho ^ d) * ENNReal.ofReal |(rho ^ d)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity)]
    simp
  rw [hcancel, one_mul]

/-- The radius in a concentric physical ball is divided by the chart scale. -/
theorem affine_preimage_euclideanBall {d : ℕ} (z : Vec d) {rho r : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) :
    (fun y => z + rho • y) ⁻¹' euclideanBall z r =
      euclideanBall (0 : Vec d) (r / rho) := by
  ext y
  simp only [Set.mem_preimage, euclideanBall, Set.mem_setOf_eq]
  rw [show z + rho • y = rho • y + z from add_comm _ _,
    euclideanSqDist_affine_center]
  have heq : (r / rho) ^ 2 = r ^ 2 / rho ^ 2 := div_pow r rho 2
  rw [heq]
  constructor
  · intro h
    apply (lt_div_iff₀ (sq_pos_of_pos hrho)).2
    rwa [mul_comm]
  · intro h
    have h' := (lt_div_iff₀ (sq_pos_of_pos hrho)).1 h
    rwa [mul_comm] at h'

/-- Concentric physical-ball energy scales by the exact positive Jacobian. -/
theorem lintegral_euclideanBall_affine {d : ℕ} (z : Vec d) {rho r : ℝ}
    (hrho : 0 < rho) (hr : 0 < r) (g : Vec d → ℝ≥0∞) :
    (∫⁻ x in euclideanBall z r, g x) = ENNReal.ofReal (rho ^ d) *
      ∫⁻ y in euclideanBall (0 : Vec d) (r / rho), g (rho • y + z) := by
  rw [lintegral_window_affine z hrho (isOpen_euclideanBall z r).measurableSet,
    affine_preimage_euclideanBall z hrho hr]
  simp only [add_comm z]

/-- Pulling back the native gradient row gives the exact physical exponent
`d-1/2`; the dimensional Jacobian leaves a half-power of the chart radius. -/
theorem physical_ball_energy_growth_of_gradient_row {d : ℕ} [NeZero d]
    (z : Vec d) {rho kappa K Lam r : ℝ} (hrho : 0 < rho) (hkappa : 0 < kappa)
    (a : Vec d → ℝ) (u : H1Function (euclideanBall z rho))
    (hK : 0 ≤ K) (hLam : 0 ≤ Lam)
    (ha : ∀ y ∈ smallContrastUnitBall d,
      ballToUnitCoefficient a z rho kappa y ≤ Lam)
    (hrow : HasInteriorSmallContrastGradientScaleBound (3 / 4 : ℝ) K
      (ballToUnitH1 z hrho u)) (hr : 0 < r) (hrhalf : r ≤ rho / 2) :
    ∫⁻ x in euclideanBall z r, ENNReal.ofReal (a x * vecDot (u.grad x) (u.grad x)) ≤
      ENNReal.ofReal (kappa * rho ^ (1 / 2 : ℝ) * Lam *
        (volume (smallContrastUnitBall d)).toReal * K ^ 2 * r ^ ((d : ℝ) - 1 / 2)) := by
  let v := ballToUnitH1 z hrho u
  let au := ballToUnitCoefficient a z rho kappa
  have hrunit : 0 < r / rho := div_pos hr hrho
  have hrsmall : r / rho ≤ 1 / 2 := (div_le_iff₀ hrho).2 (by linarith)
  have hzero : (0 : Vec d) ∈ smallContrastBall d (1 / 2) := by
    change euclideanSqDist (0 : Vec d) 0 < (1 / 2 : ℝ) ^ 2
    simp [euclideanSqDist, vecNormSq, vecDot]
  have hraw := interior_energy_growth_of_gradient_row v au hK hLam ha hrow
    0 hzero (r / rho) hrunit hrsmall
  have hpoint : ∀ y, ENNReal.ofReal
      (a (rho • y + z) * vecDot (u.grad (rho • y + z)) (u.grad (rho • y + z))) =
      ENNReal.ofReal kappa * ENNReal.ofReal (au y * vecDot (v.grad y) (v.grad y)) := by
    intro y
    rw [← ENNReal.ofReal_mul hkappa.le]
    congr 1
    simp only [v, au, ballToUnitCoefficient, ballToUnitH1_grad]
    field_simp
  rw [lintegral_euclideanBall_affine z hrho hr]
  simp_rw [hpoint]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_right (mul_le_mul_right hraw (ENNReal.ofReal kappa))
    (ENNReal.ofReal (rho ^ d))).trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ rho ^ d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ rho ^ d * kappa)]
  congr 1
  have hpowers : rho ^ d * (r / rho) ^ ((d : ℝ) - 1 / 2) =
      rho ^ (1 / 2 : ℝ) * r ^ ((d : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast, Real.div_rpow hr.le hrho.le]
    have hfactor : rho ^ (d : ℝ) =
        rho ^ (1 / 2 : ℝ) * rho ^ ((d : ℝ) - 1 / 2) := by
      rw [← Real.rpow_add hrho]
      congr 1
      ring
    rw [hfactor]
    field_simp
  calc
    rho ^ d * kappa * (Lam * (volume (smallContrastUnitBall d)).toReal * K ^ 2 *
        (r / rho) ^ ((d : ℝ) - 1 / 2)) =
      kappa * Lam * (volume (smallContrastUnitBall d)).toReal * K ^ 2 *
        (rho ^ d * (r / rho) ^ ((d : ℝ) - 1 / 2)) := by ring
    _ = _ := by rw [hpowers]; ring

end SubdiffusiveProcess.Static
