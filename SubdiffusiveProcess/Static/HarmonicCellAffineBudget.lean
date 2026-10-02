import SubdiffusiveProcess.Static.HarmonicCellAffineEnergy
import SubdiffusiveProcess.Static.HarmonicStoppedBallBudget
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.CenteredDilation

/-! # Normalized unit-cell energy under the physical cube chart -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Dilation pulls back the physical truncated ball to the exact unit window. -/
theorem harmonic_physical_ball_preimage {d : ℕ} (k : ℕ) (x : Vec d) (r : ℝ) :
    (fun y : Vec d => (3 : ℝ)^k • y) ⁻¹'
      (Metric.ball ((3 : ℝ)^k • x) ((3 : ℝ)^k*r) ∩ cube d (k : ℤ)) =
      Metric.ball x r ∩ openCubeSet (originCube d 0) := by
  have hS : 0 < (3 : ℝ)^k := by positivity
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hS,
    mul_lt_mul_iff_right₀ hS]
  rw [cube, originCube_eq_ball, originCube_eq_ball]
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos hS, zpow_natCast, zpow_zero]
  rw [show (3 : ℝ)^k/2 = (3 : ℝ)^k*(1/2) by ring, mul_lt_mul_iff_right₀ hS]

/-- The literal normalized unit energy is the physical raw energy times
`S² / (ahom*S^d)`, with no relaxation of the window. -/
theorem harmonic_unit_energy_eq_physical {d : ℕ} (M : GMCModel d) (j k : ℕ)
    (z : Vec d) (omega : PotentialSample d)
    (u : H1Function (openCubeSet (originCube d 0))) (x : Vec d) (r : ℝ) :
    (∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal ((ahom M j)⁻¹*aCutoff M j omega (z+(3 : ℝ)^k • y)*
        vecDot (u.grad y) (u.grad y))) =
    ENNReal.ofReal ((((3 : ℝ)^k)^d)⁻¹*((3 : ℝ)^k)^2*(ahom M j)⁻¹) *
      ∫⁻ y in Metric.ball ((3 : ℝ)^k • x) ((3 : ℝ)^k*r) ∩ cube d (k : ℤ),
        ENNReal.ofReal (aCutoff M j (translatePotentialSample z omega) y *
          vecDot ((centeredCubeRawDilation (k : ℤ) u).grad y)
            ((centeredCubeRawDilation (k : ℤ) u).grad y)) := by
  let S : ℝ := (3 : ℝ)^k
  have hS : 0 < S := by positivity
  have ha := ahom_pos M j
  have hchart := lintegral_window_affine (0 : Vec d) hS
    (W := Metric.ball (S • x) (S*r) ∩ cube d (k : ℤ))
    (measurableSet_ball.inter (isOpen_openCubeSet (originCube d (k : ℤ))).measurableSet)
    (fun y => ENNReal.ofReal (aCutoff M j (translatePotentialSample z omega) y *
      vecDot ((centeredCubeRawDilation (k : ℤ) u).grad y)
        ((centeredCubeRawDilation (k : ℤ) u).grad y)))
  simp only [zero_add] at hchart
  rw [harmonic_physical_ball_preimage] at hchart
  have hpoint : ∀ y, ENNReal.ofReal (aCutoff M j (translatePotentialSample z omega) (S • y)*
      vecDot ((centeredCubeRawDilation (k : ℤ) u).grad (S • y))
        ((centeredCubeRawDilation (k : ℤ) u).grad (S • y))) =
      ENNReal.ofReal ((S⁻¹)^2*ahom M j) *
        ENNReal.ofReal ((ahom M j)⁻¹*aCutoff M j omega (z+S • y)*
          vecDot (u.grad y) (u.grad y)) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hinv : (centeredCubeScale (k : ℤ))⁻¹ • (S • y) = y := by
      change S⁻¹ • (S • y) = y
      exact inv_smul_smul₀ hS.ne' y
    rw [centeredCubeRawDilation_grad, hinv]
    simp only [Section6Covariance.aCutoff_translatePotentialSample,
      vecDot_smul_left, vecDot_smul_right]
    change aCutoff M j omega (S • y+z) *
      (S⁻¹*(S⁻¹*vecDot (u.grad y) (u.grad y))) = _
    rw [add_comm (S • y) z]
    field_simp [ha.ne']
  simp_rw [hpoint] at hchart
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hchart
  rw [hchart, ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have hcancel : (S^d)⁻¹*S^2*(ahom M j)⁻¹*S^d*((S⁻¹)^2*ahom M j) = 1 := by
    field_simp [hS.ne', (ahom_pos M j).ne']
  rw [hcancel, ENNReal.ofReal_one, one_mul]

/-- The normalized affine price cancels both the coefficient and physical scale. -/
theorem harmonic_macroscopic_scale_cancel (d k : ℕ) {a B H : ℝ} (ha : 0 < a)
    {r : ℝ} (hr : 0 < r) :
    ((((3 : ℝ)^k)^d)⁻¹*((3 : ℝ)^k)^2*a⁻¹) *
      ((Real.sqrt a*((3 : ℝ)^k)⁻¹*B*H)^2 *
        (3 : ℝ)^((k : ℝ)/4) * (max ((3 : ℝ)^k*r) 1)^((d : ℝ)-1/4)) =
      B^2*H^2*(max r ((3 : ℝ)^k)⁻¹)^((d : ℝ)-1/4) := by
  let S : ℝ := (3 : ℝ)^k
  have hS : 0 < S := by positivity
  have hm : max (S*r) 1 = S * max r S⁻¹ := by
    rw [mul_max_of_nonneg _ _ hS.le, mul_inv_cancel₀ hS.ne']
  have hp : (3 : ℝ)^((k : ℝ)/4) * S^((d : ℝ)-1/4) = S^d := by
    dsimp only [S]
    rw [← Real.rpow_natCast (3 : ℝ) k, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  change (S^d)⁻¹*S^2*a⁻¹ * ((Real.sqrt a*S⁻¹*B*H)^2 *
    (3 : ℝ)^((k : ℝ)/4)*(max (S*r) 1)^((d : ℝ)-1/4)) = _
  rw [hm, Real.mul_rpow hS.le (le_trans hr.le (le_max_left _ _))]
  simp only [mul_pow, Real.sq_sqrt ha.le]
  calc
    _ = ((S^d)⁻¹*S^2*a⁻¹*(a*(S⁻¹)^2*B^2*H^2)) *
        ((3 : ℝ)^((k : ℝ)/4)*S^((d : ℝ)-1/4)) *
        (max r S⁻¹)^((d : ℝ)-1/4) := by ring
    _ = _ := by
      rw [hp]
      dsimp only [S]
      field_simp [hS.ne', ha.ne']

end SubdiffusiveProcess.Static
