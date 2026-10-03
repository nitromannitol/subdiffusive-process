module

public import SubdiffusiveProcess.Static.HarmonicCellPhysicalBudget
public import SubdiffusiveProcess.Static.HarmonicCellAffineBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.TailSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ZeroDatum

@[expose] public section

/-! # Joining the native physical energy and Hölder rows -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The closed native energy and stopping rows give the literal unit-ball budget. -/
theorem harmonicCell_native_energy_growth {d : ℕ} (hd : 2 ≤ d)
    (M : GMCModel d) (j k : ℕ) (hjk : j ≤ k) (z : Vec d) (omega : PotentialSample d)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hb : HarmonicCutoffDatumSizeBound f B)
    (u : H1Function (openCubeSet (originCube d 0))) {CH E : ℝ}
    (hCH : 0 ≤ CH) (hE : 0 ≤ E) (X : ℕ)
    (hwhole : vectorNormalizedL2On (cube d (k : ℤ))
      (fun y => Real.sqrt (aCutoff M j (translatePotentialSample z omega) y) •
        (centeredCubeRawDilation (k : ℤ) u).grad y) ≤
      Real.sqrt (ahom M j)*((3 : ℝ)^k)⁻¹*B*E)
    (hconcl : HolderRegularityConclusions M CH j (translatePotentialSample z omega)
      (7/8) k X (centeredCubeRawDilation (k : ℤ) u)
      (centeredCubeRawDilation (k : ℤ) (cutoffHarmonicCellDatum f hf hc)) (fun _ => 0))
    (x : Vec d) (hx : x ∈ openCubeSet (originCube d 0)) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal ((ahom M j)⁻¹*aCutoff M j omega (z+(3 : ℝ)^k • y)*
        vecDot (u.grad y) (u.grad y)) ≤
    ENNReal.ofReal (((1+CH^2)*(6 : ℝ)^((d : ℝ)-1/4)*(E+3*(d : ℝ))^2*
      (3 : ℝ)^((d : ℝ)*(X : ℝ))) * B^2 *
      (max r ((3 : ℝ)^k)⁻¹)^((d : ℝ)-1/4)) := by
  classical
  let S : ℝ := (3 : ℝ)^k
  let U := centeredCubeRawDilation (k : ℤ) u
  let H := centeredCubeRawDilation (k : ℤ) (cutoffHarmonicCellDatum f hf hc)
  let A := aCutoff M j (translatePotentialSample z omega)
  let D := Real.sqrt (ahom M j)*S⁻¹*B*(E+3*(d : ℝ))
  have hS : 0 < S := by positivity
  have ha := ahom_pos M j
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE' : E ≤ E+3*(d : ℝ) := le_add_of_nonneg_right (by positivity)
  have hwhole' : vectorNormalizedL2On (cube d (k : ℤ))
      (fun y => Real.sqrt (A y) • U.grad y) ≤ D :=
    hwhole.trans (mul_le_mul_of_nonneg_left hE' (by positivity))
  obtain ⟨_, hfrac⟩ := harmonicDatum_rawDilation_holder_bounds f hf hc hB hb (k : ℤ)
  have hboundary : (ahom M j)^(1/2 : ℝ)*(3 : ℝ)^((k : ℝ)/2)*
      fractionalInfinityNormOnReal (cube d (k : ℤ)) ((3 : ℝ)^k) (1/2) H.grad ≤
      Real.sqrt (ahom M j)*S⁻¹*B*(3*(d : ℝ)) := by
    have hfrac' : fractionalInfinityNormOnReal (cube d (k : ℤ)) ((3 : ℝ)^k) (1/2) H.grad ≤
        3*(d : ℝ)*B*S^(-(3/2 : ℝ)) := by
      simpa only [Int.cast_natCast, zpow_natCast] using hfrac
    refine (mul_le_mul_of_nonneg_left hfrac' (by positivity)).trans_eq ?_
    have hp : (3 : ℝ)^((k : ℝ)/2)*S^(-(3/2 : ℝ)) = S⁻¹ := by
      have hpS : (3 : ℝ)^((k : ℝ)/2) = S^(1/2 : ℝ) := by
        dsimp only [S]
        rw [← Real.rpow_natCast (3 : ℝ) k, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
      rw [hpS, ← Real.rpow_add hS, show (1/2 : ℝ)+ -(3/2 : ℝ) = -1 by norm_num,
        Real.rpow_neg_one]
    rw [← Real.sqrt_eq_rpow]
    calc
      _ = Real.sqrt (ahom M j)*B*(3*(d : ℝ))*
          ((3 : ℝ)^((k : ℝ)/2)*S^(-(3/2 : ℝ))) := by ring
      _ = _ := by rw [hp]; ring
  have hrow : ∀ n : ℕ, (n : ℤ) ≤ (k : ℤ)-(X : ℤ) → ∀ y ∈ cube d (k : ℤ),
      vectorNormalizedL2On (truncatedCube d (k : ℤ) (n : ℤ) y)
        (fun w => Real.sqrt (A w) • U.grad w) ≤
        CH*(3 : ℝ)^((1-(7/8 : ℝ))*((k : ℝ)-(n : ℝ)))*D := by
    intro n hn y hy
    have hh := hconcl.2.1 n hn y hy
    rw [Section6TheoremC.holderSeminormOn_zero,
      Section6HolderInterior.tailAverage_cube_eq_ahom_of_cutoff_le M hjk,
      mul_zero, add_zero] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hif : (if y ∈ cube d ((k : ℤ)-1) then 0 else
        (ahom M j)^(1/2 : ℝ)*(3 : ℝ)^((k : ℝ)/2)*
        fractionalInfinityNormOnReal (cube d (k : ℤ)) ((3 : ℝ)^k) (1/2) H.grad) ≤
        Real.sqrt (ahom M j)*S⁻¹*B*(3*(d : ℝ)) := by
      split_ifs
      · positivity
      · exact hboundary
    have hh' := add_le_add hwhole hif
    simpa only [D, mul_add] using hh'
  let P := (1+CH^2)*D^2
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hvol : (volume (cube d (k : ℤ))).toReal = S^d := by
    rw [cube, volume_openCubeSet_toReal]
    simp [cubeVolume, cubeScaleFactor, originCube, S]
  have hwholeRaw : ∫⁻ y in cube d (k : ℤ), ENNReal.ofReal (A y*vecDot (U.grad y) (U.grad y)) ≤
      ENNReal.ofReal (P*S^d) := by
    have hh := lintegral_energy_le_volume_mul_sq (cube d (k : ℤ)) A U.grad
      (fun y => (aCutoff_pos M j _ y).le) (by rw [hvol]; positivity)
      (Section6HarmonicApproximation.integrableOn_aCutoff_energy M j _ (originCube d (k : ℤ)) U)
      hD hwhole'
    rw [hvol] at hh
    refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp only [P]
    have hp : D^2 ≤ (1+CH^2)*D^2 := by
      nlinarith [sq_nonneg (CH*D)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hp (pow_nonneg hS.le d)
  have hwindow : ∀ n : ℕ, (n : ℤ) ≤ (k : ℤ)-(X : ℤ) → ∀ y ∈ cube d (k : ℤ),
      ∫⁻ w in truncatedCube d (k : ℤ) (n : ℤ) y,
        ENNReal.ofReal (A w*vecDot (U.grad w) (U.grad w)) ≤
      ENNReal.ofReal (P*(3 : ℝ)^((k : ℝ)/4)*((3 : ℝ)^n)^((d : ℝ)-1/4)) := by
    intro n hn y hy
    have hh := cutoff_window_energy_growth_of_gradient_row M j (translatePotentialSample z omega)
      k X (7/8) U hCH hD hrow n hn y hy
    norm_num only [show (2 : ℝ)*(1-7/8) = 1/4 by norm_num] at hh
    refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp : CH^2*D^2 ≤ P := by dsimp only [P]; nlinarith [sq_nonneg D]
    calc
      _ = CH^2*D^2*(3 : ℝ)^((k : ℝ)/4)*((3 : ℝ)^n)^((d : ℝ)-1/4) := by
        congr 2
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp
        (show 0 ≤ (3 : ℝ)^((k : ℝ)/4) by positivity))
        (show 0 ≤ ((3 : ℝ)^n)^((d : ℝ)-1/4) by positivity)
  have hx' : S • x ∈ cube d (k : ℤ) := by
    rw [cube, originCube_eq_ball]
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos hS, zpow_natCast]
    have hx0 : ‖x‖ < (1/2 : ℝ) := by
      simpa only [originCube_eq_ball, Metric.mem_ball, dist_eq_norm, sub_zero, zpow_zero] using hx
    calc
      S*‖x‖ < S*(1/2) := mul_lt_mul_of_pos_left hx0 hS
      _ = _ := by dsimp only [S]; ring
  have hraw := harmonic_stopped_ball_budget hd k X (fun y => ENNReal.ofReal
    (A y*vecDot (U.grad y) (U.grad y))) hP hwholeRaw hwindow (S • x) hx' (mul_pos hS hr)
  rw [harmonic_unit_energy_eq_physical]
  refine (mul_le_mul_right hraw (ENNReal.ofReal ((S^d)⁻¹*S^2*(ahom M j)⁻¹))).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hcanc := harmonic_macroscopic_scale_cancel d k (ahom_pos M j) (B := B)
    (H := E+3*(d : ℝ)) hr
  dsimp only [P, D]
  calc
    _ = (1+CH^2)*(6 : ℝ)^((d : ℝ)-1/4)*(3 : ℝ)^((d : ℝ)*(X : ℝ)) *
        (((S^d)⁻¹*S^2*(ahom M j)⁻¹)*
          ((Real.sqrt (ahom M j)*S⁻¹*B*(E+3*(d : ℝ)))^2*
            (3 : ℝ)^((k : ℝ)/4)*(max (S*r) 1)^((d : ℝ)-1/4))) := by ring
    _ = _ := by rw [hcanc]; ring

end SubdiffusiveProcess.Static
