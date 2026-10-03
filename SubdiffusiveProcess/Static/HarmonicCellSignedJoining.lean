module

public import SubdiffusiveProcess.Static.HarmonicCellEnvelopePrice
public import SubdiffusiveProcess.Static.HarmonicCellWholeEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

@[expose] public section

/-! # Literal translated signed-cell joining -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- A signed-cell macro budget, truncated at the physical unit scale. -/
def CutoffHarmonicCellSignedMacroscopicGrowth {d : ℕ} (M : GMCModel d) (j : ℕ) (k : ℤ)
    (z : Vec d) (omega : PotentialSample d) (G : ℝ) : Prop :=
  ∀ (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (B : ℝ), 0 ≤ B → HarmonicCutoffDatumSizeBound f B →
    ∀ u : H1Function (openCubeSet (originCube d 0)),
      IsWeaklyHarmonicOn
        (fun x => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ k • x))
        (openCubeSet (originCube d 0)) u →
      HasZeroTraceDifferenceOn (openCubeSet (originCube d 0)) u
        (cutoffHarmonicCellDatum f hf hc) →
      ∀ x ∈ openCubeSet (originCube d 0), ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
          ENNReal.ofReal ((ahom M j)⁻¹ *
            aCutoff M j omega (z + (3 : ℝ) ^ k • y) * vecNormSq (u.grad y)) ≤
          ENNReal.ofReal (G * B ^ 2 * (max r ((3 : ℝ) ^ k.toNat)⁻¹) ^ ((d : ℝ) - 1 / 4))

/-- The measurable polynomial envelope of the native all-radius price. -/
def harmonicCellJoinedEnvelope (d k : ℕ) (R D G : ℝ) : ℝ :=
  G + harmonicCellJoiningPrice d (harmonicCellContrast d) *
    (((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) *
      (R + G + harmonicCellTransition d D) ^ (d + 6)

theorem one_le_harmonicCellJoinedEnvelope (d k : ℕ) {R D G : ℝ}
    (hR : 1 ≤ R) (hD : 1 ≤ D) (hG : 1 ≤ G) :
    1 ≤ harmonicCellJoinedEnvelope d k R D G := by
  have hQ := harmonicCellJoiningPrice_nonneg d (harmonicCellContrast_pos d).le
  have hT := harmonicCellTransition_ge_two d (zero_le_one.trans hD)
  unfold harmonicCellJoinedEnvelope
  have h : 0 ≤ harmonicCellJoiningPrice d (harmonicCellContrast d) *
      (((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) *
      (R + G + harmonicCellTransition d D) ^ (d + 6) := by positivity
  linarith

/-- The literal bank bounds in an arbitrary translated signed chart. -/
theorem harmonicCell_translated_bank_bounds {d : ℕ} (M : GMCModel d)
    (j : ℕ) (k : ℤ) (z : Vec d) (omega : PotentialSample d) :
    let R := harmonicMicroscopicCoefficientBank M j k.toNat (translatePotentialSample z omega)
    let D := harmonicMicroscopicDerivativeBank M j k.toNat (translatePotentialSample z omega)
    let a := fun x : Vec d => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ k • x)
    (∀ x ∈ Metric.closedBall (0 : Vec d) (1 / 2), R⁻¹ ≤ a x ∧ a x ≤ R) ∧
      ∀ x ∈ Metric.closedBall (0 : Vec d) (1 / 2),
        ∀ y ∈ Metric.closedBall (0 : Vec d) (1 / 2),
          |Real.log (a x) - Real.log (a y)| ≤ ((3 : ℝ) ^ k.toNat * D) * ‖x - y‖ := by
  simpa only [Section6Covariance.aCutoff_translatePotentialSample, add_comm] using
    harmonicMicroscopicBank_unit_coefficient_bounds M j k (translatePotentialSample z omega)

/-- A signed macroscopic budget supplies the actual all-radius native clause. -/
theorem cutoffHarmonicCellGrowth_of_signed_macroscopic {d : ℕ} (M : GMCModel d)
    (j : ℕ) (k : ℤ) (z : Vec d) (omega : PotentialSample d) {G : ℝ} (hG : 1 ≤ G)
    (hmacro : CutoffHarmonicCellSignedMacroscopicGrowth M j k z omega G) :
    CutoffHarmonicCellGrowth M j k z omega
      (harmonicCellJoinedEnvelope d k.toNat
        (harmonicMicroscopicCoefficientBank M j k.toNat (translatePotentialSample z omega))
        (harmonicMicroscopicDerivativeBank M j k.toNat (translatePotentialSample z omega)) G) := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  haveI : NeZero d := ⟨by omega⟩
  let R := harmonicMicroscopicCoefficientBank M j k.toNat (translatePotentialSample z omega)
  let D := harmonicMicroscopicDerivativeBank M j k.toNat (translatePotentialSample z omega)
  let a := fun x : Vec d => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ k • x)
  let eps := ((3 : ℝ) ^ k.toNat)⁻¹
  let T := harmonicCellTransition d D
  have hR : 1 ≤ R := one_le_harmonicMicroscopicCoefficientBank _ _ _ _
  have hD : 1 ≤ D := one_le_harmonicMicroscopicDerivativeBank _ _ _ _
  have hT : 2 ≤ T := harmonicCellTransition_ge_two d (zero_le_one.trans hD)
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have heps1 : eps ≤ 1 := by
    dsimp only [eps]
    exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have ha : Continuous a := continuous_const.mul ((continuous_aCutoff M j omega).comp
    (by fun_prop))
  have hapos : ∀ x, 0 < a x := fun x =>
    mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M j)) (aCutoff_pos _ _ _ _)
  obtain ⟨hacoef, hlog⟩ := harmonicCell_translated_bank_bounds M j k z omega
  intro f hf hc B hB hfB u hu htr x hx r hr hr1
  have hgrow := harmonicCell_all_radius_energy_le hd a u (cutoffHarmonicCellDatum f hf hc)
    ha hapos heps heps1 hT hR hG (by positivity : 0 ≤ (3 : ℝ) ^ k.toNat * D) hB
    hacoef (cutoffHarmonicCellDatum_gradient_le f hf hc hB hfB) hlog
    (harmonicCellContrast_pos d).le le_rfl
    (harmonicCellTransition_small_modulus d k.toNat (zero_le_one.trans hD)) hu htr
    (hmacro f hf hc B hB hfB u hu htr) x hx r hr hr1
  refine hgrow.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpoly := harmonicCell_polynomial_le_sum_power d (zero_le_one.trans hR)
    (zero_le_one.trans hG) (by linarith : 0 ≤ T)
  have hQ := harmonicCellJoiningPrice_nonneg d (harmonicCellContrast_pos d).le
  change (G + harmonicCellJoiningPrice d (harmonicCellContrast d) *
    (eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d)) * B ^ 2 * r ^ ((d : ℝ) - 1 / 2) ≤ _
  have hprice := mul_le_mul_of_nonneg_left hpoly
    (mul_nonneg hQ (by positivity : 0 ≤ eps ^ (1 / 4 : ℝ)))
  have h := mul_le_mul_of_nonneg_right hprice
    (by positivity : 0 ≤ B ^ 2 * r ^ ((d : ℝ) - 1 / 2))
  dsimp only [harmonicCellJoinedEnvelope, eps, T, R, D] at *
  nlinarith only [h]

/-- At nonpositive physical scales, the exact whole-cell variational bound
is the required signed macroscopic budget. -/
theorem cutoffHarmonicCellSignedMacroscopicGrowth_of_nonpos {d : ℕ} (M : GMCModel d)
    (j : ℕ) (k : ℤ) (hk : k ≤ 0) (z : Vec d) (omega : PotentialSample d) :
    let R := harmonicMicroscopicCoefficientBank M j k.toNat (translatePotentialSample z omega)
    CutoffHarmonicCellSignedMacroscopicGrowth M j k z omega (1 + R * (d : ℝ) ^ 2) := by
  let R := harmonicMicroscopicCoefficientBank M j k.toNat (translatePotentialSample z omega)
  let a := fun x : Vec d => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ k • x)
  have hR : 1 ≤ R := one_le_harmonicMicroscopicCoefficientBank _ _ _ _
  have ha : Continuous a := continuous_const.mul ((continuous_aCutoff M j omega).comp
    (by fun_prop))
  have hapos : ∀ x, 0 < a x := fun x =>
    mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M j)) (aCutoff_pos _ _ _ _)
  have hb := (harmonicCell_translated_bank_bounds M j k z omega).1
  change CutoffHarmonicCellSignedMacroscopicGrowth M j k z omega (1 + R * (d : ℝ) ^ 2)
  intro f hf hc B hB hfB u hu htr x hx r hr hr1
  have hwhole := harmonicCell_whole_energy_le a ha hapos hR
    (fun y hy => hb y (unitCell_mem_closedBall hy)) f hf hc B hB hfB u hu htr
  have hkN : k.toNat = 0 := by omega
  simp only [hkN, pow_zero, inv_one, max_eq_right hr1, Real.one_rpow]
  refine (lintegral_mono_set Set.inter_subset_right).trans (hwhole.trans
    (ENNReal.ofReal_le_ofReal ?_))
  change R * (d : ℝ) ^ 2 * B ^ 2 ≤ (1 + R * (d : ℝ) ^ 2) * B ^ 2 * 1
  nlinarith only [sq_nonneg B]

end SubdiffusiveProcess.Static
