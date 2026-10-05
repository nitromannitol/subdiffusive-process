module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveMass
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeExitTransfer

@[expose] public section

/-!
# From normalized Sobolev estimates to the good-cube display

The Section 8 power integral is normalized by coefficient mass, while its
energy is averaged by Lebesgue volume. Multiplying out therefore retains
one factor of the coefficient average. The last theorem isolates exactly
this scalar price and gives `GoodCubeSobolevDisplay` for a cutoff coefficient.

-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Remove a finite positive mass from a normalized power bound. -/
theorem goodCube_unnormalize_power {mass I K : ℝ≥0∞} {r : ℝ}
    (hm0 : mass ≠ 0) (hmt : mass ≠ ⊤) (hr : 0 ≤ r)
    (h : (mass⁻¹ * I) ^ r ≤ K * mass⁻¹) :
    I ^ r ≤ K * mass ^ (r - 1) := by
  have hmr0 : mass ^ r ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hm0) hmt)
  have hmrT : mass ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hm0 hmt
  have key : mass ^ r * (mass⁻¹ * I) ^ r = I ^ r := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ENNReal.inv_rpow,
      ENNReal.mul_inv_cancel_left hmr0 hmrT]
  have h2 : mass ^ r * (mass⁻¹ * I) ^ r ≤ mass ^ r * (K * mass⁻¹) :=
    mul_le_mul_right h (mass ^ r)
  have hsub : mass ^ r * mass⁻¹ = mass ^ (r - 1) := by
    rw [ENNReal.rpow_sub r 1 hm0 hmt, ENNReal.rpow_one, div_eq_mul_inv]
  have h3 : mass ^ r * (K * mass⁻¹) = K * mass ^ (r - 1) := by
    rw [← mul_assoc, mul_comm (mass ^ r) K, mul_assoc, hsub]
  exact le_trans (le_of_eq key.symm) (le_trans h2 (le_of_eq h3))

/-- Express the squared weighted Lᵖ norm as the weighted power integral. -/
theorem goodCube_lpSq_eq_weighted_power {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {a : Vec d → ℝ} (ha : Measurable a)
    (f : Vec d → ℝ) {p : ℝ} (hp : 0 < p) :
    lpSq a U p f =
      (∫⁻ x in U, ENNReal.ofReal (|f x| ^ p * a x)) ^ (2 / p) := by
  have hpq0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hpqt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpto : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  unfold lpSq
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral hpq0 hpqt f _, hpto,
    MeasureTheory.restrict_withDensity hU,
    lintegral_withDensity_eq_lintegral_mul_non_measurable (volume.restrict U)
      ha.ennreal_ofReal
      (ae_of_all (volume.restrict U) fun _ => ENNReal.ofReal_lt_top)
      (fun x => ‖f x‖ₑ ^ p)]
  have hexp : ((∫⁻ x in U, ENNReal.ofReal (a x) * ‖f x‖ₑ ^ p) ^ (1 / p)) ^ (2 : ℕ)
      = (∫⁻ x in U, ENNReal.ofReal (|f x| ^ p * a x)) ^ (2 / p) := by
    have hint : ∫⁻ x in U, ENNReal.ofReal (a x) * ‖f x‖ₑ ^ p
        = ∫⁻ x in U, ENNReal.ofReal (|f x| ^ p * a x) := by
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) p), mul_comm]
    have he : (1 / p) * 2 = (2 / p : ℝ) := by ring
    rw [hint, ← ENNReal.rpow_two, ← ENNReal.rpow_mul, he]
  simpa only [Pi.mul_apply] using! hexp

/-- On a set of finite nonzero volume, weighted mass is volume times average. -/
theorem goodCube_weightedMeasure_eq_volume_mul_average {d : ℕ}
    {U : Set (Vec d)} (hU : MeasurableSet U)
    (hv0 : volume U ≠ 0) (hvt : volume U ≠ ⊤)
    {a : Vec d → ℝ} (ha : IntegrableOn a U)
    (hnn : ∀ᵐ x ∂volume.restrict U, 0 ≤ a x) :
    weightedMeasure a U = ENNReal.ofReal (volumeAverage U a) * volume U := by
  have hI : ENNReal.ofReal (∫ x in U, a x)
      = ∫⁻ x in U, ENNReal.ofReal (a x) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal ha hnn
  have key : ENNReal.ofReal (volumeAverage U a) * volume U
      = ∫⁻ x in U, ENNReal.ofReal (a x) ∂volume := by
    rw [volumeAverage,
      ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hv0 hvt),
      ENNReal.ofReal_toReal hvt, hI,
      mul_comm ((volume U)⁻¹) (∫⁻ x in U, ENNReal.ofReal (a x) ∂volume),
      ENNReal.inv_mul_cancel_right hv0 hvt]
  unfold weightedMeasure
  rw [withDensity_apply _ hU, ← key]

/-- Convert a volume-averaged energy bound using! the scalar coefficient price. -/
theorem goodCube_unnormalize_sobolev_bound {mass vol I : ℝ≥0∞}
    {avg k E price r : ℝ} (havg : 0 < avg) (hv0 : vol ≠ 0) (hvt : vol ≠ ⊤)
    (hmass : mass = ENNReal.ofReal avg * vol) (hr : 0 ≤ r)
    (hE : 0 ≤ E) (hprice : k * avg ≤ price)
    (h : (mass⁻¹ * I) ^ r ≤ ENNReal.ofReal (k * (vol.toReal⁻¹ * E))) :
    I ^ r ≤ ENNReal.ofReal (price * E) * mass ^ (r - 1) := by
  have hmass0 : mass ≠ 0 := by
    rw [hmass]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr havg) hv0
  have hmasst : mass ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvt
  have hmtR : mass.toReal = avg * vol.toReal := by
    rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal havg.le]
  have hmassRPos : 0 < mass.toReal := ENNReal.toReal_pos hmass0 hmasst
  have hkey : ENNReal.ofReal (k * (vol.toReal⁻¹ * E))
      = ENNReal.ofReal (k * avg * E) * mass⁻¹ := by
    have hkeyR : k * (vol.toReal⁻¹ * E) = (k * avg * E) / mass.toReal := by
      rw [hmtR]
      field_simp [havg.ne', (ENNReal.toReal_pos hv0 hvt).ne']
    rw [hkeyR, ENNReal.ofReal_div_of_pos hmassRPos, ENNReal.ofReal_toReal hmasst,
      div_eq_mul_inv]
  have hstep : (mass⁻¹ * I) ^ r ≤ ENNReal.ofReal (k * avg * E) * mass⁻¹ := by
    rw [← hkey]
    exact h
  refine le_trans (goodCube_unnormalize_power hmass0 hmasst hr hstep) ?_
  exact mul_le_mul_left
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hprice hE)) _

/-- A normalized cutoff Sobolev bound and its clock price give the v4 display. -/
theorem goodCube_sobolevDisplay_cutoff_of_normalized {d : ℕ}
    (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (Q : Cube d) (hQ : 0 < Q.2) {p A k : ℝ} {clock : ℝ → ℝ}
    (hp : 0 < p) (hA : 0 ≤ A)
    (hprice : k * volumeAverage (cubeSet Q) (aCutoff M L omega) ≤ A * clock Q.2)
    (hnorm : ∀ f : H10Function (cubeSet Q),
      (ENNReal.ofReal ((volumeAverage (cubeSet Q) (aCutoff M L omega))⁻¹) *
        (volume (cubeSet Q))⁻¹ * ∫⁻ x in cubeSet Q,
          ENNReal.ofReal (|f.toH1Function.toFun x| ^ p * aCutoff M L omega x)) ^ (2 / p) ≤
        ENNReal.ofReal (k * volumeAverage (cubeSet Q) (fun x =>
          aCutoff M L omega x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)))) :
    GoodCubeSobolevDisplay (aCutoff M L omega) p A clock Q := by
  have hUmeas : MeasurableSet (cubeSet Q) := measurableSet_cubeSet Q
  have hvol : volume (cubeSet Q) = ENNReal.ofReal (Q.2 ^ d) := volume_cubeSet hQ.le
  have hvol0 : volume (cubeSet Q) ≠ 0 := by
    rw [hvol]; exact ENNReal.ofReal_ne_zero_iff.2 (pow_pos hQ d)
  have hvolT : volume (cubeSet Q) ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  have hint : IntegrableOn (aCutoff M L omega) (cubeSet Q) volume :=
    ((continuous_aCutoff M L omega).continuousOn.integrableOn_compact
      (isBounded_centeredAxisCube Q.1 Q.2).isCompact_closure).mono_set subset_closure
  have hnn : ∀ᵐ x ∂(volume.restrict (cubeSet Q)), 0 ≤ aCutoff M L omega x :=
    ae_of_all _ (fun x => le_of_lt (aCutoff_pos M L omega x))
  have hmass : weightedMeasure (aCutoff M L omega) (cubeSet Q)
      = ENNReal.ofReal (volumeAverage (cubeSet Q) (aCutoff M L omega)) * volume (cubeSet Q) :=
    goodCube_weightedMeasure_eq_volume_mul_average hUmeas hvol0 hvolT hint hnn
  have hmass08 := goodCube_weightedMeasure_aCutoff_ne_zero_ne_top M L omega Q hQ
  have havgpos : 0 < volumeAverage (cubeSet Q) (aCutoff M L omega) := by
    by_contra hcon
    push Not at hcon
    exact hmass08.1 (by rw [hmass, ENNReal.ofReal_eq_zero.2 hcon, zero_mul])
  have hmassinv : (weightedMeasure (aCutoff M L omega) (cubeSet Q))⁻¹
      = ENNReal.ofReal ((volumeAverage (cubeSet Q) (aCutoff M L omega))⁻¹)
        * (volume (cubeSet Q))⁻¹ := by
    rw [hmass, ENNReal.mul_inv (Or.inl ((ENNReal.ofReal_ne_zero_iff).2 havgpos)) (Or.inr hvol0),
      ENNReal.ofReal_inv_of_pos havgpos]
  have hameas : Measurable (aCutoff M L omega) := (continuous_aCutoff M L omega).measurable
  intro f
  have hE : 0 ≤ energy (aCutoff M L omega) (cubeSet Q) f.toH1Function := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (aCutoff_pos M L omega x).le
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (f.toH1Function.grad x i)))
  have havgE : volumeAverage (cubeSet Q) (fun x => aCutoff M L omega x *
        vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
      = (volume (cubeSet Q)).toReal⁻¹ *
        energy (aCutoff M L omega) (cubeSet Q) f.toH1Function := rfl
  have hkey : (∫⁻ x in cubeSet Q,
      ENNReal.ofReal (|f.toH1Function.toFun x| ^ p * aCutoff M L omega x)) ^ ((2:ℝ) / p)
      ≤ ENNReal.ofReal ((A * clock Q.2) *
          energy (aCutoff M L omega) (cubeSet Q) f.toH1Function)
        * (weightedMeasure (aCutoff M L omega) (cubeSet Q)) ^ ((2:ℝ) / p - 1) := by
    refine goodCube_unnormalize_sobolev_bound (r := (2:ℝ) / p) havgpos hvol0 hvolT hmass
      (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hp.le) hE hprice ?_
    rw [hmassinv, ← havgE]
    exact hnorm f
  rw [goodCube_lpSq_eq_weighted_power hUmeas hameas f.toH1Function.toFun hp]
  refine hkey.trans_eq ?_
  rw [show (A * clock Q.2) * energy (aCutoff M L omega) (cubeSet Q) f.toH1Function =
      A * (clock Q.2 * energy (aCutoff M L omega) (cubeSet Q) f.toH1Function) by ring,
    ENNReal.ofReal_mul hA, show (2 : ℝ) / p - 1 = -(1 - 2 / p) by ring]
  ac_rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
