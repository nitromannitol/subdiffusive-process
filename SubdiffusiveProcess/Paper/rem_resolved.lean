module

public import SubdiffusiveProcess.Paper.rem_resolved_strata
public import SubdiffusiveProcess.Paper.rem_resolved_meshes
public import SubdiffusiveProcess.Main.InfraredAdmissible
public import SubdiffusiveProcess.Paper.rem_resolved_microscopic
public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.rem_resolved_eps_power
public import SubdiffusiveProcess.Paper.lane4_smoothed_neumann_source_scaling
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Paper.prop_folded_iteration

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

namespace Paper

/-- The coordinate cube of side `r` centred at `x` is measurable. -/
theorem aux_rem_resolved_cube_meas {d : ℕ} (x : SpatialCoordinates d) (r : ℝ) :
    MeasurableSet {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} := by
  have h : {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} =
      ⋂ i : Fin d, {y : SpatialCoordinates d | |y i - x i| < r / 2} := by
    ext y; simp
  rw [h]
  exact MeasurableSet.iInter fun i =>
    (isOpen_lt (((continuous_apply i).sub continuous_const).abs) continuous_const).measurableSet

/-- A sup-metric ball of radius `r` sits in the coordinate cube of side `2 r`. -/
theorem aux_rem_resolved_ball_sub_cube {d : ℕ} (x : SpatialCoordinates d) (r : ℝ)
    (S : Set (SpatialCoordinates d)) :
    Metric.ball x r ∩ S ⊆ {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < 2 * r / 2} := by
  intro y hy i
  have h1 : dist (y i) (x i) ≤ dist y x := dist_le_pi_dist y x i
  have h2 : dist y x < r := hy.1
  rw [Real.dist_eq] at h1
  have : 2 * r / 2 = r := by ring
  rw [this]
  exact lt_of_le_of_lt h1 h2

/-- A mean-zero Neumann solution forces the compatibility `∫_Q F = 0`: test with the constant `1`. -/
theorem aux_rem_resolved_neumann_mean_zero {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (F : SpatialCoordinates d → ℝ)
    (u : meanZeroSobolevGraph (unitNeumannCube d)) (hsol : SolvesNeumann a F u) :
    (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), F y) = 0 := by
  have hΩ : Bornology.IsBounded (unitNeumannCube d : Set (SpatialCoordinates d)) :=
    centeredCube_isBounded _ one_pos
  have h := hsol (affineSobolev hΩ 0 1)
  have hL : sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d))
      ((affineSobolev hΩ 0 1 : weakSobolevGraph (unitNeumannCube d)) :
        SobolevData (unitNeumannCube d)) = 0 := by
    rw [sobolevCoefficientForm_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hz : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val x * ((u : SobolevData (unitNeumannCube d)).2 i x *
          ((affineSobolev hΩ 0 1 : weakSobolevGraph (unitNeumannCube d)) :
            SobolevData (unitNeumannCube d)).2 i x) = 0 := by
      filter_upwards [domainConstantL2_coeFn (Ω := unitNeumannCube d) ((0 : Fin d → ℝ) i)]
        with x hx
      change a.val x * ((u : SobolevData (unitNeumannCube d)).2 i x *
        (domainConstantL2 (Ω := unitNeumannCube d) ((0 : Fin d → ℝ) i) :
          SpatialCoordinates d → ℝ) x) = 0
      rw [hx]; simp
    rw [integral_congr_ae hz, integral_zero]
  have hR : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      F x * ((affineSobolev hΩ 0 1 : weakSobolevGraph (unitNeumannCube d)) :
        SobolevData (unitNeumannCube d)).1 x) =
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x := by
    apply integral_congr_ae
    filter_upwards [affineL2_coeFn hΩ 0 1] with x hx
    change F x * (affineL2 hΩ 0 1 : SpatialCoordinates d → ℝ) x = F x
    rw [hx]
    simp [affineSlope]
  rw [← hR, ← h, hL]

/-- An a.e.-bounded a.e.-measurable source has a measurable modification bounded everywhere. -/
theorem aux_rem_resolved_clamp {d : ℕ} (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (hf : AEMeasurable f (volume.restrict S))
    (Kf : ℝ) (hKf : 0 ≤ Kf) (hb : ∀ᵐ y ∂volume.restrict S, |f y| ≤ Kf) :
    ∃ g : SpatialCoordinates d → ℝ, Measurable g ∧ (∀ y, |g y| ≤ Kf) ∧
      g =ᵐ[volume.restrict S] f := by
  refine ⟨fun y => max (-Kf) (min Kf (hf.mk f y)), ?_, ?_, ?_⟩
  · exact measurable_const.max (measurable_const.min hf.measurable_mk)
  · intro y
    refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · filter_upwards [hf.ae_eq_mk, hb] with y h1 h2
    rw [← h1]
    have h3 := abs_le.mp h2
    rw [min_eq_right h3.2, max_eq_right h3.1]

/-- The Neumann equation only sees the source through `∫_Q F ψ`. -/
theorem aux_rem_resolved_solves_congr {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (f g : SpatialCoordinates d → ℝ)
    (hfg : g =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] f)
    (u : meanZeroSobolevGraph (unitNeumannCube d)) (hsol : SolvesNeumann a f u) :
    SolvesNeumann a g u := by
  intro ψ
  rw [hsol ψ]
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- The microscopic `gamma` of a continuous representative is the actual local energy. -/
theorem aux_rem_resolved_gamma_eq {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (v : SobolevData (unitNeumannCube d)) (x : SpatialCoordinates d) (r : ℝ) :
    (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, (v.2 i y) ^ 2) =
      localGradientEnergy a (aux_rem_resolved_cube_meas x r) (sobolevGradient v) := by
  rw [← aux_rem_resolved_meshes_energy_eq_local a (sobolevGradient v) _
    (aux_rem_resolved_cube_meas x r)]
  apply integral_congr_ae
  have h := ae_restrict_of_ae_restrict_of_subset
    (Set.inter_subset_right (s := {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2})
      (t := (unitNeumannCube d : Set (SpatialCoordinates d)))) haA
  filter_upwards [h] with y hy
  rw [hy]
  rfl

/-- The cutoff wavelength as a real power. -/
theorem aux_rem_resolved_zpow_eq_rpow (N : ℕ) :
    (3 : ℝ) ^ (-(N : ℤ)) = (3 : ℝ) ^ (-(N : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, zpow_neg, zpow_natCast]

/-- Pure real combination of the large-scale and matched microscopic estimates. -/
theorem aux_rem_resolved_arith
    (L : ℝ → ℝ) (Lb t t1 Cm Cmic eps U V DN mN SN E Eform Kf dd r : ℝ)
    (htt1 : t ≤ t1) (hCm : 0 ≤ Cm) (hCmic : 0 < Cmic)
    (heps : 0 < eps) (hU : 0 ≤ U) (hV : 0 ≤ V) (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hSN : mN⁻¹ ≤ SN) (hE : 0 ≤ E) (hEE : E ≤ Eform) (hr : 0 < r) (hr1 : r ≤ 1)
    (hmono : ∀ r1 r2 : ℝ, 0 < r1 → r1 ≤ r2 → L r1 ≤ L r2)
    (hball : Lb ≤ L (2 * r))
    (hmac : ∀ r' : ℝ, eps ≤ r' → L r' ≤ Cm * U * r' ^ t1 * (E + V * Kf ^ 2))
    (hmic : ∀ Kmac : ℝ, 0 ≤ Kmac → L (Cmic * eps) ≤ Kmac * eps ^ t1 →
        ∀ s : ℝ, 0 < s → s ≤ eps →
          L s ≤ Cmic * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ (dd + 2 - t)) * s ^ t) :
    Lb ≤ (Cm * 2 ^ t1 * (U * (1 + V)) +
      Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 * ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) +
        SN * eps ^ (dd + 2 - t))) * (Eform + Kf ^ 2) * r ^ t := by
  have hW : 0 ≤ U * (1 + V) := mul_nonneg hU (by linarith)
  have hX : 0 ≤ Eform + Kf ^ 2 := by nlinarith [sq_nonneg Kf]
  have hEV : E + V * Kf ^ 2 ≤ (1 + V) * (Eform + Kf ^ 2) := by
    nlinarith [sq_nonneg Kf, mul_nonneg hV (le_trans hE hEE)]
  have hEVnn : 0 ≤ E + V * Kf ^ 2 := by nlinarith [sq_nonneg Kf]
  have hSN0 : 0 ≤ SN := le_trans (inv_pos.mpr hmN).le hSN
  have hrt : 0 ≤ r ^ t := (Real.rpow_pos_of_pos hr t).le
  have h2t1 : 0 ≤ (2 : ℝ) ^ t1 := (Real.rpow_pos_of_pos (by norm_num) t1).le
  have h2t : 0 ≤ (2 : ℝ) ^ t := (Real.rpow_pos_of_pos (by norm_num) t).le
  have hC'1 : (1 : ℝ) ≤ max Cmic 1 := le_max_right _ _
  have hC'0 : 0 < max Cmic 1 := lt_of_lt_of_le one_pos hC'1
  have hC't1 : 0 ≤ (max Cmic 1) ^ t1 := (Real.rpow_pos_of_pos hC'0 t1).le
  have hDt : 0 ≤ (1 + DN) ^ t := (Real.rpow_pos_of_pos (by linarith) t).le
  have het : 0 ≤ eps ^ (t1 - t) := (Real.rpow_pos_of_pos heps _).le
  have hed : 0 ≤ eps ^ (dd + 2 - t) := (Real.rpow_pos_of_pos heps _).le
  have hA1 : 0 ≤ Cm * 2 ^ t1 * (U * (1 + V)) := by positivity
  have hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
      ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t)) := by
    have := hCmic.le
    positivity
  rcases le_or_gt eps (2 * r) with hcase | hcase
  · -- large scales
    have h1 := hmac (2 * r) hcase
    have h2r : (2 * r) ^ t1 = 2 ^ t1 * r ^ t1 := Real.mul_rpow (by norm_num) hr.le
    have hrr : r ^ t1 ≤ r ^ t := Real.rpow_le_rpow_of_exponent_ge hr hr1 htt1
    have h3 : Cm * U * (2 * r) ^ t1 * (E + V * Kf ^ 2) ≤
        Cm * 2 ^ t1 * (U * (1 + V)) * (Eform + Kf ^ 2) * r ^ t := by
      rw [h2r]
      calc Cm * U * (2 ^ t1 * r ^ t1) * (E + V * Kf ^ 2)
          ≤ Cm * U * (2 ^ t1 * r ^ t) * ((1 + V) * (Eform + Kf ^ 2)) := by
            gcongr
        _ = Cm * 2 ^ t1 * (U * (1 + V)) * (Eform + Kf ^ 2) * r ^ t := by ring
    have h4 : Cm * 2 ^ t1 * (U * (1 + V)) * (Eform + Kf ^ 2) * r ^ t ≤
        (Cm * 2 ^ t1 * (U * (1 + V)) +
          Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
            ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t))) *
          (Eform + Kf ^ 2) * r ^ t := by
      have h5 := mul_nonneg (mul_nonneg hA2 hX) hrt
      have h6 : (Cm * 2 ^ t1 * (U * (1 + V)) +
          Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
            ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t))) *
          (Eform + Kf ^ 2) * r ^ t =
          Cm * 2 ^ t1 * (U * (1 + V)) * (Eform + Kf ^ 2) * r ^ t +
          Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
            ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t)) *
          (Eform + Kf ^ 2) * r ^ t := by ring
      rw [h6]
      linarith
    linarith
  · -- microscopic scales
    have hKex : ∃ Kmac : ℝ, Kmac = Cm * U * (max Cmic 1) ^ t1 * (E + V * Kf ^ 2) := ⟨_, rfl⟩
    obtain ⟨Kmac, hKmac⟩ := hKex
    have hKmac0 : 0 ≤ Kmac := by
      rw [hKmac]; exact mul_nonneg (mul_nonneg (mul_nonneg hCm hU) hC't1) hEVnn
    have hle1 : Cmic * eps ≤ max Cmic 1 * eps :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) heps.le
    have hle2 : eps ≤ max Cmic 1 * eps := le_mul_of_one_le_left heps.le hC'1
    have hK : L (Cmic * eps) ≤ Kmac * eps ^ t1 := by
      calc L (Cmic * eps) ≤ L (max Cmic 1 * eps) := hmono _ _ (mul_pos hCmic heps) hle1
        _ ≤ Cm * U * (max Cmic 1 * eps) ^ t1 * (E + V * Kf ^ 2) := hmac _ hle2
        _ = Kmac * eps ^ t1 := by
          rw [Real.mul_rpow hC'0.le heps.le, hKmac]; ring
    have h1 := hmic Kmac hKmac0 hK (2 * r) (by linarith) hcase.le
    have h2r : (2 * r) ^ t = 2 ^ t * r ^ t := Real.mul_rpow (by norm_num) hr.le
    have hKm : Kmac ≤ Cm * (max Cmic 1) ^ t1 * (U * (1 + V)) * (Eform + Kf ^ 2) := by
      rw [hKmac]
      calc Cm * U * (max Cmic 1) ^ t1 * (E + V * Kf ^ 2)
          ≤ Cm * U * (max Cmic 1) ^ t1 * ((1 + V) * (Eform + Kf ^ 2)) := by gcongr
        _ = _ := by ring
    have hmK : mN⁻¹ * Kf ^ 2 ≤ SN * (Eform + Kf ^ 2) := by
      have : Kf ^ 2 ≤ Eform + Kf ^ 2 := by linarith
      calc mN⁻¹ * Kf ^ 2 ≤ SN * Kf ^ 2 := mul_le_mul_of_nonneg_right hSN (sq_nonneg _)
        _ ≤ SN * (Eform + Kf ^ 2) := mul_le_mul_of_nonneg_left this hSN0
    have hin : (1 + DN) ^ t * eps ^ (t1 - t) * Kmac + mN⁻¹ * Kf ^ 2 * eps ^ (dd + 2 - t) ≤
        (Cm * (max Cmic 1) ^ t1 * ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) +
          SN * eps ^ (dd + 2 - t)) * (Eform + Kf ^ 2) := by
      calc (1 + DN) ^ t * eps ^ (t1 - t) * Kmac + mN⁻¹ * Kf ^ 2 * eps ^ (dd + 2 - t)
          ≤ (1 + DN) ^ t * eps ^ (t1 - t) *
              (Cm * (max Cmic 1) ^ t1 * (U * (1 + V)) * (Eform + Kf ^ 2)) +
            SN * (Eform + Kf ^ 2) * eps ^ (dd + 2 - t) := by gcongr
        _ = _ := by ring
    have h3 : L (2 * r) ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
        ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t)) *
          (Eform + Kf ^ 2) * r ^ t := by
      calc L (2 * r) ≤ Cmic * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ (dd + 2 - t)) * (2 * r) ^ t := h1
        _ ≤ Cmic * ((Cm * (max Cmic 1) ^ t1 * ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) +
            SN * eps ^ (dd + 2 - t)) * (Eform + Kf ^ 2)) * (2 * r) ^ t := by
          have := hCmic.le
          have : 0 ≤ (2 * r) ^ t := (Real.rpow_pos_of_pos (by linarith) t).le
          gcongr
        _ = _ := by rw [h2r]; ring
    have h4 : Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
        ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t)) *
          (Eform + Kf ^ 2) * r ^ t ≤
        (Cm * 2 ^ t1 * (U * (1 + V)) +
          Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
            ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t))) *
          (Eform + Kf ^ 2) * r ^ t := by
      have h5 := mul_nonneg (mul_nonneg hA1 hX) hrt
      have h6 : (Cm * 2 ^ t1 * (U * (1 + V)) +
          Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
            ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t))) *
          (Eform + Kf ^ 2) * r ^ t =
          Cm * 2 ^ t1 * (U * (1 + V)) * (Eform + Kf ^ 2) * r ^ t +
          Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 *
            ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) + SN * eps ^ (dd + 2 - t)) *
          (Eform + Kf ^ 2) * r ^ t := by ring
      rw [h6]
      linarith
    linarith

/-- The matched-range microscopic Neumann clause of `rem_resolved_microscopic`, read on the actual
local energy of the positive coefficient. -/
theorem aux_rem_resolved_micro_local (d : ℕ) (hd : 2 ≤ d) (W : SmallPerturbationInput d)
    (p1 t t1 : ℝ) (hp1 : 2 ≤ p1) (ht : (d : ℝ) - 1 < t)
    (htt1 : t < t1) (ht1d : t1 < (d : ℝ))
    (htp : t < (d : ℝ) - 2 * (d : ℝ) / p1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ Kmac : ℝ, 0 ≤ Kmac →
        localGradientEnergy a (aux_rem_resolved_cube_meas x (C * eps))
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤ Kmac * eps ^ t1 →
        ∀ r : ℝ, 0 < r → r ≤ eps →
          localGradientEnergy a (aux_rem_resolved_cube_meas x r)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
            C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
              mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t)) * r ^ t := by
  have h := rem_resolved_microscopic d hd W p1 t t1 hp1 ht htt1 ht1d htp
  rcases h with ⟨C, c, hC, _hc, _hc16, hdet, _hstat⟩
  refine ⟨C, hC, ?_⟩
  intro eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb u hsol x hx Kmac hKmac
    hK r hr hre
  have h2 := hdet eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb
  rcases h2 with ⟨_, hneu, _⟩
  have hK' : (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < C * eps / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤
      Kmac * eps ^ t1 := by
    rw [aux_rem_resolved_gamma_eq a A haA]; exact hK
  have h3 := (hneu u hsol).2 Kmac hKmac x hx hK' r hr hre
  beta_reduce at h3
  rw [aux_rem_resolved_gamma_eq a A haA] at h3
  exact h3

/-- Three-term moment bound, transferred down to any smaller listed order. -/
theorem aux_rem_resolved_three_term_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p A1 A2 A3 BW B : ℝ) (hp : 1 ≤ p) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hBW : 0 ≤ BW) (hB : 0 ≤ B)
    (W T1 T2 : Ω → ℝ)
    (hW : AEStronglyMeasurable W P) (hT1 : AEStronglyMeasurable T1 P)
    (hT2 : AEStronglyMeasurable T2 P)
    (hWb : eLpNorm W (ENNReal.ofReal p) P ≤ ENNReal.ofReal BW)
    (hT1b : eLpNorm T1 (ENNReal.ofReal p) P ≤ ENNReal.ofReal B)
    (hT2b : eLpNorm T2 (ENNReal.ofReal p) P ≤ ENNReal.ofReal B)
    (s : ℝ) (hsp : s ≤ p) :
    MemLp (fun om => A1 * W om + A2 * T1 om + A3 * T2 om) (ENNReal.ofReal s) P ∧
    eLpNorm (fun om => A1 * W om + A2 * T1 om + A3 * T2 om) (ENNReal.ofReal s) P ≤
      ENNReal.ofReal (A1 * BW + A2 * B + A3 * B) := by
  have hmW : AEStronglyMeasurable (fun om => A1 * W om) P := aestronglyMeasurable_const.mul hW
  have hmT1 : AEStronglyMeasurable (fun om => A2 * T1 om) P := aestronglyMeasurable_const.mul hT1
  have hmT2 : AEStronglyMeasurable (fun om => A3 * T2 om) P := aestronglyMeasurable_const.mul hT2
  have hm12 : AEStronglyMeasurable (fun om => A1 * W om + A2 * T1 om) P := hmW.add hmT1
  have hmeas : AEStronglyMeasurable (fun om => A1 * W om + A2 * T1 om + A3 * T2 om) P :=
    hm12.add hmT2
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hsc : ∀ (A : ℝ) (hA : 0 ≤ A) (F : Ω → ℝ) (BF : ℝ) (hBF : 0 ≤ BF),
      eLpNorm F (ENNReal.ofReal p) P ≤ ENNReal.ofReal BF →
      eLpNorm (fun om => A * F om) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (A * BF) := by
    intro A hA F BF hBF hF
    rw [aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm P p A hA F, ENNReal.ofReal_mul hA]
    gcongr
  have hbound : eLpNorm (fun om => A1 * W om + A2 * T1 om + A3 * T2 om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (A1 * BW + A2 * B + A3 * B) := by
    have h12 : eLpNorm (fun om => A1 * W om + A2 * T1 om) (ENNReal.ofReal p) P ≤
        eLpNorm (fun om => A1 * W om) (ENNReal.ofReal p) P +
          eLpNorm (fun om => A2 * T1 om) (ENNReal.ofReal p) P := eLpNorm_add_le hp1
    have h123 : eLpNorm (fun om => A1 * W om + A2 * T1 om + A3 * T2 om) (ENNReal.ofReal p) P ≤
        eLpNorm (fun om => A1 * W om + A2 * T1 om) (ENNReal.ofReal p) P +
          eLpNorm (fun om => A3 * T2 om) (ENNReal.ofReal p) P := eLpNorm_add_le hp1
    calc eLpNorm (fun om => A1 * W om + A2 * T1 om + A3 * T2 om) (ENNReal.ofReal p) P
        ≤ eLpNorm (fun om => A1 * W om) (ENNReal.ofReal p) P +
            eLpNorm (fun om => A2 * T1 om) (ENNReal.ofReal p) P +
            eLpNorm (fun om => A3 * T2 om) (ENNReal.ofReal p) P := by
          refine h123.trans ?_
          gcongr
      _ ≤ ENNReal.ofReal (A1 * BW) + ENNReal.ofReal (A2 * B) + ENNReal.ofReal (A3 * B) := by
          gcongr
          · exact hsc A1 hA1 W BW hBW hWb
          · exact hsc A2 hA2 T1 B hB hT1b
          · exact hsc A3 hA3 T2 B hB hT2b
      _ = ENNReal.ofReal (A1 * BW + A2 * B + A3 * B) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
  have hbs : eLpNorm (fun om => A1 * W om + A2 * T1 om + A3 * T2 om) (ENNReal.ofReal s) P ≤
      ENNReal.ofReal (A1 * BW + A2 * B + A3 * B) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hsp)).trans hbound
  exact ⟨lt_of_le_of_lt hbs ENNReal.ofReal_lt_top, hbs⟩

/-- Hölder for the large-scale factor `U (1 + V)`. -/
theorem aux_rem_resolved_UV_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q Cp : ℝ) (hq : 1 ≤ q) (hCp : 0 ≤ Cp) (U V : Ω → ℝ)
    (hU : MemLp U (ENNReal.ofReal (2 * q)) P) (hV : MemLp V (ENNReal.ofReal (2 * q)) P)
    (hUb : eLpNorm U (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cp)
    (hVb : eLpNorm V (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cp) :
    MemLp (fun om => U om * (1 + V om)) (ENNReal.ofReal q) P ∧
    eLpNorm (fun om => U om * (1 + V om)) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (Cp * (1 + Cp)) := by
  have h2q : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * q) := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * q by linarith)
  have hV1 : MemLp (fun om => (1 : ℝ) + V om) (ENNReal.ofReal (2 * q)) P := by
    have hconst : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 * q)) P := memLp_const 1
    simpa only [Pi.add_apply] using! hconst.add hV
  have hconst_norm : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 * q)) P = 1 := by
    rw [eLpNorm_const _ (by simp [ENNReal.ofReal_eq_zero]; linarith) (NeZero.ne P)]
    simp
  have hV1b : eLpNorm (fun om => (1 : ℝ) + V om) (ENNReal.ofReal (2 * q)) P ≤
      ENNReal.ofReal (1 + Cp) := by
    calc
      _ ≤ eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 * q)) P +
          eLpNorm V (ENNReal.ofReal (2 * q)) P := by
            simpa only [Pi.add_apply] using!
              (eLpNorm_add_le h2q)
      _ ≤ 1 + ENNReal.ofReal Cp := by rw [hconst_norm]; gcongr
      _ = ENNReal.ofReal (1 + Cp) := by
          rw [ENNReal.ofReal_add (by norm_num) hCp]; norm_num
  have hprod := aux_rem_resolved_microscopic_product_lq_bound P q (2 * q) (by linarith) le_rfl
    U (fun om => 1 + V om) hU hV1
  have hb : eLpNorm (fun om => U om * (1 + V om)) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (Cp * (1 + Cp)) := by
    calc _ ≤ eLpNorm U (ENNReal.ofReal (2 * q)) P *
          eLpNorm (fun om => (1 : ℝ) + V om) (ENNReal.ofReal (2 * q)) P := hprod
      _ ≤ ENNReal.ofReal Cp * ENNReal.ofReal (1 + Cp) := mul_le_mul' hUb hV1b
      _ = ENNReal.ofReal (Cp * (1 + Cp)) := (ENNReal.ofReal_mul hCp).symm
  exact ⟨lt_of_le_of_lt hb ENNReal.ofReal_lt_top, hb⟩

/-- The rate budget: small disorder keeps the extremes rate below the matched gain. -/
theorem aux_rem_resolved_rate (Cd Cp rmax δ : ℝ) (hCd : 0 < Cd) (hCp : 0 < Cp)
    (hrmax : 0 < rmax) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδr : δ ≤ rmax / (2 * (Cd + Cp))) :
    0 ≤ Cd * δ + Cp * δ ^ 2 ∧ Cd * δ + Cp * δ ^ 2 < rmax := by
  refine ⟨by positivity, ?_⟩
  have h1 : δ ^ 2 ≤ δ := by nlinarith
  have h2 : Cd * δ + Cp * δ ^ 2 ≤ (Cd + Cp) * δ := by nlinarith
  have h3 : (Cd + Cp) * δ ≤ rmax / 2 := by
    have hpos : 0 < 2 * (Cd + Cp) := by positivity
    rw [le_div_iff₀ hpos] at hδr
    nlinarith
  linarith

/-- Regrouping of the random constant into its three moment pieces. -/
theorem aux_rem_resolved_K_expand (Cm t1 Cmic t W DN e1 SN e2 : ℝ) :
    Cm * 2 ^ t1 * W + Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1 * ((1 + DN) ^ t * e1 * W) +
        SN * e2) =
      (Cm * 2 ^ t1) * W + (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * ((1 + DN) ^ t * e1 * W) +
        (Cmic * 2 ^ t) * (SN * e2) := by
  ring

/-- Local energy on `Q` is at most the full coefficient energy. -/
theorem aux_rem_resolved_local_le_form {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (u : SobolevData (unitNeumannCube d))
    {S : Set (SpatialCoordinates d)} (hS : MeasurableSet S) :
    localGradientEnergy a hS (sobolevGradient u) ≤ sobolevCoefficientForm a u u :=
  localGradientEnergy_le a hS (sobolevGradient u)

/-- The frozen first conjunct at one sample and one cutoff, from the large-scale mesh estimate
and the matched-range microscopic estimate. -/
theorem aux_rem_resolved_first {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d))
    (t t1 Cm Cmic eps U V DN mN SN : ℝ)
    (htt1 : t ≤ t1) (hCm : 0 ≤ Cm) (hCmic : 0 < Cmic) (heps : 0 < eps)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hDN : 0 ≤ DN) (hmN : 0 < mN) (hSN : mN⁻¹ ≤ SN)
    (hmic : ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ Kmac : ℝ, 0 ≤ Kmac →
        localGradientEnergy a (aux_rem_resolved_cube_meas x (Cmic * eps))
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤ Kmac * eps ^ t1 →
        ∀ r : ℝ, 0 < r → r ≤ eps →
          localGradientEnergy a (aux_rem_resolved_cube_meas x r)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
            Cmic * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
              mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t)) * r ^ t)
    (hmac : ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ r : ℝ, eps ≤ r →
        localGradientEnergy a (aux_rem_resolved_cube_meas x r)
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
          Cm * U * r ^ t1 *
            (localGradientEnergy a (unitNeumannCube d).isOpen.measurableSet
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) + V * Kf ^ 2)) :
    ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
    ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
    ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
    ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      localGradientEnergy a
          (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
        ((Cm * 2 ^ t1) * (U * (1 + V)) +
          (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
            ((1 + DN) ^ t * eps ^ (t1 - t) * (U * (1 + V))) +
          (Cmic * 2 ^ t) * (SN * eps ^ ((d : ℝ) + 2 - t))) *
          (sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d))
            (u : SobolevData (unitNeumannCube d)) + Kf ^ 2) * r ^ t := by
  intro f hf Kf hKf hfb hmean u hsol x hx r hr hr1
  have hcl := aux_rem_resolved_clamp (unitNeumannCube d : Set (SpatialCoordinates d)) f hf Kf hKf hfb
  rcases hcl with ⟨g, hgm, hgb, hgf⟩
  have hsolg := aux_rem_resolved_solves_congr a f g hgf u hsol
  set G := sobolevGradient (u : SobolevData (unitNeumannCube d)) with hG
  let L : ℝ → ℝ := fun s => localGradientEnergy a (aux_rem_resolved_cube_meas x s) G
  have hmono : ∀ r1 r2 : ℝ, 0 < r1 → r1 ≤ r2 → L r1 ≤ L r2 := by
    intro r1 r2 _ h12
    refine Lane3.localGradientEnergy_mono a _ _ ?_ G
    intro y hy i
    exact lt_of_lt_of_le (hy i) (by linarith)
  have hball : localGradientEnergy a
      (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet) G ≤ L (2 * r) :=
    Lane3.localGradientEnergy_mono a _ _ (aux_rem_resolved_ball_sub_cube x r _) G
  have hE := localGradientEnergy_nonneg a (unitNeumannCube d).isOpen.measurableSet G
  have hEE := aux_rem_resolved_local_le_form a (u : SobolevData (unitNeumannCube d))
    (unitNeumannCube d).isOpen.measurableSet
  have hres := aux_rem_resolved_arith L _ t t1 Cm Cmic eps U V DN mN SN _ _ Kf (d : ℝ) r htt1 hCm
    hCmic heps hU hV hDN hmN hSN hE hEE hr hr1 hmono hball
    (fun r' hr' => hmac f hf Kf hKf hfb hmean u hsol x hx r' hr')
    (fun Kmac hKmac hK s hs hse => hmic g hgm Kf hKf (fun y _ => hgb y) u hsolg x hx Kmac hKmac hK
      s hs hse)
  rw [aux_rem_resolved_K_expand] at hres
  exact hres

/-- The face bump is continuous. -/
theorem aux_rem_resolved_faceBump_continuous {d : ℕ} (rho : ℝ → ℝ) (hrho : Continuous rho)
    (pvec : Fin d → ℝ) (eps : ℝ) : Continuous (faceBump rho pvec eps) := by
  unfold faceBump
  refine continuous_finset_sum _ fun i _ => ?_
  refine continuous_const.mul ?_
  refine (continuous_const.mul (hrho.comp ?_)).sub (continuous_const.mul (hrho.comp ?_))
  · exact (continuous_const.sub (continuous_apply i)).div_const _
  · exact (continuous_apply i).div_const _

/-- The frozen face-bump conjunct follows from the first conjunct with `‖f_ε‖_∞ ≤ Cρ ε⁻¹`. -/
theorem aux_rem_resolved_second {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d)) (Kv t : ℝ)
    (hfirst : ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
        (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
      ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        localGradientEnergy a
            (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
          Kv * (sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d))
            (u : SobolevData (unitNeumannCube d)) + Kf ^ 2) * r ^ t) :
    ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho →
      (∀ tau : ℝ, 0 ≤ rho tau) →
      (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
      (∫ tau, rho tau) = 1 →
    ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ Cρ : ℝ, 0 ≤ Cρ →
      (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ y : SpatialCoordinates d, y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
          |faceBump rho pvec eps y| ≤ Cρ * eps⁻¹) →
    ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
    ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      SolvesNeumann a (faceBump rho pvec eps) v →
    ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      localGradientEnergy a
          (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
        Kv * (sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
          (v : SobolevData (unitNeumannCube d)) + Cρ ^ 2 * eps ^ (-2 : ℝ)) * r ^ t := by
  intro rho hrho _ _ _ pvec _ Cρ hCρ hbump eps heps heps8 v hsol x hx r hr hr1
  have hcont := aux_rem_resolved_faceBump_continuous rho hrho.continuous pvec eps
  have hb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |faceBump rho pvec eps y| ≤ Cρ * eps⁻¹ :=
    ae_restrict_of_forall_mem (unitNeumannCube d).isOpen.measurableSet
      (fun y hy => hbump eps heps heps8 y hy)
  have h := hfirst (faceBump rho pvec eps) hcont.measurable.aemeasurable (Cρ * eps⁻¹)
    (mul_nonneg hCρ (inv_pos.mpr heps).le) hb
    (aux_rem_resolved_neumann_mean_zero a _ v hsol) v hsol x hx r hr hr1
  have hpow : (Cρ * eps⁻¹) ^ 2 = Cρ ^ 2 * eps ^ (-2 : ℝ) := by
    rw [mul_pow, Real.rpow_neg heps.le, Real.rpow_two, inv_pow]
  rw [hpow] at h
  exact h


/-- One sample and one cutoff: the actual cutoff coefficient, its extremes, the mesh estimate and
the microscopic clause give the frozen first conjunct. -/
theorem aux_rem_resolved_sample (d : ℕ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (t t1 t0 Cm Cmic U V DN mN MN : ℝ)
    (htt1 : t ≤ t1) (hCm : 0 ≤ Cm) (hCmic : 0 < Cmic) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hbounds : ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)),
      mN ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ MN)
    (hlog : ∀ x y, x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
          Set (SpatialCoordinates d)) →
        y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
          DN * (3 : ℝ) ^ N * dist x y)
    (hmic : ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / (3 : ℝ) ^ (-(N : ℝ)) * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ Kmac : ℝ, 0 ≤ Kmac →
        localGradientEnergy a (aux_rem_resolved_cube_meas x (Cmic * (3 : ℝ) ^ (-(N : ℝ))))
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
          Kmac * ((3 : ℝ) ^ (-(N : ℝ))) ^ t1 →
        ∀ r : ℝ, 0 < r → r ≤ (3 : ℝ) ^ (-(N : ℝ)) →
          localGradientEnergy a (aux_rem_resolved_cube_meas x r)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
            Cmic * ((1 + DN) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac +
              mN⁻¹ * Kf ^ 2 * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)) * r ^ t)
    (hmac : ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        SolvesNeumann (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
          f u →
      ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ r →
        (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
            (unitNeumannCube d : Set (SpatialCoordinates d)),
          (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y *
            ∑ i : Fin d, (((sobolevGradient (u : SobolevData (unitNeumannCube d))) i :
              SpatialCoordinates d → ℝ) y) ^ 2) ≤
          Cm * U * r ^ (t0 - (t0 - t1)) *
            ((∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)) ∩
                (unitNeumannCube d : Set (SpatialCoordinates d)),
              (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y *
                ∑ i : Fin d, (((sobolevGradient (u : SobolevData (unitNeumannCube d))) i :
                  SpatialCoordinates d → ℝ) y) ^ 2) + V * Kf ^ 2)) :
    ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
    ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
    ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      SolvesNeumann (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
        f u →
    ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      localGradientEnergy
          (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
          (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
        ((Cm * 2 ^ t1) * (U * (1 + V)) +
          (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
            ((1 + DN) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U * (1 + V))) +
          (Cmic * 2 ^ t) * (‖MN + mN⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))) *
          (sobolevCoefficientForm
            (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
            (u : SobolevData (unitNeumannCube d))
            (u : SobolevData (unitNeumannCube d)) + Kf ^ 2) * r ^ t := by
  have heps : 0 < (3 : ℝ) ^ (-(N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  let A : C(SpatialCoordinates d, ℝ) :=
    ⟨cutoffCoefficient M H om N, cutoffCoefficient_continuous M H om N⟩
  have haA : (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A :=
    aux_rem_resolved_meshes_physical_cutoff_bridge_cutoffPositiveCoefficient_ae M H om N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
  have hcl : closure (unitNeumannCube d : Set (SpatialCoordinates d)) =
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
    show closure (Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) =
      Metric.closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)
    exact closure_ball _ (by norm_num)
  have hAK : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      mN ≤ A y ∧ A y ≤ MN := by
    rw [hcl]; exact hbounds
  have hinv : DN / (3 : ℝ) ^ (-(N : ℝ)) = DN * (3 : ℝ) ^ N := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, div_inv_eq_mul]
  have hlog' : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        |Real.log (A y) - Real.log (A z)| ≤ DN / (3 : ℝ) ^ (-(N : ℝ)) * dist y z := by
    rw [hcl, hinv]
    intro y hy z hz
    exact hlog y z hy hz
  have hmM : mN ≤ MN := by
    have hc : (fun _ : Fin d => (1 / 2 : ℝ)) ∈
        (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) :=
      Metric.mem_closedBall_self (by norm_num)
    exact (hbounds _ hc).1.trans (hbounds _ hc).2
  have hSN : mN⁻¹ ≤ ‖MN + mN⁻¹‖ := by
    have h0 : 0 ≤ MN := hmN.le.trans hmM
    rw [Real.norm_eq_abs]
    exact le_abs.mpr (Or.inl (by linarith))
  refine aux_rem_resolved_first _ t t1 Cm Cmic ((3 : ℝ) ^ (-(N : ℝ))) U V DN mN ‖MN + mN⁻¹‖
    htt1 hCm hCmic heps hU hV hDN hmN hSN (hmic _ A haA DN mN MN hDN hmN hAK hlog') ?_
  intro f hf Kf hKf hfb hmean u hsol x hx r hr
  have hr' : (3 : ℝ) ^ (-(N : ℤ)) ≤ r := by rw [aux_rem_resolved_zpow_eq_rpow]; exact hr
  have h := hmac f hf Kf hKf hfb hmean u hsol x hx r hr'
  convert! h using 1 <;> simp only [sub_sub_cancel]
  · simpa using! (aux_rem_resolved_meshes_energy_eq_local
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (sobolevGradient (u : SobolevData _)) _ (aux_rem_resolved_cube_meas x r)).symm
  · congr 2
    simpa using! (aux_rem_resolved_meshes_energy_eq_local
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (sobolevGradient (u : SobolevData _)) _ (unitNeumannCube d).isOpen.measurableSet).symm

/-- Numerical exponents and one moment order covering the finite list. -/
theorem aux_rem_resolved_parameters (d : ℕ) (hd : 2 ≤ d)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht_low : (d : ℝ) - 1 < t) (ht_high : t < (d : ℝ)) :
    ∃ t1 t0 pmax : ℝ,
      0 ≤ t ∧ t < t1 ∧ t1 < (d : ℝ) ∧
      (d : ℝ) - 1 < t0 ∧ t0 < (d : ℝ) ∧
      0 < t0 - t1 ∧ t0 - t1 < t0 - ((d : ℝ) - 1) ∧
      0 < ((d : ℝ) + 2 - t0) / 2 ∧
      ((d : ℝ) + 2 - t0) / 2 < (d : ℝ) + 2 - t0 ∧
      1 ≤ pmax ∧ (∀ i : Fin k, ps i ≤ pmax) ∧
      1 ≤ 2 * pmax * max 1 t ∧ pmax ≤ 2 * pmax * max 1 t ∧
      1 ≤ 2 * (2 * pmax * max 1 t) ∧
      2 * (2 * pmax * max 1 t) ≤
        max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) ∧
      (d : ℝ) <
        max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) := by
  have hdt : 0 < (d : ℝ) - t := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht_nn : 0 ≤ t := by linarith
  -- exponents: t < t1 < t0 < d, eta = t0 - t1, all fixed before disorder
  have hex1 : ∃ t1 : ℝ, t1 = t + ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ := hex1
  have hex0 : ∃ t0 : ℝ, t0 = t + 2 * ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ := hex0
  have htt1 : t < t1 := by rw [ht1]; linarith
  have ht1d : t1 < (d : ℝ) := by rw [ht1]; linarith
  have ht0_low : (d : ℝ) - 1 < t0 := by rw [ht0]; linarith
  have ht0_high : t0 < (d : ℝ) := by rw [ht0]; linarith
  have heta_pos : 0 < t0 - t1 := by rw [ht0, ht1]; linarith
  have heta_lt : t0 - t1 < t0 - ((d : ℝ) - 1) := by rw [ht0, ht1]; linarith
  have hetas_pos : 0 < ((d : ℝ) + 2 - t0) / 2 := by linarith
  have hetas_lt : ((d : ℝ) + 2 - t0) / 2 < (d : ℝ) + 2 - t0 := by linarith
  -- one moment order covering the finite list
  have hexp : ∃ pmax : ℝ, pmax = 1 + ∑ i : Fin k, |ps i| := ⟨_, rfl⟩
  obtain ⟨pmax, hpmax_def⟩ := hexp
  have hsum_nn : 0 ≤ ∑ i : Fin k, |ps i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hpmax : 1 ≤ pmax := by rw [hpmax_def]; linarith
  have hps_le : ∀ i : Fin k, ps i ≤ pmax := by
    intro i
    have h1 : ps i ≤ |ps i| := le_abs_self _
    have h2 : |ps i| ≤ ∑ j : Fin k, |ps j| :=
      Finset.single_le_sum (f := fun j => |ps j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hpmax_def]; linarith
  have hmax1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have hq1 : 1 ≤ 2 * pmax * max 1 t := by nlinarith
  have hpq : pmax ≤ 2 * pmax * max 1 t := by nlinarith
  have hqmesh_p : 1 ≤ 2 * (2 * pmax * max 1 t) := by linarith
  have hqmesh_q : 2 * (2 * pmax * max 1 t) ≤
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) := le_max_left _ _
  have hqmesh_eta : (d : ℝ) <
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) := by
    have h1 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) = (d : ℝ) + 1 := by
      field_simp
    have h2 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) ≤
        max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) heta_pos.le
    linarith
  exact ⟨t1, t0, pmax, ht_nn, htt1, ht1d, ht0_low, ht0_high, heta_pos, heta_lt,
    hetas_pos, hetas_lt, hpmax, hps_le, hq1, hpq, hqmesh_p, hqmesh_q, hqmesh_eta⟩

theorem aux_rem_resolved_adm :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < (d : ℝ) →
    (∀ i : Fin k, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (_Rm : in_responses d M) (Sreg : in_6_16 d M)
      (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ delta0 →
    let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
    let a : ℕ → BilateralField d → PositiveCoefficient Q :=
      fun N omega => cutoffPositiveCoefficient M H omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
    ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
      (∀ N omega, 0 ≤ K N omega) ∧
      (∀ i N,
        MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
      (∀ i N,
        eLpNorm (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (∀ N : ℕ,
          ∀ f : SpatialCoordinates d → ℝ,
            AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
          ∀ Kf : ℝ, 0 ≤ Kf →
            (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
              |f y| ≤ Kf) →
            (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph Q,
            SolvesNeumann (a N omega) f u →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (u : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a N omega)
                    (u : SobolevData Q) (u : SobolevData Q) + Kf ^ 2) * r ^ t) ∧
        (∀ N : ℕ,
          ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho →
            (∀ tau : ℝ, 0 ≤ rho tau) →
            (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
            (∫ tau, rho tau) = 1 →
          ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
          ∀ Cρ : ℝ, 0 ≤ Cρ →
            (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
              ∀ y : SpatialCoordinates d, y ∈ (Q : Set (SpatialCoordinates d)) →
                |faceBump rho pvec eps y| ≤ Cρ * eps⁻¹) →
          ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
          ∀ v : meanZeroSobolevGraph Q,
            SolvesNeumann (a N omega) (faceBump rho pvec eps) v →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (v : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a N omega)
                    (v : SobolevData Q) (v : SobolevData Q) +
                    Cρ ^ 2 * eps ^ (-2 : ℝ)) * r ^ t) := by
  intro d hd _ _ E _P _X _W D t k ps ht_low ht_high hps
  have hdt : 0 < (d : ℝ) - t := sub_pos.mpr ht_high
  obtain ⟨t1, t0, pmax, ht_nn, htt1, ht1d, ht0_low, ht0_high, heta_pos, heta_lt,
    hetas_pos, hetas_lt, hpmax, hps_le, hq1, hpq, hqmesh_p, hqmesh_q, hqmesh_eta⟩ :=
    aux_rem_resolved_parameters d hd t k ps ht_low ht_high
  -- geometric root radius
  have hRpos : (0 : ℝ) < (3 : ℝ) ^ (-7 : ℤ) / 2 := by positivity
  have hRlt : (3 : ℝ) ^ (-7 : ℤ) / 2 < 1 / (100 * 10) := by norm_num
  have hRmem : (3 : ℝ) ^ (-7 : ℤ) / 2 ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) := ⟨-7, rfl⟩
  -- the large-scale common package
  have hM := aux_rem_resolved_meshes_adm d hd 10 ((3 : ℝ) ^ (-7 : ℤ) / 2) t0 (t0 - t1)
    (((d : ℝ) + 2 - t0) / 2) (2 * (2 * pmax * max 1 t))
    (max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1))) (by norm_num) hRpos hRlt hRmem
    ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hqmesh_p hqmesh_q hqmesh_eta
  rcases hM with ⟨J, _, Cstep, c, Cm, delta0m, Cp, Kt, _, _, hCm, hdelta0m, hCp, _, Ccount, Cd,
    _, _, _, Cmom, Crate, _, _, hmesh⟩
  -- the microscopic matched range
  have hp1 : (2 : ℝ) ≤ 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by
    have : 0 ≤ 4 * (d : ℝ) / ((d : ℝ) - t) := by positivity
    linarith
  have htp : t < (d : ℝ) - 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) := by
    have hp1pos : 0 < 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by linarith
    have hkey : 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) < ((d : ℝ) - t) / 2 := by
      rw [div_lt_iff₀ hp1pos]
      have h4 : ((d : ℝ) - t) * (4 * (d : ℝ) / ((d : ℝ) - t)) = 4 * (d : ℝ) := by
        field_simp
      nlinarith
    linarith
  have hml := aux_rem_resolved_micro_local d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hml with ⟨Cmic, hCmic, hmicL⟩
  have hms := rem_resolved_microscopic d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hms with ⟨_, _, _, _, _, _, hstat⟩
  -- extremes of the actual cutoff coefficient on the closed unit cube
  have hXall := aux_lem_extremes_upper d hd
  rcases hXall with ⟨Cde, cde, hCde, hcde, hXz⟩
  have hX := hXz (fun _ => (1 / 2 : ℝ)) 1 one_pos (2 * pmax * max 1 t) hq1
  rcases hX with ⟨Cpe, hCpe, hextM⟩
  -- rate budget
  have hexr : ∃ rmax : ℝ,
      rmax = min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := ⟨_, rfl⟩
  obtain ⟨rmax, hrmax_def⟩ := hexr
  have hrmax : 0 < rmax := by
    rw [hrmax_def]
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) hdt)) ?_
    exact Real.log_pos (by norm_num)
  have hqpos : 0 < 2 * pmax * max 1 t := by linarith
  refine ⟨min (min delta0m (cde / (2 * pmax * max 1 t)))
    (min 1 (rmax / (2 * (Cde + Cpe)))), ?_, ?_⟩
  · refine lt_min (lt_min hdelta0m (div_pos hcde hqpos)) (lt_min one_pos ?_)
    exact div_pos hrmax (by positivity)
  intro M _Rm Sreg _It H hIR hδ Q a
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδm : M.delta ≤ delta0m := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδe : M.delta ≤ cde / (2 * pmax * max 1 t) :=
    hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : M.delta ≤ rmax / (2 * (Cde + Cpe)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrate := aux_rem_resolved_rate Cde Cpe rmax M.delta hCde hCpe hrmax hδpos hδ1 hδr
  rw [hrmax_def] at hrate
  -- instantiate the large-scale package and the extremes on the same sample law
  have hmM := hmesh M E _P _X _Rm Sreg _It D H hIR hδm
  rcases hmM with ⟨_, U, V, _, _, hU0, hV0, hULp, hVLp, hUb, hVb, hae⟩
  have heM := hextM M H hIR hδe
  rcases heM with ⟨De, mlow, mhigh, hDe0, heae, hDeLp, hmLp, hDeb, hmb⟩
  have hW : ∀ N : ℕ,
      MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) := fun N =>
    aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure (2 * pmax * max 1 t) Cp hq1 hCp.le
      (U N) (V N) (hULp N) (hVLp N) (hUb N) (hVb N)
  have hSb : ∀ N : ℕ,
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖)
        (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * Cpe *
        Real.exp ((Cde * M.delta + Cpe * M.delta ^ 2) * (N : ℝ))) := by
    intro N
    have h2 : (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖) =
        fun om => 2 * ‖mhigh N om + (mlow N om)⁻¹‖ := by
      funext om; ring
    have hm := hmb N
    calc _ = ENNReal.ofReal 2 * eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹)
            (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure := by
          rw [h2, aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm _ _ 2 (by norm_num),
            eLpNorm_norm _ (hmLp N).aestronglyMeasurable]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal
            (Cpe * Real.exp ((Cde * M.delta + Cpe * M.delta ^ 2) * (N : ℝ))) := by
          gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num), mul_assoc]
  have hstatM := hstat (BilateralField d) (chaosSampleLaw M).toMeasure pmax hpmax De
    (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖) (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖)
    (fun N om => U N om * (1 + V N om)) Cpe (2 * Cpe) (Cp * (1 + Cp))
    (Cde * M.delta + Cpe * M.delta ^ 2) hCpe.le (by positivity) (by positivity) hrate.1 hrate.2
    (fun N om => ⟨hDe0 N om, norm_nonneg _, norm_nonneg _,
      mul_nonneg (hU0 N om) (by linarith [hV0 N om])⟩)
    (fun N => ⟨hDeLp N, (hmLp N).norm, (hmLp N).norm, (hW N).1⟩)
    hDeb hSb (fun N => (hW N).2)
  rcases hstatM with ⟨B, hB0, hBN⟩
  have hA1 : 0 ≤ Cm * 2 ^ t1 := mul_nonneg hCm.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA3 : 0 ≤ Cmic * 2 ^ t := mul_nonneg hCmic.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1) :=
    mul_nonneg hA3 (mul_nonneg hCm.le
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _).le)
  have hmom : ∀ (i : Fin k) (N : ℕ),
      MemLp (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B) := by
    intro i N
    have hBNN := hBN N
    beta_reduce at hBNN
    have hWm := (hW N).1.aestronglyMeasurable
    have hDt := (aux_rem_resolved_microscopic_one_add_power_memLp (chaosSampleLaw M).toMeasure
      pmax t hpmax ht_nn (De N) (hDe0 N) (hDeLp N)).aestronglyMeasurable
    have hT1m : AEStronglyMeasurable (fun om =>
        (1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om)))
        (chaosSampleLaw M).toMeasure :=
      (hDt.mul aestronglyMeasurable_const).mul hWm
    have hT2m : AEStronglyMeasurable (fun om =>
        ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (chaosSampleLaw M).toMeasure :=
      (hmLp N).norm.aestronglyMeasurable.mul aestronglyMeasurable_const
    have hWb : eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal pmax)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) :=
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans (hW N).2
    exact aux_rem_resolved_three_term_moment (chaosSampleLaw M).toMeasure pmax _ _ _
      (Cp * (1 + Cp)) B hpmax hA1 hA2 hA3 (by positivity) hB0 _ _ _ hWm hT1m hT2m hWb
      hBNN.1 hBNN.2.1 (ps i) (hps_le i)
  refine ⟨fun N om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)),
    fun _ => (Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B, ?_,
    fun i N => (hmom i N).1, fun i N => (hmom i N).2, ?_⟩
  · intro N om
    have h1 : 0 ≤ U N om * (1 + V N om) := mul_nonneg (hU0 N om) (by linarith [hV0 N om])
    have h2 : 0 ≤ (1 + De N om) ^ t := (Real.rpow_pos_of_pos (by linarith [hDe0 N om]) _).le
    have h3 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h4 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h5 := norm_nonneg (mhigh N om + (mlow N om)⁻¹)
    exact add_nonneg (add_nonneg (mul_nonneg hA1 h1) (mul_nonneg hA2 (mul_nonneg (mul_nonneg h2 h3) h1)))
      (mul_nonneg hA3 (mul_nonneg h5 h4))
  · filter_upwards [hae, heae] with om hω1 hω2
    have hfirst := fun N : ℕ => aux_rem_resolved_sample d M H om N t t1 t0 Cm Cmic
      (U N om) (V N om) (De N om) (mlow N om) (mhigh N om) (le_of_lt htt1) hCm.le hCmic
      (hU0 N om) (hV0 N om) (hDe0 N om) (hω2 N).2.1 (hω2 N).2.2 (hω2 N).1
      (hmicL ((3 : ℝ) ^ (-(N : ℝ))) (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)))
      ((hω1 N).2.2.2.2)
    exact ⟨hfirst, fun N => aux_rem_resolved_second (a N om) _ t (hfirst N)⟩



theorem rem_resolved :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < (d : ℝ) →
    (∀ i : Fin k, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (_Rm : in_responses d M) (Sreg : in_6_16 d M)
      (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
    let a : ℕ → BilateralField d → PositiveCoefficient Q :=
      fun N omega => cutoffPositiveCoefficient M H omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
    ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
      (∀ N omega, 0 ≤ K N omega) ∧
      (∀ i N,
        MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
      (∀ i N,
        eLpNorm (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (∀ N : ℕ,
          ∀ f : SpatialCoordinates d → ℝ,
            AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
          ∀ Kf : ℝ, 0 ≤ Kf →
            (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
              |f y| ≤ Kf) →
            (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph Q,
            SolvesNeumann (a N omega) f u →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (u : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a N omega)
                    (u : SobolevData Q) (u : SobolevData Q) + Kf ^ 2) * r ^ t) ∧
        (∀ N : ℕ,
          ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho →
            (∀ tau : ℝ, 0 ≤ rho tau) →
            (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
            (∫ tau, rho tau) = 1 →
          ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
          ∀ Cρ : ℝ, 0 ≤ Cρ →
            (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
              ∀ y : SpatialCoordinates d, y ∈ (Q : Set (SpatialCoordinates d)) →
                |faceBump rho pvec eps y| ≤ Cρ * eps⁻¹) →
          ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
          ∀ v : meanZeroSobolevGraph Q,
            SolvesNeumann (a N omega) (faceBump rho pvec eps) v →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (v : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a N omega)
                    (v : SobolevData Q) (v : SobolevData Q) +
                    Cρ ^ 2 * eps ^ (-2 : ℝ)) * r ^ t) := by
  intro d hd _ _ E _P _X _W D t k ps ht_low ht_high hps
  obtain ⟨delta0, hdelta0, hall⟩ :=
    aux_rem_resolved_adm d hd E _P _X _W D t k ps ht_low ht_high hps
  exact ⟨delta0, hdelta0, fun M Rm Sreg It H hIR hδ =>
    hall M Rm Sreg It H (InfraredAdmissible.of_char hIR) hδ⟩

end Paper
