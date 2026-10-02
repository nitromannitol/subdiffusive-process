import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Paper.tight_scale_covariance
import Mathlib
import Homogenization.Sobolev.W1p.ZeroExtensionGraph
import Homogenization.Sobolev.H1.Algebra.H10Function
import Homogenization.Sobolev.H1.BasicLemmas
import SubdiffusiveProcess.Sobolev.AffineData
import SubdiffusiveProcess.Sobolev.NativeH10
import SubdiffusiveProcess.Paper.lem_finite_source_comparison_trial
import SubdiffusiveProcess.Paper.lem_finite_source_comparison
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
import Mathlib.Probability.Moments.Basic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.NormalizerSwap
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence
import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

-- ===== module HCut.HTransfer =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hcut_coeff_congr (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H H' : BilateralField d → C(SpatialCoordinates d, ℝ)} {om : BilateralField d} (h : H om = H' om)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    cutoffPositiveCoefficient M H om N z hr = cutoffPositiveCoefficient M H' om N z hr := by
  have hCM : cutoffCoefficientCM M H om N z hr = cutoffCoefficientCM M H' om N z hr := by
    ext x
    simp only [cutoffCoefficientCM, ContinuousMap.coe_mk, cutoffCoefficient, cutoffPotential, h]
  unfold cutoffPositiveCoefficient
  congr 1

section
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Two infrared characterizations agree almost surely. -/
lemma aux_hcut_H_ae_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H H' : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (hH' : InfraredCharacterization M H') :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, H om = H' om := by
  filter_upwards [hH.2, hH'.2] with om h1 h2
  exact tendsto_nhds_unique h1 h2

lemma aux_hcut_growthAt_congr (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H H' : BilateralField d → C(SpatialCoordinates d, ℝ)} {om : BilateralField d} (h : H om = H' om)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t alpha : ℝ) (K : ℕ → ℝ)
    (hG : aux_prop_growth_large_root_GrowthAt M H' z r hr t alpha om K) :
    aux_prop_growth_large_root_GrowthAt M H z r hr t alpha om K := by
  unfold aux_prop_growth_large_root_GrowthAt at hG ⊢
  simp_rw [aux_hcut_coeff_congr M h]
  exact hG

end

end Paper
end
end

-- ===== module HCut.CellCoeff =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The environment seen by the level-`n` cell centred at `y`: translate by `y`, then zoom by `3^n`. -/
def aux_hcut_cellEnv (y : SpatialCoordinates d) (n : ℕ) (om : BilateralField d) : BilateralField d :=
  aux_tight_scale_covariance_scaleShift (-(n : ℤ)) (aux_tight_scale_covariance_translate y om)

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hcut_measurePreserving_cellEnv (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (y : SpatialCoordinates d) (n : ℕ) :
    MeasurePreserving (aux_hcut_cellEnv (d := d) y n) (chaosSampleLaw M).toMeasure
      (chaosSampleLaw M).toMeasure :=
  (aux_tight_scale_covariance_measurePreserving_scaleShift M (-(n : ℤ))).comp
    (aux_tight_scale_covariance_measurePreserving_translate M y)

/-- Zooming the cell environment back out by `3^n` recovers the translated environment. -/
lemma aux_hcut_scaleShift_cellEnv (y : SpatialCoordinates d) (n : ℕ) (om : BilateralField d) :
    aux_prop_growth_large_root_scaleShift n (aux_hcut_cellEnv y n om) =
      aux_tight_scale_covariance_translate y om := by
  rw [← aux_tight_scale_covariance_scaleShift_nat, aux_hcut_cellEnv,
    aux_tight_scale_covariance_scaleShift_add, add_neg_cancel, aux_tight_scale_covariance_scaleShift_zero]

/-- Translation covariance of the cutoff coefficient. -/
lemma aux_hcut_ae_coeff_translate (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) (N : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ v : SpatialCoordinates d,
      cutoffCoefficient M H om N (y + v) =
        Real.exp (H om y) * cutoffCoefficient M H (aux_tight_scale_covariance_translate y om) N v := by
  filter_upwards [aux_tight_scale_covariance_ae_density_translate hH y N] with om hom v
  unfold cutoffCoefficient
  have h := hom v
  unfold cutoffSpeedDensity at h
  rw [h]; ring

/-- **Cell coefficient identity**: on the level-`n` cell centred at `y`, `A_N(ω)(y + 3^{-n}x)` equals
`e^{H ω y} · shiftConst(ω')⁻¹ · A_{N-n}(ω')(x)` with `ω' = cellEnv y n ω`. -/
lemma aux_hcut_ae_coeff_cell (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) {n N : ℕ} (hnN : n ≤ N) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x : SpatialCoordinates d,
      cutoffCoefficient M H om N (y + ((3 : ℝ) ^ n)⁻¹ • x) =
        (Real.exp (H om y) * (aux_prop_growth_large_root_shiftConst M n (N - n)
            (aux_hcut_cellEnv y n om))⁻¹) *
          cutoffCoefficient M H (aux_hcut_cellEnv y n om) (N - n) x := by
  have hIR := (aux_hcut_measurePreserving_cellEnv M y n).quasiMeasurePreserving.ae
    (aux_prop_growth_large_root_ae_infrared_scaleShift hH n)
  filter_upwards [aux_hcut_ae_coeff_translate M hH y N, hIR] with om h1 h2 x
  have hpos := aux_prop_growth_large_root_shiftConst_pos M Rm n (N - n) (aux_hcut_cellEnv y n om)
  have hsc := aux_prop_growth_large_root_cutoffCoefficient_scaleShift M H (aux_hcut_cellEnv y n om) n
    (N - n) h2 (aux_prop_growth_large_root_ahom_pos_of M Rm _) (((3 : ℝ) ^ n)⁻¹ • x)
  rw [aux_hcut_scaleShift_cellEnv, Nat.sub_add_cancel hnN, smul_smul,
    mul_inv_cancel₀ (by positivity : ((3 : ℝ) ^ n) ≠ 0), one_smul] at hsc
  rw [h1, hsc]
  field_simp

end Laws

end Paper
end
end

-- ===== module HCut.CellTransfer =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hcut_ball_inter_cell_eq {z x : SpatialCoordinates d} {r rad : ℝ} (hr : 0 < r) (hrad : r ≤ rad)
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Metric.ball x r ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ Metric.ball x r := by
    intro y hy
    change y ∈ Metric.ball z (r / 2) at hy
    change x ∈ Metric.ball z (r / 2) at hx
    rw [Metric.mem_ball] at hx hy ⊢
    calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by rw [dist_comm z x]; exact add_lt_add hy hx
      _ = r := by ring
  rw [Set.inter_eq_right.2 (hsub.trans (Metric.ball_subset_ball hrad)), Set.inter_eq_right.2 hsub]

/-- Real bookkeeping of the zoom-in transfer. -/
lemma aux_hcut_real_small {r rad c K C t : ℝ} {d : ℕ} (hr : 0 < r) (hrad : 0 < rad) (hc : 0 < c)
    (hK : 0 ≤ K) (E : ℝ) (hE : E ≤ K * C ^ 2 * (rad / r) ^ t) :
    r ^ ((d : ℝ) - 2) * (c * E) ≤ c * K * C ^ 2 * r ^ ((d : ℝ) - 2 - t) * rad ^ t := by
  have hsplit : r ^ ((d : ℝ) - 2) * (rad / r) ^ t = r ^ ((d : ℝ) - 2 - t) * rad ^ t := by
    rw [Real.div_rpow hrad.le hr.le, sub_eq_add_neg ((d : ℝ) - 2) t, Real.rpow_add hr, Real.rpow_neg hr.le]
    field_simp
  have hrp : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
  calc r ^ ((d : ℝ) - 2) * (c * E) ≤ r ^ ((d : ℝ) - 2) * (c * (K * C ^ 2 * (rad / r) ^ t)) := by
        gcongr
    _ = c * K * C ^ 2 * (r ^ ((d : ℝ) - 2) * (rad / r) ^ t) := by ring
    _ = c * K * C ^ 2 * r ^ ((d : ℝ) - 2 - t) * rad ^ t := by rw [hsplit]; ring

/-- **Zoom-in growth transfer** (the cell version of `growthAt_transfer_gen`, zero source).  A cube of
side `r ≤ 1` whose coefficient is `c` times the pullback of a unit-cube coefficient `A'` inherits the unit
growth constant with the scale factor `r^{d-2-t}`, against the C² norm `Cfine` of the RESCALED datum. -/
theorem aux_hcut_cell_transfer (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {t : ℝ} (ht : 0 ≤ t)
    (A : PositiveCoefficient (centeredCube z r hr))
    (A' : PositiveCoefficient (centeredCube z0 1 one_pos))
    (c : ℝ) (hc : 0 < c)
    (hcoef : ∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
      (A.val : SpatialCoordinates d → ℝ) (cubeDilation z z0 r x) =
        c * (A'.val : SpatialCoordinates d → ℝ) x)
    (K' : ℝ) (hK' : 0 ≤ K')
    (hG : ∀ (phi1 : SpatialCoordinates d → ℝ) (Cphi1 : ℝ), ContDiff ℝ 2 phi1 →
      c2Norm (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) phi1 ≤ Cphi1 →
      ∀ (b1 u1 : weakSobolevGraph (centeredCube z0 1 one_pos)),
        ((b1 : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] phi1 →
        SolvesDirichlet A' (fun _ => (0 : ℝ)) b1 u1 →
        ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z0 1 one_pos →
          0 < rad → rad ≤ 1 →
          localGradientEnergy A'
              (s := Metric.ball x rad ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter
                (centeredCube z0 1 one_pos).isOpen.measurableSet)
              (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos))) ≤
            K' * Cphi1 ^ 2 * rad ^ t)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi) (Cfine : ℝ)
    (hCfine : c2Norm (closedCube z0 1 one_pos : Set (SpatialCoordinates d))
      (fun x => phi (cubeDilation z z0 r x)) ≤ Cfine)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (htrace : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hsolve : SolvesDirichlet A (fun _ => (0 : ℝ)) b u) :
    ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
      localGradientEnergy A
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        c * K' * Cfine ^ 2 * r ^ ((d : ℝ) - 2 - t) * rad ^ t := by
  obtain ⟨a1, ha1⟩ := Paper.lane4_dilation_coefficient_transport d z z0 r hr one_pos A
  have hscale : ∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
      (a1.val : SpatialCoordinates d → ℝ) x = c * (A'.val : SpatialCoordinates d → ℝ) x := by
    filter_upwards [ha1, hcoef] with x h1 h2
    rw [h1, h2]
  have htr := aux_prop_growth_large_root_dirichlet_transport z z0 r hr A a1 ha1 (fun _ => (0 : ℝ)) 0
    le_rfl measurable_const.aemeasurable (Eventually.of_forall fun x => by simp) phi
    (c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi) hphi le_rfl b u htrace hsolve
  obtain ⟨F1, phi1, b1, u1, hF1def, -, -, hphi1def, hphi1c, -, htrace1, hsolve1,
    -, -, -, henergy⟩ := htr
  have hF1 : F1 = fun _ => (0 : ℝ) := by rw [hF1def]; funext x; simp
  rw [hF1] at hsolve1
  have hsolve' := aux_prop_growth_large_root_solvesDirichlet_scale a1 A' c hc hscale
    (fun _ => (0 : ℝ)) b1 u1 hsolve1
  have hzero : (fun x : SpatialCoordinates d => c⁻¹ * (fun _ => (0 : ℝ)) x) = fun _ => (0 : ℝ) := by
    funext x; simp
  rw [hzero] at hsolve'
  have hphi1eq : phi1 = fun x => phi (cubeDilation z z0 r x) := hphi1def
  have hGu := hG phi1 Cfine hphi1c (by rw [hphi1eq]; exact hCfine) b1 u1 htrace1 hsolve'
  -- the energy at radius `rad ≤ r`
  have hsmall : ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr → 0 < rad →
      rad ≤ r →
      localGradientEnergy A
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        c * K' * Cfine ^ 2 * r ^ ((d : ℝ) - 2 - t) * rad ^ t := by
    intro x rad hx hrad0 hradr
    have hx1 := aux_prop_growth_large_root_cubeDilation_inv_mem_centeredCube z z0 hr hx
    have hTx : cubeDilation z z0 r (cubeDilation z0 z r⁻¹ x) = x :=
      aux_prop_growth_large_root_cubeDilation_inv_left z z0 hr x
    have hρ0 : 0 < rad / r := div_pos hrad0 hr
    have hρ1 : rad / r ≤ 1 := (div_le_one hr).2 hradr
    have hE := henergy (cubeDilation z0 z r⁻¹ x) (rad / r) hρ0
    have hrr : r * (rad / r) = rad := by field_simp
    rw [hTx, hrr] at hE
    have hloc := aux_prop_growth_large_root_localGradientEnergy_scale a1 A' c hscale
      (Metric.isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
      (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos)))
      (s := Metric.ball (cubeDilation z0 z r⁻¹ x) (rad / r) ∩
        (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
    have hGx := hGu (cubeDilation z0 z r⁻¹ x) (rad / r) hx1 hρ0 hρ1
    have hinv : localGradientEnergy A
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) =
        r ^ ((d : ℝ) - 2) * (c * localGradientEnergy A'
          (s := Metric.ball (cubeDilation z0 z r⁻¹ x) (rad / r) ∩
            (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
          (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos)))) := by
      rw [← hloc, hE, ← mul_assoc, ← Real.rpow_add hr]
      norm_num
    rw [hinv]
    exact aux_hcut_real_small hr hrad0 hc hK' _ hGx
  intro x rad hx hrad0 hrad1
  rcases le_or_lt rad r with hradr | hradr
  · exact hsmall x rad hx hrad0 hradr
  · have hset := aux_hcut_ball_inter_cell_eq (z := z) hr hradr.le hx
    have h1 := hsmall x r hx hr le_rfl
    have hK0 : 0 ≤ c * K' * Cfine ^ 2 * r ^ ((d : ℝ) - 2 - t) := by
      have := Real.rpow_nonneg hr.le ((d : ℝ) - 2 - t)
      positivity
    calc localGradientEnergy A
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr)))
        = localGradientEnergy A
          (s := Metric.ball x r ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) := by
          congr 1
      _ ≤ c * K' * Cfine ^ 2 * r ^ ((d : ℝ) - 2 - t) * r ^ t := h1
      _ ≤ c * K' * Cfine ^ 2 * r ^ ((d : ℝ) - 2 - t) * rad ^ t := by
          gcongr

/-- **Fine rescaled C² norm**: for the datum `φ = f - f(y)` pulled back from the cell of side `r` at `y`
to the unit cube, `c2Norm ≤ r B₁/2 + r B₁ + r² B₂` where `B₁, B₂` bound the first two derivatives of `f`. -/
lemma aux_hcut_fine_c2Norm (y z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ 2 f) (B1 B2 : ℝ)
    (hB1 : ∀ x, ‖fderiv ℝ f x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B2) :
    c2Norm (closedCube z0 1 one_pos : Set (SpatialCoordinates d))
      (fun x => (fun w => f w - f y) (cubeDilation y z0 r x)) ≤ r * B1 / 2 + r * B1 + r ^ 2 * B2 := by
  have hphi : ContDiff ℝ 2 (fun w => f w - f y) := hf.sub contDiff_const
  obtain ⟨-, -, hD1, hD2⟩ :=
    aux_lem_as_regularity_affine_transport_c2_chain_rule d y z0 r hr (fun w => f w - f y) hphi
  have hfd : ∀ w, fderiv ℝ (fun w => f w - f y) w = fderiv ℝ f w := fun w => by
    rw [fderiv_sub_const]
  have hfdd : fderiv ℝ (fderiv ℝ (fun w => f w - f y)) = fderiv ℝ (fderiv ℝ f) := by
    have : fderiv ℝ (fun w => f w - f y) = fderiv ℝ f := funext hfd
    rw [this]
  have hne : (closedCube z0 1 one_pos : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z0, Metric.mem_closedBall_self (by norm_num)⟩
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  unfold c2Norm
  have hB1' : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have h0 : sSup {v : ℝ | ∃ x ∈ (closedCube z0 1 one_pos : Set (SpatialCoordinates d)),
      v = |(fun w => f w - f y) (cubeDilation y z0 r x)|} ≤ r * B1 / 2 := by
    refine csSup_le ⟨_, z0, Metric.mem_closedBall_self (by norm_num), rfl⟩ ?_
    rintro v ⟨x, hx, rfl⟩
    have hTx : ‖cubeDilation y z0 r x - y‖ ≤ r / 2 := by
      have hx' : dist x z0 ≤ 1 / 2 := hx
      rw [dist_eq_norm] at hx'
      have : cubeDilation y z0 r x - y = r • (x - z0) := by
        funext i; simp [cubeDilation_apply]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith [norm_nonneg (x - z0)]
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (fun w _ => hdiff w) (fun w _ => hB1 w) convex_univ (Set.mem_univ y)
      (Set.mem_univ (cubeDilation y z0 r x))
    simp only
    rw [← Real.norm_eq_abs]
    calc ‖f (cubeDilation y z0 r x) - f y‖ ≤ B1 * ‖cubeDilation y z0 r x - y‖ := hmv
      _ ≤ B1 * (r / 2) := by gcongr
      _ = r * B1 / 2 := by ring
  have h1 : sSup {v : ℝ | ∃ x ∈ (closedCube z0 1 one_pos : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ (fun x => (fun w => f w - f y) (cubeDilation y z0 r x)) x‖} ≤ r * B1 := by
    refine csSup_le ⟨_, z0, Metric.mem_closedBall_self (by norm_num), rfl⟩ ?_
    rintro v ⟨x, -, rfl⟩
    refine (hD1 x).trans ?_
    rw [hfd]
    exact mul_le_mul_of_nonneg_left (hB1 _) hr.le
  have h2 : sSup {v : ℝ | ∃ x ∈ (closedCube z0 1 one_pos : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ (fderiv ℝ (fun x => (fun w => f w - f y) (cubeDilation y z0 r x))) x‖} ≤
      r ^ 2 * B2 := by
    refine csSup_le ⟨_, z0, Metric.mem_closedBall_self (by norm_num), rfl⟩ ?_
    rintro v ⟨x, -, rfl⟩
    refine (hD2 x).trans ?_
    rw [hfdd]
    exact mul_le_mul_of_nonneg_left (hB2 _) (by positivity)
  linarith

end Paper
end
end

-- ===== module HCut.CellGrowth =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The random cell constant `e^{Hω y} · shiftConst(cellEnv)⁻¹`. -/
def aux_hcut_cellConst (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d) (n N : ℕ)
    (om : BilateralField d) : ℝ :=
  Real.exp (H om y) * (aux_prop_growth_large_root_shiftConst M n (N - n) (aux_hcut_cellEnv y n om))⁻¹

lemma aux_hcut_cubeDilation_zero (y : SpatialCoordinates d) (r : ℝ) (x : SpatialCoordinates d) :
    cubeDilation y 0 r x = y + r • x := by
  funext i; simp [cubeDilation_apply]

/-- The coefficient hypothesis of `aux_hcut_cell_transfer`, almost surely. -/
lemma aux_hcut_ae_cell_hcoef (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) {n N : ℕ} (hnN : n ≤ N) (hr : 0 < ((3 : ℝ) ^ n)⁻¹) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ᵐ x ∂(volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))),
        ((cutoffPositiveCoefficient M H om N y hr).val : SpatialCoordinates d → ℝ)
            (cubeDilation y 0 ((3 : ℝ) ^ n)⁻¹ x) =
          aux_hcut_cellConst M H y n N om *
            ((cutoffPositiveCoefficient M H (aux_hcut_cellEnv y n om) (N - n) 0 one_pos).val :
              SpatialCoordinates d → ℝ) x := by
  filter_upwards [aux_hcut_ae_coeff_cell M Rm hH y hnN] with om hom
  have hq := Paper.lane4_dilation_quasi_measure_preserving d y 0 ((3 : ℝ) ^ n)⁻¹ hr one_pos
  filter_upwards [hq.ae (aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M H om N y hr),
    aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M H (aux_hcut_cellEnv y n om) (N - n)
      (0 : SpatialCoordinates d) one_pos] with x hx1 hx2
  rw [hx1, hx2, aux_hcut_cubeDilation_zero, hom x]
  rfl

lemma aux_hcut_cellConst_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d) (n N : ℕ)
    (om : BilateralField d) : 0 < aux_hcut_cellConst M H y n N om :=
  mul_pos (Real.exp_pos _) (inv_pos.2 (aux_prop_growth_large_root_shiftConst_pos M Rm _ _ _))

/-- **Per-cell growth, almost surely**, from `prop_growth` at the reference unit cube. -/
lemma aux_hcut_ae_cell_growth (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) {n N : ℕ} (hnN : n ≤ N) (hr : 0 < ((3 : ℝ) ^ n)⁻¹)
    {t alpha : ℝ} (ht : 0 ≤ t) (Kref : ℕ → BilateralField d → ℝ)
    (hKref1 : ∀ᵐ om' ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ Kref N om')
    (hGref : ∀ᵐ om' ∂(chaosSampleLaw M).toMeasure,
      aux_prop_growth_large_root_GrowthAt M H 0 1 one_pos t alpha om' (fun N => Kref N om')) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ 2 f → ∀ B1 B2 : ℝ,
        (∀ x, ‖fderiv ℝ f x‖ ≤ B1) → (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B2) →
      ∀ (b u : weakSobolevGraph (centeredCube y ((3 : ℝ) ^ n)⁻¹ hr)),
        ((b : SobolevData (centeredCube y ((3 : ℝ) ^ n)⁻¹ hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ n)⁻¹ hr : Set (SpatialCoordinates d))]
          (fun w => f w - f y) →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N y hr) (fun _ => (0 : ℝ)) b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube y ((3 : ℝ) ^ n)⁻¹ hr →
          0 < rad → rad ≤ 1 →
          localGradientEnergy (cutoffPositiveCoefficient M H om N y hr)
              (s := Metric.ball x rad ∩
                (centeredCube y ((3 : ℝ) ^ n)⁻¹ hr : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter
                (centeredCube y ((3 : ℝ) ^ n)⁻¹ hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube y ((3 : ℝ) ^ n)⁻¹ hr))) ≤
            aux_hcut_cellConst M H y n N om * Kref (N - n) (aux_hcut_cellEnv y n om) *
              (((3 : ℝ) ^ n)⁻¹ * B1 / 2 + ((3 : ℝ) ^ n)⁻¹ * B1 + (((3 : ℝ) ^ n)⁻¹) ^ 2 * B2) ^ 2 *
              (((3 : ℝ) ^ n)⁻¹) ^ ((d : ℝ) - 2 - t) * rad ^ t := by
  have hmp := (aux_hcut_measurePreserving_cellEnv M y n).quasiMeasurePreserving
  filter_upwards [aux_hcut_ae_cell_hcoef M Rm hH y hnN hr, hmp.ae hGref, hmp.ae hKref1]
    with om hcoef hG hK1
  intro f hf B1 B2 hB1 hB2 b u htrace hsolve x rad hx hrad0 hrad1
  have hr1 : ((3 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hG' : ∀ (phi1 : SpatialCoordinates d → ℝ) (Cphi1 : ℝ), ContDiff ℝ 2 phi1 →
      c2Norm (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) phi1 ≤
        Cphi1 →
      ∀ (b1 u1 : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
        ((b1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d))] phi1 →
        SolvesDirichlet (cutoffPositiveCoefficient M H (aux_hcut_cellEnv y n om) (N - n) 0 one_pos)
          (fun _ => (0 : ℝ)) b1 u1 →
        ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos →
          0 < rad → rad ≤ 1 →
          localGradientEnergy
              (cutoffPositiveCoefficient M H (aux_hcut_cellEnv y n om) (N - n) 0 one_pos)
              (s := Metric.ball x rad ∩
                (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter
                (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet)
              (sobolevGradient
                (u1 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))) ≤
            Kref (N - n) (aux_hcut_cellEnv y n om) * Cphi1 ^ 2 * rad ^ t := by
    intro phi1 Cphi1 hphi1 hC b1 u1 htr hs x' rad' hx' h0 h1
    have := (hG (N - n) (fun _ => (0 : ℝ)) 0 le_rfl measurable_const.aemeasurable
      (Eventually.of_forall fun _ => by simp) phi1 Cphi1 hphi1 hC b1 u1 htr hs).1 x' rad' hx' h0 h1
    simpa only [zero_add] using this
  have hphi : ContDiff ℝ 2 (fun w => f w - f y) := hf.sub contDiff_const
  exact aux_hcut_cell_transfer y 0 hr hr1 ht (cutoffPositiveCoefficient M H om N y hr)
    (cutoffPositiveCoefficient M H (aux_hcut_cellEnv y n om) (N - n) 0 one_pos)
    (aux_hcut_cellConst M H y n N om) (aux_hcut_cellConst_pos M Rm H y n N om) hcoef
    (Kref (N - n) (aux_hcut_cellEnv y n om)) (le_trans zero_le_one (hK1 (N - n))) hG'
    (fun w => f w - f y) hphi _ (aux_hcut_fine_c2Norm y 0 hr f hf B1 B2 hB1 hB2) b u htrace hsolve
    x rad hx hrad0 hrad1

end Paper
end
end

-- ===== module HCut.Grid =====
section
open MeasureTheory Metric
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut

variable {d : ℕ}

/-- Centre of the grid aux_hcut_cell `k` of side `h`. -/
def aux_hcut_cc (h : ℝ) (k : Fin d → ℤ) : Fin d → ℝ := fun i => h * ((k i : ℝ) + 1 / 2)

/-- The open grid aux_hcut_cell `k` of side `h` (a sup-norm ball). -/
def aux_hcut_cell (h : ℝ) (k : Fin d → ℤ) : Set (Fin d → ℝ) := ball (aux_hcut_cc h k) (h / 2)

lemma aux_hcut_mem_cell_iff {h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} {x : Fin d → ℝ} :
    x ∈ aux_hcut_cell h k ↔ ∀ i, |x i - aux_hcut_cc h k i| < h / 2 := by
  simp only [aux_hcut_cell, mem_ball, dist_pi_lt_iff (half_pos hh), Real.dist_eq]

lemma aux_hcut_cell_disjoint {h : ℝ} (hh : 0 < h) {k k' : Fin d → ℤ} (hkk : k ≠ k') :
    Disjoint (aux_hcut_cell h k) (aux_hcut_cell h k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [aux_hcut_mem_cell_iff hh] at hx hx'
  apply hkk
  funext i
  have h1 := hx i
  have h2 := hx' i
  simp only [aux_hcut_cc] at h1 h2
  have : |(k i : ℝ) - k' i| < 1 := by
    have e : (k i : ℝ) - k' i = ((x i - h * (k' i + 1 / 2)) - (x i - h * (k i + 1 / 2))) / h := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos hh, div_lt_one hh]
    calc |(x i - h * ((k' i : ℝ) + 1 / 2)) - (x i - h * ((k i : ℝ) + 1 / 2))|
        ≤ |x i - h * ((k' i : ℝ) + 1 / 2)| + |x i - h * ((k i : ℝ) + 1 / 2)| := abs_sub _ _
      _ < h / 2 + h / 2 := add_lt_add h2 h1
      _ = h := by ring
  have : |((k i - k' i : ℤ) : ℝ)| < 1 := by push_cast; exact this
  rw [← Int.cast_abs] at this
  have h3 : |k i - k' i| < 1 := by exact_mod_cast this
  rw [abs_lt] at h3
  omega

lemma aux_hcut_floor_bounds {h t : ℝ} (hh : 0 < h) :
    h * (⌊t / h⌋ : ℝ) ≤ t ∧ t < h * ((⌊t / h⌋ : ℝ) + 1) := by
  have h1 := Int.floor_le (t / h)
  have h2 := Int.lt_floor_add_one (t / h)
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hh.le
    rwa [mul_div_cancel₀ _ hh.ne'] at this
  · have := mul_lt_mul_of_pos_left h2 hh
    rwa [mul_div_cancel₀ _ hh.ne'] at this

/-- Closed grid cells cover everything. -/
lemma aux_hcut_exists_closedCell {h : ℝ} (hh : 0 < h) (x : Fin d → ℝ) :
    ∃ k : Fin d → ℤ, x ∈ closedBall (aux_hcut_cc h k) (h / 2) := by
  refine ⟨fun i => ⌊x i / h⌋, ?_⟩
  rw [mem_closedBall, dist_pi_le_iff (half_pos hh).le]
  intro i
  obtain ⟨h1, h2⟩ := aux_hcut_floor_bounds (t := x i) hh
  rw [Real.dist_eq, abs_le]
  simp only [aux_hcut_cc]
  constructor <;> nlinarith

/-- Almost every point lies in an open grid aux_hcut_cell. -/
lemma aux_hcut_ae_mem_cell {h : ℝ} (hh : 0 < h) :
    ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∃ k : Fin d → ℤ, x ∈ aux_hcut_cell h k := by
  have hnull : volume (⋃ i : Fin d, ⋃ m : ℤ, {x : Fin d → ℝ | x i = h * m}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun m => ?_
    have : {x : Fin d → ℝ | x i = h * m} = Function.eval i ⁻¹' ({h * (m : ℝ)} : Set ℝ) := rfl
    rw [this, volume_pi]
    exact Measure.pi_eval_preimage_null (fun _ => (volume : Measure ℝ)) Real.volume_singleton
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq, not_exists] at hx
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcon
  apply hx (fun i => ⌊x i / h⌋)
  rw [aux_hcut_mem_cell_iff hh]
  intro i
  obtain ⟨h1, h2⟩ := aux_hcut_floor_bounds (t := x i) hh
  have h3 : x i ≠ h * (⌊x i / h⌋ : ℝ) := fun he => hcon i ⌊x i / h⌋ he
  have h4 : x i ≠ h * ((⌊x i / h⌋ + 1 : ℤ) : ℝ) := fun he => hcon i (⌊x i / h⌋ + 1) he
  push_cast at h4
  have h1' : h * (⌊x i / h⌋ : ℝ) < x i := lt_of_le_of_ne h1 (Ne.symm h3)
  simp only [aux_hcut_cc]
  rw [abs_lt]
  constructor <;> nlinarith

lemma aux_hcut_cell_subset_ball {h : ℝ} {k : Fin d → ℤ} {x : Fin d → ℝ} {r : ℝ}
    (hk : (aux_hcut_cell h k ∩ ball x r).Nonempty) : aux_hcut_cell h k ⊆ ball x (r + h) := by
  obtain ⟨y, hy1, hy2⟩ := hk
  intro z hz
  simp only [aux_hcut_cell, mem_ball] at hy1 hz hy2 ⊢
  calc dist z x ≤ dist z (aux_hcut_cc h k) + dist (aux_hcut_cc h k) y + dist y x := dist_triangle4 _ _ _ _
    _ < h / 2 + h / 2 + r := by rw [dist_comm (aux_hcut_cc h k) y]; gcongr
    _ = r + h := by ring

lemma aux_hcut_measurableSet_cell (h : ℝ) (k : Fin d → ℤ) : MeasurableSet (aux_hcut_cell h k) :=
  measurableSet_ball

lemma aux_hcut_volume_cell {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ) :
    volume (aux_hcut_cell h k) = ENNReal.ofReal h ^ d := by
  rw [aux_hcut_cell, Real.volume_pi_ball _ (half_pos hh), Fintype.card_fin, ← ENNReal.ofReal_pow hh.le]
  congr 2; ring

/-- Counting cells meeting a ball, by volume. -/
lemma aux_hcut_card_mul_le {h : ℝ} (hh : 0 < h) (S : Finset (Fin d → ℤ)) {x : Fin d → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hS : ∀ k ∈ S, (aux_hcut_cell h k ∩ ball x r).Nonempty) :
    (S.card : ℝ) * h ^ d ≤ (2 * (r + h)) ^ d := by
  have hdisj : Set.PairwiseDisjoint (S : Set (Fin d → ℤ)) (aux_hcut_cell h) :=
    fun k _ k' _ hkk => aux_hcut_cell_disjoint hh hkk
  have hsub : (⋃ k ∈ S, aux_hcut_cell h k) ⊆ ball x (r + h) :=
    Set.iUnion₂_subset fun k hk => aux_hcut_cell_subset_ball (hS k hk)
  have hvol := measure_mono (μ := (volume : Measure (Fin d → ℝ))) hsub
  rw [measure_biUnion_finset hdisj (fun k _ => aux_hcut_measurableSet_cell h k),
    Real.volume_pi_ball x (by linarith)] at hvol
  simp only [aux_hcut_volume_cell hh, Finset.sum_const, nsmul_eq_mul] at hvol
  rw [← ENNReal.ofReal_pow hh.le, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hvol
  have h2 : (0 : ℝ) ≤ (2 * (r + h)) ^ d := by positivity
  rw [Fintype.card_fin] at hvol
  exact (ENNReal.ofReal_le_ofReal_iff h2).1 hvol

end HCut
end
end

-- ===== module HCut.AeCells =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- **All cells at once, almost surely.** -/
lemma aux_hcut_ae_cells (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H H0 : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (hH0 : InfraredCharacterization M H0) (alpha : ℝ) (K : ℕ → BilateralField d → ℝ)
    (hK1 : ∀ m om, 1 ≤ K m om)
    (hG0 : ∀ᵐ om' ∂(chaosSampleLaw M).toMeasure,
      aux_prop_growth_large_root_GrowthAt M H0 0 1 one_pos ((d : ℝ) - 1 / 2) alpha om'
        (fun m => K m om')) (N : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ k : Fin d → ℤ,
      ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ 2 f → ∀ B1 B2 : ℝ,
        (∀ x, ‖fderiv ℝ f x‖ ≤ B1) → (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B2) →
      ∀ (hr : 0 < ((3 : ℝ) ^ n)⁻¹)
        (b u : weakSobolevGraph (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr)),
        ((b : SobolevData (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr)).1 :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr :
              Set (SpatialCoordinates d))]
          (fun w => f w - f (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k)) →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) hr)
          (fun _ => (0 : ℝ)) b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr →
          0 < rad → rad ≤ 1 →
          localGradientEnergy (cutoffPositiveCoefficient M H om N (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) hr)
              (s := Metric.ball x rad ∩
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr))) ≤
            (aux_hcut_cellConst M H (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) n N om *
                K (N - n) (aux_hcut_cellEnv (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) n om)) *
              (((3 : ℝ) ^ n)⁻¹ * B1 / 2 + ((3 : ℝ) ^ n)⁻¹ * B1 + (((3 : ℝ) ^ n)⁻¹) ^ 2 * B2) ^ 2 *
              (((3 : ℝ) ^ n)⁻¹) ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * rad ^ ((d : ℝ) - 1 / 2) := by
  have hGH : ∀ᵐ om' ∂(chaosSampleLaw M).toMeasure,
      aux_prop_growth_large_root_GrowthAt M H 0 1 one_pos ((d : ℝ) - 1 / 2) alpha om'
        (fun m => K m om') := by
    filter_upwards [hG0, aux_hcut_H_ae_eq M hH hH0] with om' hg heq
    exact aux_hcut_growthAt_congr M heq 0 one_pos _ _ _ hg
  have ht : (0 : ℝ) ≤ (d : ℝ) - 1 / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [ae_all_iff]
  intro n
  by_cases hn : 1 ≤ n ∧ n ≤ N
  · have hr0 : 0 < ((3 : ℝ) ^ n)⁻¹ := by positivity
    have hall : ∀ k : Fin d → ℤ, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, _ := fun k =>
      aux_hcut_ae_cell_growth M Rm hH (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) hn.2 hr0 ht K
        (Eventually.of_forall fun om' m => hK1 m om') hGH
    rw [← ae_all_iff] at hall
    filter_upwards [hall] with om hom _ _ k f hf B1 B2 hB1 hB2 hr b u htr hs x rad hx h0 h1
    exact hom k f hf B1 B2 hB1 hB2 b u htr hs x rad hx h0 h1
  · exact Eventually.of_forall fun om h1 h2 => absurd ⟨h1, h2⟩ hn

end Paper
end
end

-- ===== module HCut.H10Ops =====
section
open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut
open Homogenization

/-- A smooth compactly supported function with support in `U`, as an `H¹₀(U)` function. -/
def aux_hcut_h10OfSmooth {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    H10Function U where
  toH1Function := H1Function.ofContDiff hU (hf.of_le (by simp)) hfc
  approx := fun _ => f
  approx_smooth := fun _ => hf
  approx_hasCompactSupport := fun _ => hfc
  approx_support_subset := fun _ => hfU
  tendsto_approx := by
    have : (fun _ : ℕ => eLpNorm (fun x => f x - f x) 2 (volume.restrict U)) = fun _ => 0 := by
      funext n; simp
    simpa [H1Function.ofContDiff] using (tendsto_const_nhds (x := (0 : ℝ≥0∞)) (f := atTop)).congr
      (fun n => by simp)
  tendsto_approx_grad := by
    intro i
    simpa [H1Function.ofContDiff] using (tendsto_const_nhds (x := (0 : ℝ≥0∞)) (f := atTop)).congr
      (fun n => by simp)

@[simp] lemma aux_hcut_h10OfSmooth_toFun {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    (aux_hcut_h10OfSmooth hU hf hfc hfU).toH1Function.toFun = f := rfl

@[simp] lemma aux_hcut_h10OfSmooth_grad {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    (aux_hcut_h10OfSmooth hU hf hfc hfU).toH1Function.grad = fun x i => (fderiv ℝ f x) (basisVec i) := rfl

/-- Replace `toFun` by an a.e.-equal function (same gradient and approximants). -/
def aux_hcut_h10CongrAe {d : ℕ} {U : Set (Vec d)} (v : H10Function U) (g : Vec d → ℝ)
    (hg : g =ᵐ[volume.restrict U] v.toH1Function.toFun) : H10Function U where
  toH1Function :=
    { toFun := g
      grad := v.toH1Function.grad
      memL2 := v.toH1Function.memL2.ae_eq hg.symm
      gradMemL2 := v.toH1Function.gradMemL2
      hasWeakGradient := by
        intro i φ h1 h2 h3
        rw [← v.toH1Function.hasWeakGradient i φ h1 h2 h3]
        exact integral_congr_ae (hg.mono fun x hx => by simp only [hx]) }
  approx := v.approx
  approx_smooth := v.approx_smooth
  approx_hasCompactSupport := v.approx_hasCompactSupport
  approx_support_subset := v.approx_support_subset
  tendsto_approx := by
    refine v.tendsto_approx.congr fun n => ?_
    exact eLpNorm_congr_ae (hg.mono fun x hx => by simp only [hx])
  tendsto_approx_grad := v.tendsto_approx_grad

@[simp] lemma aux_hcut_h10CongrAe_toFun {d : ℕ} {U : Set (Vec d)} (v : H10Function U) (g : Vec d → ℝ)
    (hg : g =ᵐ[volume.restrict U] v.toH1Function.toFun) :
    (aux_hcut_h10CongrAe v g hg).toH1Function.toFun = g := rfl

@[simp] lemma aux_hcut_h10CongrAe_grad {d : ℕ} {U : Set (Vec d)} (v : H10Function U) (g : Vec d → ℝ)
    (hg : g =ᵐ[volume.restrict U] v.toH1Function.toFun) :
    (aux_hcut_h10CongrAe v g hg).toH1Function.grad = v.toH1Function.grad := rfl

/-- Sum over a list of `H¹₀` functions. -/
def aux_hcut_h10ListSum {d : ℕ} {U : Set (Vec d)} : List (H10Function U) → H10Function U
  | [] => 0
  | v :: l => v + aux_hcut_h10ListSum l

lemma aux_hcut_h10ListSum_toFun {d : ℕ} {U : Set (Vec d)} (l : List (H10Function U)) (x : Vec d) :
    (aux_hcut_h10ListSum l).toH1Function.toFun x = (l.map fun v => v.toH1Function.toFun x).sum := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    simp only [aux_hcut_h10ListSum, List.map_cons, List.sum_cons]
    rw [← ih]; rfl

lemma aux_hcut_h10ListSum_grad {d : ℕ} {U : Set (Vec d)} (l : List (H10Function U)) (x : Vec d) :
    (aux_hcut_h10ListSum l).toH1Function.grad x = (l.map fun v => v.toH1Function.grad x).sum := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    simp only [aux_hcut_h10ListSum, List.map_cons, List.sum_cons]
    rw [← ih]; rfl

end HCut
end
end

-- ===== module HCut.CoreA =====
section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut
open Homogenization

variable {d : ℕ}

/-- The closed transition annulus of `f`. -/
def aux_hcut_Ann (R1 R2 h : ℝ) : Set (Fin d → ℝ) := {x | R1 + h ≤ ‖x‖ ∧ ‖x‖ ≤ R2 - 2 * h}

/-- Transition cells: closed aux_hcut_cell meets the annulus. -/
def aux_hcut_IsTrans (h R1 R2 : ℝ) (k : Fin d → ℤ) : Prop :=
  (closedBall (aux_hcut_cc h k) (h / 2) ∩ aux_hcut_Ann R1 R2 h).Nonempty

/-- The gradient vector of a smooth function. -/
def aux_hcut_gradVec (f : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) : Fin d → ℝ :=
  fun i => fderiv ℝ f z (basisVec i)

lemma aux_hcut_gradVec_eq_zero_of_eventuallyEq_const {f : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} {c : ℝ}
    (h : f =ᶠ[𝓝 z] fun _ => c) : aux_hcut_gradVec f z = 0 := by
  funext i
  simp only [aux_hcut_gradVec, h.fderiv_eq]
  simp

lemma aux_hcut_gradVec_eq_zero_off_Ann {f : (Fin d → ℝ) → ℝ} {R1 R2 h : ℝ}
    (hf1 : ∀ x, ‖x‖ ≤ R1 + h → f x = 1) (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0)
    {z : Fin d → ℝ} (hz : z ∉ aux_hcut_Ann R1 R2 h) : aux_hcut_gradVec f z = 0 := by
  simp only [aux_hcut_Ann, Set.mem_setOf_eq, not_and_or, not_le] at hz
  rcases hz with hz | hz
  · refine aux_hcut_gradVec_eq_zero_of_eventuallyEq_const (c := 1) ?_
    have : {x : Fin d → ℝ | ‖x‖ < R1 + h} ∈ 𝓝 z :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hz
    filter_upwards [this] with x hx using hf1 x hx.le
  · refine aux_hcut_gradVec_eq_zero_of_eventuallyEq_const (c := 0) ?_
    have : {x : Fin d → ℝ | R2 - 2 * h < ‖x‖} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hz
    filter_upwards [this] with x hx using hf0 x hx.le

lemma aux_hcut_trans_geom {R1 R2 h : ℝ} {k : Fin d → ℤ} (hk : aux_hcut_IsTrans h R1 R2 k)
    {z : Fin d → ℝ} (hz : z ∈ closedBall (aux_hcut_cc h k) (h / 2)) : R1 ≤ ‖z‖ ∧ ‖z‖ ≤ R2 - h := by
  obtain ⟨a, ha1, ha2⟩ := hk
  have hza : dist z a ≤ h := by
    calc dist z a ≤ dist z (aux_hcut_cc h k) + dist (aux_hcut_cc h k) a := dist_triangle _ _ _
      _ ≤ h / 2 + h / 2 := by rw [dist_comm (aux_hcut_cc h k) a]; exact add_le_add hz ha1
      _ = h := by ring
  have h1 : ‖a‖ ≤ ‖z‖ + dist z a := by
    rw [dist_eq_norm]; calc ‖a‖ = ‖z - (z - a)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖z‖ + ‖z - a‖ := norm_sub_le _ _
  have h2 : ‖z‖ ≤ ‖a‖ + dist z a := by
    rw [dist_eq_norm]; calc ‖z‖ = ‖a + (z - a)‖ := by rw [add_sub_cancel]
      _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
  obtain ⟨ha3, ha4⟩ := ha2
  constructor <;> linarith

lemma aux_hcut_trans_cell_subset {R1 R2 h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} (hk : aux_hcut_IsTrans h R1 R2 k) :
    closedBall (aux_hcut_cc h k) (h / 2) ⊆ ball (0 : Fin d → ℝ) R2 := by
  intro z hz
  rw [mem_ball_zero_iff]
  have := (aux_hcut_trans_geom hk hz).2
  linarith

lemma aux_hcut_trans_cell_disjoint_inner {R1 R2 h : ℝ} {k : Fin d → ℤ} (hk : aux_hcut_IsTrans h R1 R2 k)
    {z : Fin d → ℝ} (hz : z ∈ ball (0 : Fin d → ℝ) R1) : z ∉ closedBall (aux_hcut_cc h k) (h / 2) := by
  intro hzc
  have := (aux_hcut_trans_geom hk hzc).1
  rw [mem_ball_zero_iff] at hz
  linarith

lemma aux_hcut_trans_finite {R1 R2 h : ℝ} (hh : 0 < h) : {k : Fin d → ℤ | aux_hcut_IsTrans h R1 R2 k}.Finite := by
  set N : ℕ := ⌈|R2| / h⌉₊ + 1
  refine (Set.Finite.pi (t := fun _ : Fin d => (Finset.Icc (-(N : ℤ)) N : Set ℤ))
    (fun _ => Finset.finite_toSet _)).subset ?_
  intro k hk
  simp only [Set.mem_pi, Set.mem_univ, Finset.coe_Icc, Set.mem_Icc, true_implies]
  intro i
  have hc := (aux_hcut_trans_geom hk (mem_closedBall_self (by positivity : 0 ≤ h / 2)))
  have hci : |aux_hcut_cc h k i| ≤ ‖aux_hcut_cc h k‖ := by
    have := norm_le_pi_norm (aux_hcut_cc h k) i; rwa [Real.norm_eq_abs] at this
  simp only [aux_hcut_cc] at hci
  have hR : R2 - h ≤ |R2| := by linarith [le_abs_self R2]
  have h1 : |h * ((k i : ℝ) + 1 / 2)| ≤ |R2| := by linarith [hc.2]
  rw [abs_mul, abs_of_pos hh] at h1
  have h2 : |(k i : ℝ) + 1 / 2| ≤ |R2| / h := by rw [le_div_iff₀ hh]; linarith
  have hceil : |R2| / h ≤ (⌈|R2| / h⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : |(k i : ℝ)| ≤ (N : ℝ) := by
    have e : ((k i : ℝ) + 1 / 2) - 1 / 2 = (k i : ℝ) := by ring
    have h4 := abs_sub ((k i : ℝ) + 1 / 2) (1 / 2)
    rw [e] at h4
    have h5 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    have hN : (N : ℝ) = (⌈|R2| / h⌉₊ : ℝ) + 1 := by push_cast [N]; ring
    linarith
  rw [abs_le] at h3
  exact ⟨by exact_mod_cast h3.1, by exact_mod_cast h3.2⟩

end HCut
end
end

-- ===== module HCut.CoreB =====
section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut
open Homogenization

variable {d : ℕ}

lemma aux_hcut_sum_single_cell {M : Type*} [AddCommMonoid M] {h : ℝ} (hh : 0 < h) (T : Finset (Fin d → ℤ))
    (G : (Fin d → ℤ) → (Fin d → ℝ) → M) (hG : ∀ k ∈ T, ∀ x, x ∉ aux_hcut_cell h k → G k x = 0)
    {k0 : Fin d → ℤ} (hk0 : k0 ∈ T) {x : Fin d → ℝ} (hx : x ∈ aux_hcut_cell h k0) :
    ∑ k ∈ T, G k x = G k0 x := by
  refine Finset.sum_eq_single_of_mem k0 hk0 fun k hk hne => hG k hk x fun hxk => ?_
  exact Set.disjoint_left.1 (aux_hcut_cell_disjoint hh hne) hxk hx

lemma aux_hcut_sum_no_cell {M : Type*} [AddCommMonoid M] {h : ℝ} (T : Finset (Fin d → ℤ))
    (G : (Fin d → ℤ) → (Fin d → ℝ) → M) (hG : ∀ k ∈ T, ∀ x, x ∉ aux_hcut_cell h k → G k x = 0)
    {x : Fin d → ℝ} (hx : ∀ k ∈ T, x ∉ aux_hcut_cell h k) : ∑ k ∈ T, G k x = 0 :=
  Finset.sum_eq_zero fun k hk => hG k hk x (hx k hk)

/-- The raw interpolant `f + Σ_{k∈T} E_k`. -/
def aux_hcut_rawChi {R2 : ℝ} (F : H10Function (ball (0 : Fin d → ℝ) R2)) (T : Finset (Fin d → ℤ))
    (E : (Fin d → ℤ) → H10Function (ball (0 : Fin d → ℝ) R2)) :
    H10Function (ball (0 : Fin d → ℝ) R2) :=
  F + aux_hcut_h10ListSum (T.toList.map E)

lemma aux_hcut_rawChi_toFun {R2 : ℝ} (F : H10Function (ball (0 : Fin d → ℝ) R2)) (T : Finset (Fin d → ℤ))
    (E : (Fin d → ℤ) → H10Function (ball (0 : Fin d → ℝ) R2)) (x : Fin d → ℝ) :
    (aux_hcut_rawChi F T E).toH1Function.toFun x =
      F.toH1Function.toFun x + ∑ k ∈ T, (E k).toH1Function.toFun x := by
  show F.toH1Function.toFun x + (aux_hcut_h10ListSum (T.toList.map E)).toH1Function.toFun x = _
  rw [aux_hcut_h10ListSum_toFun, List.map_map]
  congr 1
  exact Finset.sum_map_toList T _

lemma aux_hcut_rawChi_grad {R2 : ℝ} (F : H10Function (ball (0 : Fin d → ℝ) R2)) (T : Finset (Fin d → ℤ))
    (E : (Fin d → ℤ) → H10Function (ball (0 : Fin d → ℝ) R2)) (x : Fin d → ℝ) :
    (aux_hcut_rawChi F T E).toH1Function.grad x =
      F.toH1Function.grad x + ∑ k ∈ T, (E k).toH1Function.grad x := by
  show F.toH1Function.grad x + (aux_hcut_h10ListSum (T.toList.map E)).toH1Function.grad x = _
  rw [aux_hcut_h10ListSum_grad, List.map_map]
  congr 1
  exact Finset.sum_map_toList T _

end HCut
end
end

-- ===== module HCut.CoreC =====
section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut

variable {d : ℕ}

/-- Decomposition of a ball integral along the open grid cells. -/
lemma aux_hcut_lintegral_ball_cells {h : ℝ} (hh : 0 < h) (Φ : (Fin d → ℝ) → ℝ≥0∞) (x : Fin d → ℝ) (r : ℝ) :
    ∫⁻ z in ball x r, Φ z = ∑' k : Fin d → ℤ, ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φ z := by
  have huniv : (⋃ k : Fin d → ℤ, aux_hcut_cell h k) =ᵐ[volume] (Set.univ : Set (Fin d → ℝ)) := by
    rw [ae_eq_univ]
    have h1 := aux_hcut_ae_mem_cell (d := d) hh
    rw [ae_iff] at h1
    refine measure_mono_null (fun z hz => ?_) h1
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hz
    simpa only [Set.mem_setOf_eq, not_exists] using hz
  have hae : (ball x r : Set (Fin d → ℝ)) =ᵐ[volume] ⋃ k : Fin d → ℤ, ball x r ∩ aux_hcut_cell h k := by
    rw [← Set.inter_iUnion]
    have := ae_eq_set_inter (ae_eq_refl (ball x r : Set (Fin d → ℝ))) huniv
    rw [Set.inter_univ] at this
    exact this.symm
  rw [Measure.restrict_congr_set hae]
  refine lintegral_iUnion (fun k => measurableSet_ball.inter (aux_hcut_measurableSet_cell h k)) ?_ Φ
  intro k k' hkk
  exact (aux_hcut_cell_disjoint hh hkk).mono Set.inter_subset_right Set.inter_subset_right

/-- Real bound, small balls. -/
lemma aux_hcut_real_small {h Kc r N : ℝ} {d : ℕ} (hd : 1 ≤ d) (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hKc : 0 ≤ Kc)
    (hr : 0 < r) (hN : N ≤ 4 ^ d) (hN0 : 0 ≤ N) :
    N * (Kc * (2 * r) ^ ((d : ℝ) - 1 / 2)) ≤ 8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by
  have ht : (0 : ℝ) ≤ (d : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h2t : (2 : ℝ) ^ ((d : ℝ) - 1 / 2) ≤ 2 ^ d := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hhm : 1 ≤ h ^ (-(1 / 2 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh (by linarith) (by norm_num)
  have hrt : 0 ≤ r ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg hr.le _
  rw [Real.mul_rpow (by norm_num) hr.le]
  calc N * (Kc * (2 ^ ((d : ℝ) - 1 / 2) * r ^ ((d : ℝ) - 1 / 2)))
      ≤ 4 ^ d * (Kc * (2 ^ d * r ^ ((d : ℝ) - 1 / 2))) := by gcongr
    _ = 8 ^ d * Kc * 1 * r ^ ((d : ℝ) - 1 / 2) := by
        rw [show (8 : ℝ) ^ d = 4 ^ d * 2 ^ d by rw [← mul_pow]; norm_num]; ring
    _ ≤ 8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by gcongr

/-- Real bound, large balls. -/
lemma aux_hcut_real_large {h Kc r N : ℝ} {d : ℕ} (hd : 1 ≤ d) (hh : 0 < h) (hKc : 0 ≤ Kc)
    (hhr : h < r) (hr1 : r ≤ 1) (hN : N * h ^ d ≤ (4 * r) ^ d) (hN0 : 0 ≤ N) :
    N * (Kc * h ^ ((d : ℝ) - 1 / 2)) ≤ 8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by
  have hr : 0 < r := hh.trans hhr
  have hsplit : h ^ ((d : ℝ) - 1 / 2) = h ^ d * h ^ (-(1 / 2 : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hh, Real.rpow_natCast]
  have hrd : r ^ d ≤ r ^ ((d : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hhm : 0 ≤ h ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hh.le _
  rw [hsplit]
  calc N * (Kc * (h ^ d * h ^ (-(1 / 2 : ℝ)))) = (N * h ^ d) * Kc * h ^ (-(1 / 2 : ℝ)) := by ring
    _ ≤ (4 * r) ^ d * Kc * h ^ (-(1 / 2 : ℝ)) := by gcongr
    _ = 4 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ d := by rw [mul_pow]; ring
    _ ≤ 8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by
        have h48 : (4 : ℝ) ^ d ≤ 8 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
        gcongr

/-- **Ball energy of the cellwise interpolant.** -/
lemma aux_hcut_energy_bound (hd : 1 ≤ d) {h Kc : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hKc : 0 ≤ Kc)
    (T : Finset (Fin d → ℤ)) (Φ : (Fin d → ℝ) → ℝ≥0∞) (Φk : (Fin d → ℤ) → (Fin d → ℝ) → ℝ≥0∞)
    (hΦ1 : ∀ k ∈ T, ∀ z ∈ aux_hcut_cell h k, Φ z = Φk k z)
    (hΦ0 : ∀ k ∉ T, ∀ z ∈ aux_hcut_cell h k, Φ z = 0)
    (hgrow : ∀ k ∈ T, ∀ y ∈ aux_hcut_cell h k, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∫⁻ z in ball y ρ ∩ aux_hcut_cell h k, Φk k z ≤ ENNReal.ofReal (Kc * ρ ^ ((d : ℝ) - 1 / 2)))
    (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ z in ball x r, Φ z ≤
      ENNReal.ofReal (8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2)) := by
  classical
  set T' := T.filter (fun k => (aux_hcut_cell h k ∩ ball x r).Nonempty) with hT'
  have hterm0 : ∀ k ∉ T', ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φ z = 0 := by
    intro k hk
    by_cases hkT : k ∈ T
    · have hemp : ball x r ∩ aux_hcut_cell h k = ∅ := by
        rw [Set.inter_comm]
        by_contra hne
        exact hk (Finset.mem_filter.2 ⟨hkT, Set.nonempty_iff_ne_empty.2 hne⟩)
      rw [hemp, Measure.restrict_empty, lintegral_zero_measure]
    · rw [setLIntegral_congr_fun (measurableSet_ball.inter (aux_hcut_measurableSet_cell h k))
        (fun z hz => hΦ0 k hkT z hz.2)]
      simp
  rw [aux_hcut_lintegral_ball_cells hh Φ x r, tsum_eq_sum (s := T') (fun k hk => hterm0 k hk)]
  have hterm1 : ∀ k ∈ T', ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φ z = ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φk k z := by
    intro k hk
    exact setLIntegral_congr_fun (measurableSet_ball.inter (aux_hcut_measurableSet_cell h k))
      (fun z hz => hΦ1 k (Finset.mem_filter.1 hk).1 z hz.2)
  rw [Finset.sum_congr rfl hterm1]
  have hcard := aux_hcut_card_mul_le hh T' hr.le (fun k hk => by
    have := (Finset.mem_filter.1 hk).2; exact this)
  rcases le_or_lt r h with hrh | hrh
  · -- small balls: at most `4^d` cells, each bounded at radius `2r`
    have hb : ∀ k ∈ T', ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φk k z ≤
        ENNReal.ofReal (Kc * (2 * r) ^ ((d : ℝ) - 1 / 2)) := by
      intro k hk
      obtain ⟨hkT, ⟨y, hy1, hy2⟩⟩ := Finset.mem_filter.1 hk
      refine (lintegral_mono_set ?_).trans (hgrow k hkT y hy1 (2 * r) (by positivity) (by linarith))
      intro z ⟨hz1, hz2⟩
      refine ⟨?_, hz2⟩
      rw [mem_ball] at hz1 hy2 ⊢
      calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
        _ < r + r := by rw [dist_comm x y]; exact add_lt_add hz1 hy2
        _ = 2 * r := by ring
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (aux_hcut_real_small hd hh hh1 hKc hr ?_ (by positivity))
    have h4 : (2 * (r + h)) ^ d ≤ (4 * h) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    have hhd : 0 < h ^ d := by positivity
    have := hcard.trans h4
    rw [mul_pow] at this
    exact le_of_mul_le_mul_right (by linarith) hhd
  · -- large balls: whole-aux_hcut_cell bounds
    have hb : ∀ k ∈ T', ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φk k z ≤
        ENNReal.ofReal (Kc * h ^ ((d : ℝ) - 1 / 2)) := by
      intro k hk
      obtain ⟨hkT, -⟩ := Finset.mem_filter.1 hk
      have hc : aux_hcut_cc h k ∈ aux_hcut_cell h k := mem_ball_self (half_pos hh)
      refine (lintegral_mono_set ?_).trans (hgrow k hkT (aux_hcut_cc h k) hc h hh (by linarith))
      intro z ⟨_, hz2⟩
      refine ⟨?_, hz2⟩
      exact ball_subset_ball (by linarith) hz2
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (aux_hcut_real_large hd hh hKc hrh hr1 ?_ (by positivity))
    exact hcard.trans (pow_le_pow_left₀ (by positivity) (by linarith) d)

end HCut
end
end

-- ===== module HCut.CoreD =====
section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut
open Homogenization

variable {d : ℕ}

lemma aux_hcut_cell_sub_ball {R1 R2 h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} (hk : aux_hcut_IsTrans h R1 R2 k) :
    aux_hcut_cell h k ⊆ ball (0 : Fin d → ℝ) R2 :=
  ball_subset_closedBall.trans (aux_hcut_trans_cell_subset hh hk)

/-- The zero-extended aux_hcut_cell correctors. -/
def aux_hcut_extE {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) (k : Fin d → ℤ) :
    H10Function (ball (0 : Fin d → ℝ) R2) := by
  classical
  exact if hk : aux_hcut_IsTrans h R1 R2 k then
    (e k hk).extendByZeroToOpenSuperset (aux_hcut_measurableSet_cell h k) isOpen_ball (aux_hcut_cell_sub_ball hh hk)
  else 0

lemma aux_hcut_extE_toFun_of_mem {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) {k : Fin d → ℤ}
    (hk : aux_hcut_IsTrans h R1 R2 k) {z : Fin d → ℝ} (hz : z ∈ aux_hcut_cell h k) :
    (aux_hcut_extE hh e k).toH1Function.toFun z = (e k hk).toH1Function.toFun z := by
  classical
  simp only [aux_hcut_extE, dif_pos hk, H10Function.extendByZeroToOpenSuperset_toFun,
    H10Function.zeroExtension_apply_of_mem _ hz]

lemma aux_hcut_extE_toFun_of_not_mem {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) {k : Fin d → ℤ}
    (hk : aux_hcut_IsTrans h R1 R2 k) {z : Fin d → ℝ} (hz : z ∉ aux_hcut_cell h k) :
    (aux_hcut_extE hh e k).toH1Function.toFun z = 0 := by
  classical
  simp only [aux_hcut_extE, dif_pos hk, H10Function.extendByZeroToOpenSuperset_toFun,
    H10Function.zeroExtension_apply_of_not_mem _ hz]

lemma aux_hcut_extE_grad_of_mem {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) {k : Fin d → ℤ}
    (hk : aux_hcut_IsTrans h R1 R2 k) {z : Fin d → ℝ} (hz : z ∈ aux_hcut_cell h k) :
    (aux_hcut_extE hh e k).toH1Function.grad z = (e k hk).toH1Function.grad z := by
  classical
  simp only [aux_hcut_extE, dif_pos hk, H10Function.extendByZeroToOpenSuperset_grad,
    H10Function.zeroExtensionGrad_apply_of_mem _ hz]

lemma aux_hcut_extE_grad_of_not_mem {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) {k : Fin d → ℤ}
    (hk : aux_hcut_IsTrans h R1 R2 k) {z : Fin d → ℝ} (hz : z ∉ aux_hcut_cell h k) :
    (aux_hcut_extE hh e k).toH1Function.grad z = 0 := by
  classical
  simp only [aux_hcut_extE, dif_pos hk, H10Function.extendByZeroToOpenSuperset_grad,
    H10Function.zeroExtensionGrad_apply_of_not_mem _ hz]

end HCut
end
end

-- ===== module HCut.CoreE =====
section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut
open Homogenization

variable {d : ℕ}

lemma aux_hcut_mem_T {R1 R2 h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} :
    k ∈ (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset ↔ aux_hcut_IsTrans h R1 R2 k :=
  Set.Finite.mem_toFinset _

section Formulas
variable {R1 R2 h : ℝ} (hh : 0 < h) (F : H10Function (ball (0 : Fin d → ℝ) R2))
  (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k))

lemma aux_hcut_X_toFun_on_cell {k0 : Fin d → ℤ} (hk0 : aux_hcut_IsTrans h R1 R2 k0) {z : Fin d → ℝ}
    (hz : z ∈ aux_hcut_cell h k0) :
    (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.toFun z =
      F.toH1Function.toFun z + (e k0 hk0).toH1Function.toFun z := by
  rw [aux_hcut_rawChi_toFun, aux_hcut_sum_single_cell hh _ (fun k z => (aux_hcut_extE hh e k).toH1Function.toFun z)
    (fun k hk z hz => aux_hcut_extE_toFun_of_not_mem hh e ((aux_hcut_mem_T hh).1 hk) hz)
    ((aux_hcut_mem_T hh).2 hk0) hz, aux_hcut_extE_toFun_of_mem hh e hk0 hz]

lemma aux_hcut_X_grad_on_cell {k0 : Fin d → ℤ} (hk0 : aux_hcut_IsTrans h R1 R2 k0) {z : Fin d → ℝ}
    (hz : z ∈ aux_hcut_cell h k0) :
    (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.grad z =
      F.toH1Function.grad z + (e k0 hk0).toH1Function.grad z := by
  rw [aux_hcut_rawChi_grad, aux_hcut_sum_single_cell hh _ (fun k z => (aux_hcut_extE hh e k).toH1Function.grad z)
    (fun k hk z hz => aux_hcut_extE_grad_of_not_mem hh e ((aux_hcut_mem_T hh).1 hk) hz)
    ((aux_hcut_mem_T hh).2 hk0) hz, aux_hcut_extE_grad_of_mem hh e hk0 hz]

lemma aux_hcut_X_toFun_off {z : Fin d → ℝ} (hz : ∀ k, aux_hcut_IsTrans h R1 R2 k → z ∉ aux_hcut_cell h k) :
    (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.toFun z =
      F.toH1Function.toFun z := by
  rw [aux_hcut_rawChi_toFun, aux_hcut_sum_no_cell _ (fun k z => (aux_hcut_extE hh e k).toH1Function.toFun z)
    (fun k hk z hz => aux_hcut_extE_toFun_of_not_mem hh e ((aux_hcut_mem_T hh).1 hk) hz)
    (fun k hk => hz k ((aux_hcut_mem_T hh).1 hk)), add_zero]

lemma aux_hcut_X_grad_off {z : Fin d → ℝ} (hz : ∀ k, aux_hcut_IsTrans h R1 R2 k → z ∉ aux_hcut_cell h k) :
    (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.grad z =
      F.toH1Function.grad z := by
  rw [aux_hcut_rawChi_grad, aux_hcut_sum_no_cell _ (fun k z => (aux_hcut_extE hh e k).toH1Function.grad z)
    (fun k hk z hz => aux_hcut_extE_grad_of_not_mem hh e ((aux_hcut_mem_T hh).1 hk) hz)
    (fun k hk => hz k ((aux_hcut_mem_T hh).1 hk)), add_zero]

end Formulas

lemma aux_hcut_not_trans_cells_of_mem {R1 R2 h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} {z : Fin d → ℝ}
    (hz : z ∈ aux_hcut_cell h k) (hk : ¬ aux_hcut_IsTrans h R1 R2 k) : ∀ k', aux_hcut_IsTrans h R1 R2 k' → z ∉ aux_hcut_cell h k' := by
  intro k' hk' hz'
  by_cases hkk : k = k'
  · exact hk (hkk ▸ hk')
  · exact Set.disjoint_left.1 (aux_hcut_cell_disjoint hh hkk) hz hz'

lemma aux_hcut_not_mem_Ann_of_not_trans {R1 R2 h : ℝ} {k : Fin d → ℤ} {z : Fin d → ℝ}
    (hz : z ∈ aux_hcut_cell h k) (hk : ¬ aux_hcut_IsTrans h R1 R2 k) : z ∉ aux_hcut_Ann R1 R2 h :=
  fun hzA => hk ⟨z, ball_subset_closedBall hz, hzA⟩

end HCut
end
end

-- ===== module HCut.CoreF =====
section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut
open Homogenization

variable {d : ℕ}

lemma aux_hcut_f_compact {R2 h : ℝ} {f : (Fin d → ℝ) → ℝ} (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) (R2 - 2 * h)) fun x hx => by
    apply hf0; rw [mem_closedBall_zero_iff, not_le] at hx; exact hx.le

lemma aux_hcut_f_tsupport {R2 h : ℝ} (hh : 0 < h) {f : (Fin d → ℝ) → ℝ}
    (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0) :
    tsupport f ⊆ closedBall (0 : Fin d → ℝ) (R2 - 2 * h) := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  rw [mem_closedBall_zero_iff]
  by_contra hcon
  exact hx (hf0 x (le_of_lt (not_le.1 hcon)))

/-- The a.e. `[0,1]` bounds of the raw interpolant. -/
lemma aux_hcut_raw_bounds {R1 R2 h : ℝ} (hh : 0 < h) (F : H10Function (ball (0 : Fin d → ℝ) R2))
    (f : (Fin d → ℝ) → ℝ) (hFf : F.toH1Function.toFun = f) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k))
    (he : ∀ k (hk : aux_hcut_IsTrans h R1 R2 k), ∀ᵐ x ∂(volume.restrict (aux_hcut_cell h k)),
      0 ≤ f x + (e k hk).toH1Function.toFun x ∧ f x + (e k hk).toH1Function.toFun x ≤ 1) :
    ∀ᵐ z ∂(volume : Measure (Fin d → ℝ)),
      0 ≤ (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.toFun z ∧
      (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.toFun z ≤ 1 := by
  set T := (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset
  have hall : ∀ᵐ z ∂(volume : Measure (Fin d → ℝ)), ∀ k ∈ T, ∀ hk : aux_hcut_IsTrans h R1 R2 k,
      z ∈ aux_hcut_cell h k → 0 ≤ f z + (e k hk).toH1Function.toFun z ∧
        f z + (e k hk).toH1Function.toFun z ≤ 1 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    have hk' := (aux_hcut_mem_T hh).1 hk
    filter_upwards [(ae_restrict_iff' (aux_hcut_measurableSet_cell h k)).1 (he k hk')] with z hz _ hz'
    exact hz hz'
  filter_upwards [hall, aux_hcut_ae_mem_cell (d := d) hh] with z hz ⟨k, hk⟩
  by_cases hkT : aux_hcut_IsTrans h R1 R2 k
  · rw [aux_hcut_X_toFun_on_cell hh F e hkT hk, hFf]
    exact hz k ((aux_hcut_mem_T hh).2 hkT) hkT hk
  · rw [aux_hcut_X_toFun_off hh F e (aux_hcut_not_trans_cells_of_mem hh hk hkT), hFf]
    exact hf01 z

end HCut
end
end

-- ===== module HCut.Core =====
section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut
open Homogenization

variable {d : ℕ}

/-- **hCut deterministic core.** Given smooth `f` (`1` on `‖x‖ ≤ R1+h`, `0` on `‖x‖ ≥ R2-2h`) and, on
every transition aux_hcut_cell of the side-`h` grid, a corrector `e ∈ H¹₀(aux_hcut_cell)` with `0 ≤ f+e ≤ 1` and the
local energy growth `Kc ρ^{d-1/2}`, the cellwise interpolant is an admissible cutoff between
`ball 0 R1` and `ball 0 R2` with ball energy `≤ 8^d Kc h^{-1/2} r^{d-1/2}`. -/
theorem aux_hcut_hcut_core (hd : 1 ≤ d) (A : (Fin d → ℝ) → ℝ) (hApos : ∀ x, 0 < A x)
    (R1 R2 h Kc : ℝ) (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hKc : 0 ≤ Kc)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hf1 : ∀ x, ‖x‖ ≤ R1 + h → f x = 1) (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0)
    (hcell : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → ∃ e : H10Function (aux_hcut_cell h k),
      (∀ᵐ x ∂(volume.restrict (aux_hcut_cell h k)),
        0 ≤ f x + e.toH1Function.toFun x ∧ f x + e.toH1Function.toFun x ≤ 1) ∧
      ∀ y ∈ aux_hcut_cell h k, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ∫⁻ z in ball y ρ ∩ aux_hcut_cell h k, ENNReal.ofReal (A z *
          vecDot (aux_hcut_gradVec f z + e.toH1Function.grad z) (aux_hcut_gradVec f z + e.toH1Function.grad z)) ≤
        ENNReal.ofReal (Kc * ρ ^ ((d : ℝ) - 1 / 2))) :
    ∃ chi : H10Function (ball (0 : Fin d → ℝ) R2),
      (∀ x, 0 ≤ chi.toH1Function.toFun x ∧ chi.toH1Function.toFun x ≤ 1) ∧
      (∀ x ∈ ball (0 : Fin d → ℝ) R1, chi.toH1Function.toFun x = 1) ∧
      tsupport chi.toH1Function.toFun ⊆ ball (0 : Fin d → ℝ) R2 ∧
      ∀ (x : Fin d → ℝ) (r : ℝ), 0 < r → r ≤ 1 →
        ∫⁻ z in ball x r ∩ ball (0 : Fin d → ℝ) R2, ENNReal.ofReal (A z *
            vecDot (chi.toH1Function.grad z) (chi.toH1Function.grad z)) ≤
          ENNReal.ofReal (8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2)) := by
  classical
  choose e he using hcell
  have hfsub : tsupport f ⊆ ball (0 : Fin d → ℝ) R2 :=
    (aux_hcut_f_tsupport hh hf0).trans (closedBall_subset_ball (by linarith))
  set F := aux_hcut_h10OfSmooth isOpen_ball hf (aux_hcut_f_compact hf0) hfsub with hF
  set X := aux_hcut_rawChi F (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e) with hX
  have hbd : ∀ᵐ z ∂(volume : Measure (Fin d → ℝ)),
      0 ≤ X.toH1Function.toFun z ∧ X.toH1Function.toFun z ≤ 1 :=
    aux_hcut_raw_bounds hh F f rfl hf01 e (fun k hk => (he k hk).1)
  set clamp : (Fin d → ℝ) → ℝ := fun z => max 0 (min 1 (X.toH1Function.toFun z)) with hclamp
  have hcl : clamp =ᵐ[volume.restrict (ball (0 : Fin d → ℝ) R2)] X.toH1Function.toFun := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hbd] with z hz
    simp only [hclamp, min_eq_right hz.2, max_eq_right hz.1]
  refine ⟨aux_hcut_h10CongrAe X clamp hcl, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [aux_hcut_h10CongrAe_toFun, hclamp]
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · intro x hx
    simp only [aux_hcut_h10CongrAe_toFun, hclamp]
    have hoff : ∀ k, aux_hcut_IsTrans h R1 R2 k → x ∉ aux_hcut_cell h k := fun k hk hxk =>
      aux_hcut_trans_cell_disjoint_inner hk hx (ball_subset_closedBall hxk)
    rw [hX, aux_hcut_X_toFun_off hh F e hoff, hF, aux_hcut_h10OfSmooth_toFun,
      hf1 x (by rw [mem_ball_zero_iff] at hx; linarith)]
    norm_num
  · -- support
    set K0 : Set (Fin d → ℝ) := closedBall 0 (R2 - 2 * h) ∪
      ⋃ k ∈ (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset, closedBall (aux_hcut_cc h k) (h / 2)
    have hK0closed : IsClosed K0 :=
      isClosed_closedBall.union (isClosed_biUnion_finset fun k _ => isClosed_closedBall)
    have hK0sub : K0 ⊆ ball (0 : Fin d → ℝ) R2 := by
      refine Set.union_subset (closedBall_subset_ball (by linarith)) (Set.iUnion₂_subset fun k hk => ?_)
      exact aux_hcut_trans_cell_subset hh ((aux_hcut_mem_T hh).1 hk)
    refine (closure_minimal (fun x hx => ?_) hK0closed).trans hK0sub
    simp only [aux_hcut_h10CongrAe_toFun, Function.mem_support, hclamp] at hx
    by_cases hin : ∃ k, aux_hcut_IsTrans h R1 R2 k ∧ x ∈ aux_hcut_cell h k
    · obtain ⟨k, hk, hxk⟩ := hin
      exact Or.inr (Set.mem_biUnion ((aux_hcut_mem_T hh).2 hk) (ball_subset_closedBall hxk))
    · push_neg at hin
      rw [hX, aux_hcut_X_toFun_off hh F e hin, hF, aux_hcut_h10OfSmooth_toFun] at hx
      left
      rw [mem_closedBall_zero_iff]
      by_contra hcon
      apply hx
      rw [hf0 x (le_of_lt (not_le.1 hcon))]
      norm_num
  · -- energy
    intro x r hr hr1
    refine (lintegral_mono_set Set.inter_subset_left).trans ?_
    simp only [aux_hcut_h10CongrAe_grad]
    refine aux_hcut_energy_bound hd hh hh1 hKc (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset
      (fun z => ENNReal.ofReal (A z * vecDot (X.toH1Function.grad z) (X.toH1Function.grad z)))
      (fun k z => if hk : aux_hcut_IsTrans h R1 R2 k then ENNReal.ofReal (A z *
          vecDot (aux_hcut_gradVec f z + (e k hk).toH1Function.grad z)
            (aux_hcut_gradVec f z + (e k hk).toH1Function.grad z)) else 0)
      ?_ ?_ ?_ x hr hr1
    · intro k hk z hz
      have hk' := (aux_hcut_mem_T hh).1 hk
      beta_reduce
      simp only [dif_pos hk']
      rw [hX, aux_hcut_X_grad_on_cell hh F e hk' hz, hF, aux_hcut_h10OfSmooth_grad]
      rfl
    · intro k hk z hz
      have hk' : ¬ aux_hcut_IsTrans h R1 R2 k := fun h' => hk ((aux_hcut_mem_T hh).2 h')
      beta_reduce
      rw [hX, aux_hcut_X_grad_off hh F e (aux_hcut_not_trans_cells_of_mem hh hz hk'), hF, aux_hcut_h10OfSmooth_grad]
      have h0 : aux_hcut_gradVec f z = 0 := aux_hcut_gradVec_eq_zero_off_Ann hf1 hf0 (aux_hcut_not_mem_Ann_of_not_trans hz hk')
      have h0' : (fun x i => (fderiv ℝ f x) (basisVec i)) z = 0 := h0
      rw [h0']
      simp [vecDot]
    · intro k hk y hy ρ hρ hρ1
      have hk' := (aux_hcut_mem_T hh).1 hk
      beta_reduce
      simp only [dif_pos hk']
      exact (he k hk').2 y hy ρ hρ hρ1

end HCut
end
end

-- ===== module HCut.SmoothDatum =====
section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- A globally smooth function restricted to a bounded open domain is square
integrable, using boundedness of `closure Ω` (Heine--Borel) rather than
linearity. -/
theorem aux_hcut_cell_corrector_smooth_memLp
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    MemLp φ 2 (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have hcl : IsCompact (closure (Ω : Set (SpatialCoordinates d))) := hΩ.isCompact_closure
  obtain ⟨C, hC⟩ := hcl.exists_bound_of_continuousOn hφ.continuous.continuousOn
  refine MemLp.of_bound hφ.continuous.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hC x (subset_closure hx)

/-- Each coordinate derivative of a globally smooth function is square integrable
on a bounded open domain. -/
theorem aux_hcut_cell_corrector_smooth_derivMemLp
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    MemLp (fun x => fderiv ℝ φ x (Homogenization.basisVec i)) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have hcl : IsCompact (closure (Ω : Set (SpatialCoordinates d))) := hΩ.isCompact_closure
  have hderiv_cont : Continuous (fun x => (fderiv ℝ φ x) (Homogenization.basisVec i)) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := by
      simpa using hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (h1.continuous).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hcl.exists_bound_of_continuousOn hderiv_cont.continuousOn
  refine MemLp.of_bound hderiv_cont.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hC x (subset_closure hx)

/-- The `L²` class of a globally smooth function on a bounded open domain. -/
noncomputable def aux_hcut_cell_corrector_smoothVal
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : DomainL2 Ω :=
  (aux_hcut_cell_corrector_smooth_memLp hΩ φ hφ).toLp φ

theorem aux_hcut_cell_corrector_smoothVal_coeFn
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (aux_hcut_cell_corrector_smoothVal hΩ φ hφ : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] φ :=
  MemLp.coeFn_toLp _

/-- The `L²` class of one coordinate derivative of a globally smooth function. -/
noncomputable def aux_hcut_cell_corrector_smoothGrad
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) : DomainL2 Ω :=
  (aux_hcut_cell_corrector_smooth_derivMemLp hΩ φ hφ i).toLp
    (fun x => fderiv ℝ φ x (Homogenization.basisVec i))

theorem aux_hcut_cell_corrector_smoothGrad_coeFn
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    (aux_hcut_cell_corrector_smoothGrad hΩ φ hφ i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))]
      (fun x => fderiv ℝ φ x (Homogenization.basisVec i)) :=
  MemLp.coeFn_toLp _

/-- The function/gradient pair of a globally smooth function, as raw `SobolevData`. -/
noncomputable def aux_hcut_cell_corrector_smoothData
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : SobolevData Ω :=
  (aux_hcut_cell_corrector_smoothVal hΩ φ hφ,
    fun i => aux_hcut_cell_corrector_smoothGrad hΩ φ hφ i)

/-- The classical derivative of a globally smooth function really is its
distributional derivative: the same integration-by-parts argument as
`affineSobolevData_mem`, without using linearity of the target function. -/
theorem aux_hcut_cell_corrector_smoothData_mem
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    aux_hcut_cell_corrector_smoothData hΩ φ hφ ∈ weakSobolevGraph Ω := by
  rw [mem_weakSobolevGraph_iff]
  intro test i
  let v : SpatialCoordinates d := Homogenization.basisVec i
  have hbcont : Continuous φ := hφ.continuous
  have htestderiv : Continuous (fun x => fderiv ℝ test x v) :=
    (test.contDiff.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hbderiv : Continuous (fun x => fderiv ℝ φ x v) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := by
      simpa using hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (h1.continuous).clm_apply continuous_const
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (SpatialCoordinates d))) (v := v)
    ((htestderiv.mul hbcont).integrable_of_hasCompactSupport
      (test.hasCompactSupport.fderiv_apply ℝ v).mul_right)
    ((test.contDiff.continuous.mul hbderiv).integrable_of_hasCompactSupport
      test.hasCompactSupport.mul_right)
    ((test.contDiff.continuous.mul hbcont).integrable_of_hasCompactSupport
      test.hasCompactSupport.mul_right)
    (test.contDiff.differentiable (by simp)) (hφ.differentiable (by simp))
  have hleft : (∫ x in (Ω : Set (SpatialCoordinates d)),
      test x * (aux_hcut_cell_corrector_smoothGrad hΩ φ hφ i : SpatialCoordinates d → ℝ) x) =
      ∫ x, test x * fderiv ℝ φ x v := by
    calc
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)), test x * fderiv ℝ φ x v := by
        apply integral_congr_ae
        filter_upwards [aux_hcut_cell_corrector_smoothGrad_coeFn hΩ φ hφ i] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : test x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (test.tsupport_subset h))
        simp only [hz, zero_mul]
  have hright : (∫ x in (Ω : Set (SpatialCoordinates d)),
      fderiv ℝ test x v * (aux_hcut_cell_corrector_smoothVal hΩ φ hφ : SpatialCoordinates d → ℝ) x) =
      ∫ x, fderiv ℝ test x v * φ x := by
    calc
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ test x v * φ x := by
        apply integral_congr_ae
        filter_upwards [aux_hcut_cell_corrector_smoothVal_coeFn hΩ φ hφ] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : fderiv ℝ test x = 0 := fderiv_of_notMem_tsupport ℝ
          (fun h => hx (test.tsupport_subset h))
        simp only [hz, ContinuousLinearMap.zero_apply, zero_mul]
  change (∫ x in (Ω : Set (SpatialCoordinates d)), test x *
      (aux_hcut_cell_corrector_smoothData hΩ φ hφ).2 i x) +
    (∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ test x v *
      (aux_hcut_cell_corrector_smoothData hΩ φ hφ).1 x) = 0
  change (∫ x in (Ω : Set (SpatialCoordinates d)), test x *
      (aux_hcut_cell_corrector_smoothGrad hΩ φ hφ i : SpatialCoordinates d → ℝ) x) +
    (∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ test x v *
      (aux_hcut_cell_corrector_smoothVal hΩ φ hφ : SpatialCoordinates d → ℝ) x) = 0
  rw [hleft, hright, hibp, neg_add_cancel]

/-- A globally smooth function on a bounded open domain, as an element of the
proved weak Sobolev graph. -/
noncomputable def aux_hcut_cell_corrector_smoothSobolev
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : weakSobolevGraph Ω :=
  ⟨aux_hcut_cell_corrector_smoothData hΩ φ hφ, aux_hcut_cell_corrector_smoothData_mem hΩ φ hφ⟩

theorem aux_hcut_cell_corrector_smoothSobolev_val_coeFn
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ((aux_hcut_cell_corrector_smoothSobolev hΩ φ hφ : SobolevData Ω).1 :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] φ :=
  aux_hcut_cell_corrector_smoothVal_coeFn hΩ φ hφ

theorem aux_hcut_cell_corrector_smoothSobolev_grad_coeFn
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    ((aux_hcut_cell_corrector_smoothSobolev hΩ φ hφ : SobolevData Ω).2 i :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      (fun x => fderiv ℝ φ x (Homogenization.basisVec i)) :=
  aux_hcut_cell_corrector_smoothGrad_coeFn hΩ φ hφ i

end Paper
end
end

-- ===== module HCut.CellCorrectorStmt =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Split-off half of `aux_hcut_cell_corrector` (weak maximum principle), so each
half gets its own `200000`-heartbeat budget. Same hypotheses as the main theorem's
`hdpos` branch, with `u` and `e` threaded in explicitly (`u` via its defining
equation to `dirichletMinimizer`, since it is a genuine local `set`, and `e` via
the same pointwise equation `heval` that `exists_nativeH10Function_of_killedSobolevGraph`
produces at the call site) so the same witnesses can be reused by the energy half. -/
theorem aux_hcut_cell_corrector_maxprinciple {d : ℕ} [NeZero d] (y : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube y r hr)) (Acont : SpatialCoordinates d → ℝ)
    (hAc : Continuous Acont) (hApos : ∀ x, 0 < Acont x)
    (ha : ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      (a.val : SpatialCoordinates d → ℝ) x = Acont x)
    (f : SpatialCoordinates d → ℝ) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hQconv : Homogenization.IsOpenBoundedConvexDomain (centeredCube y r hr : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube y r hr),
        ‖(v : SobolevData (centeredCube y r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube y r hr)) v‖)
    (b : weakSobolevGraph (centeredCube y r hr))
    (hbval : ((b : SobolevData (centeredCube y r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))]
          (fun w => f w - f y))
    (e : Homogenization.H10Function (centeredCube y r hr : Set (SpatialCoordinates d)))
    (heval : (e : SpatialCoordinates d → ℝ) =
        fun x => ((dirichletMinimizer (killedResponseSpace hP) a b : SobolevData (centeredCube y r hr))
          - (b : SobolevData (centeredCube y r hr))).1 x) :
    ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      0 ≤ f x + e.toH1Function.toFun x ∧ f x + e.toH1Function.toFun x ≤ 1 := by
  set φ : SpatialCoordinates d → ℝ := fun w => f w - f y with hφdef
  have hφ01M : ∀ x, φ x ≤ 1 - f y := by
    intro x; simp only [hφdef]; linarith [(hf01 x).2]
  have hφ01m : ∀ x, -(f y) ≤ φ x := by
    intro x; simp only [hφdef]; linarith [(hf01 x).1]
  set u : weakSobolevGraph (centeredCube y r hr) :=
    dirichletMinimizer (killedResponseSpace hP) a b with hudef
  obtain ⟨gnat, hnat, hgtof, hharm, htr, hheq⟩ :=
    aux_lem_finite_source_comparison_trial_minimizer_bridge
      (le_refl (centeredCube y r hr)) hP a ha b hbval
  have hbr : (⟨sobolevDataRestrict (le_refl (centeredCube y r hr))
      (b : SobolevData (centeredCube y r hr)),
      sobolevDataRestrict_mem_weak (le_refl (centeredCube y r hr))
        (b : weakSobolevGraph (centeredCube y r hr)).property⟩ :
      weakSobolevGraph (centeredCube y r hr)) = b := by
    apply Subtype.ext
    show sobolevDataRestrict (le_refl (centeredCube y r hr))
        (b : SobolevData (centeredCube y r hr)) = (b : SobolevData (centeredCube y r hr))
    simp [sobolevDataRestrict, domainLpRestrict_refl]
  have hqu : (dirichletMinimizer (killedResponseSpace hP)
      (positiveCoefficientRestrict (le_refl (centeredCube y r hr)) a)
      (⟨sobolevDataRestrict (le_refl (centeredCube y r hr))
        (b : SobolevData (centeredCube y r hr)),
        sobolevDataRestrict_mem_weak (le_refl (centeredCube y r hr))
          (b : weakSobolevGraph (centeredCube y r hr)).property⟩ :
        weakSobolevGraph (centeredCube y r hr))) = u := by
    rw [hbr, positiveCoefficientRestrict_refl]
  rw [hqu] at hheq
  have hcompact : IsCompact (closedCube y r hr : Set (SpatialCoordinates d)) :=
    (closedCube y r hr).isCompact
  have hsub : (centeredCube y r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube y r hr : Set (SpatialCoordinates d)) :=
    centeredCube_subset_closedCube y hr
  obtain ⟨lam, hlampos, hlamb⟩ := hcompact.exists_forall_le' hAc.continuousOn
    (a := (0 : ℝ)) (fun x _ => hApos x)
  obtain ⟨Lam, hLamb⟩ := hcompact.exists_bound_of_continuousOn hAc.continuousOn
  have hameas : AEStronglyMeasurable Acont
      (volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))) :=
    hAc.aestronglyMeasurable
  have hbounds : ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      lam ≤ Acont x ∧ Acont x ≤ Lam := by
    filter_upwards [ae_restrict_mem (centeredCube y r hr).isOpen.measurableSet] with x hx
    exact ⟨hlamb x (hsub hx), (le_abs_self _).trans (hLamb x (hsub hx))⟩
  have hupper : ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      hnat.toFun x ≤ 1 - f y :=
    aux_lem_finite_source_comparison_trial_ae_le_of_harmonic hQconv hlampos hameas
      hbounds hharm htr (fun x _ => by rw [hgtof x]; exact hφ01M x)
  have hlower : ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      -(f y) ≤ hnat.toFun x :=
    aux_lem_finite_source_comparison_trial_le_ae_of_harmonic hQconv hlampos hameas
      hbounds hharm htr (fun x _ => by rw [hgtof x]; exact hφ01m x)
  have hu_upper : ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      (u : SobolevData (centeredCube y r hr)).1 x ≤ 1 - f y := by
    filter_upwards [hupper, hheq] with x h1 h2
    rw [← h2]; exact h1
  have hu_lower : ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      -(f y) ≤ (u : SobolevData (centeredCube y r hr)).1 x := by
    filter_upwards [hlower, hheq] with x h1 h2
    rw [← h2]; exact h1
  have hsub_fst : ((u : SobolevData (centeredCube y r hr)) -
      (b : SobolevData (centeredCube y r hr))).1
      = (u : SobolevData (centeredCube y r hr)).1 - (b : SobolevData (centeredCube y r hr)).1 :=
    rfl
  have he_eq : (e : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))]
      fun x => (u : SobolevData (centeredCube y r hr)).1 x - φ x := by
    filter_upwards [Lp.coeFn_sub (u : SobolevData (centeredCube y r hr)).1
        (b : SobolevData (centeredCube y r hr)).1, hbval] with x hx hbx
    show (e : SpatialCoordinates d → ℝ) x = _
    rw [congrFun heval x, hsub_fst]
    show ((u : SobolevData (centeredCube y r hr)).1 -
        (b : SobolevData (centeredCube y r hr)).1) x = _
    rw [hx, Pi.sub_apply, hbx]
  filter_upwards [he_eq, hu_upper, hu_lower] with x h1 h2 h3
  have hex : e.toH1Function.toFun x = (u : SobolevData (centeredCube y r hr)).1 x - φ x := h1
  have hrw : f x + ((u : SobolevData (centeredCube y r hr)).1 x - φ x)
      = (u : SobolevData (centeredCube y r hr)).1 x + f y := by
    simp only [hφdef]; ring
  rw [hex, hrw]
  exact ⟨by linarith, by linarith⟩

/-- Split-off half of `aux_hcut_cell_corrector` (`Acont`-energy of `∇f + ∇e` equals
`localGradientEnergy a` of `u`), so each half gets its own `200000`-heartbeat budget.
`hbgrad_f` records the (already-known) gradient of `b` directly in terms of `f`
(rather than the smooth datum's own name `φ = f - f y`, since `fderiv` kills the
constant `f y` anyway) so this half does not need to re-derive it. -/
theorem aux_hcut_cell_corrector_energy {d : ℕ} [NeZero d] (y : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube y r hr)) (Acont : SpatialCoordinates d → ℝ)
    (ha : ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      (a.val : SpatialCoordinates d → ℝ) x = Acont x)
    (f : SpatialCoordinates d → ℝ)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube y r hr),
        ‖(v : SobolevData (centeredCube y r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube y r hr)) v‖)
    (b : weakSobolevGraph (centeredCube y r hr))
    (hbgrad_f : ∀ i : Fin d, ((b : SobolevData (centeredCube y r hr)).2 i :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict ((centeredCube y r hr) : Set (SpatialCoordinates d))]
        (fun x => fderiv ℝ f x (Homogenization.basisVec i)))
    (e : Homogenization.H10Function (centeredCube y r hr : Set (SpatialCoordinates d)))
    (hegrad : e.toH1Function.grad =
        fun x i => ((dirichletMinimizer (killedResponseSpace hP) a b : SobolevData (centeredCube y r hr))
          - (b : SobolevData (centeredCube y r hr))).2 i x) :
    ∀ (x : SpatialCoordinates d) (ρ : ℝ), 0 < ρ →
      ∫⁻ z in Metric.ball x ρ ∩ (centeredCube y r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (Acont z * Homogenization.vecDot
            ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
            ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)) =
        ENNReal.ofReal (localGradientEnergy a
          (s := Metric.ball x ρ ∩ (centeredCube y r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube y r hr).isOpen.measurableSet)
          (sobolevGradient
            (dirichletMinimizer (killedResponseSpace hP) a b : SobolevData (centeredCube y r hr)))) := by
  set u : weakSobolevGraph (centeredCube y r hr) :=
    dirichletMinimizer (killedResponseSpace hP) a b with hudef
  intro x rho _hrho
  set s : Set (SpatialCoordinates d) := Metric.ball x rho ∩ (centeredCube y r hr : Set _)
    with hsdef
  have hs_sub : s ⊆ (centeredCube y r hr : Set (SpatialCoordinates d)) :=
    Set.inter_subset_right
  have hs_meas : MeasurableSet s :=
    Metric.isOpen_ball.measurableSet.inter (centeredCube y r hr).isOpen.measurableSet
  show (∫⁻ z in s, ENNReal.ofReal (Acont z * Homogenization.vecDot
      ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
      ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z))) =
    ENNReal.ofReal (localGradientEnergy a hs_meas
      (sobolevGradient (u : SobolevData (centeredCube y r hr))))
  have hsub_snd : ∀ i : Fin d, ((u : SobolevData (centeredCube y r hr)) -
      (b : SobolevData (centeredCube y r hr))).2 i
      = (u : SobolevData (centeredCube y r hr)).2 i - (b : SobolevData (centeredCube y r hr)).2 i :=
    fun i => rfl
  have hVeq : ∀ᵐ z ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
        = fun i => (u : SobolevData (centeredCube y r hr)).2 i z := by
    have h1 : ∀ᵐ z ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
        ∀ i : Fin d, e.toH1Function.grad z i
          = (u : SobolevData (centeredCube y r hr)).2 i z -
            (b : SobolevData (centeredCube y r hr)).2 i z := by
      apply ae_all_iff.mpr
      intro i
      filter_upwards [Lp.coeFn_sub ((u : SobolevData (centeredCube y r hr)).2 i)
          ((b : SobolevData (centeredCube y r hr)).2 i)] with z hz
      have hgi : e.toH1Function.grad z i
          = ((u : SobolevData (centeredCube y r hr)) -
            (b : SobolevData (centeredCube y r hr))).2 i z := by
        rw [congrFun (congrFun hegrad z) i]
      rw [hgi, hsub_snd i]
      exact hz
    have h2 : ∀ᵐ z ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
        ∀ i : Fin d, (b : SobolevData (centeredCube y r hr)).2 i z
          = fderiv ℝ f z (Homogenization.basisVec i) := by
      apply ae_all_iff.mpr
      intro i
      filter_upwards [hbgrad_f i] with z hz
      exact hz
    filter_upwards [h1, h2] with z hz1 hz2
    funext i
    show fderiv ℝ f z (Homogenization.basisVec i) + e.toH1Function.grad z i = _
    rw [hz1 i, hz2 i]; ring
  have hvdot : ∀ᵐ z ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      Homogenization.vecDot
        ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
        ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
      = ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2 := by
    filter_upwards [hVeq] with z hz
    rw [hz]
    show Homogenization.vecDot (fun i => (u : SobolevData (centeredCube y r hr)).2 i z)
        (fun i => (u : SobolevData (centeredCube y r hr)).2 i z) = _
    simp only [Homogenization.vecDot, sq]
  have hvdot_s : ∀ᵐ z ∂(volume.restrict s),
      Homogenization.vecDot
        ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
        ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
      = ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2 :=
    ae_restrict_of_ae_restrict_of_subset hs_sub hvdot
  have hAeq_s : ∀ᵐ z ∂(volume.restrict s), Acont z = (a.val : SpatialCoordinates d → ℝ) z :=
    ae_restrict_of_ae_restrict_of_subset hs_sub (ha.mono fun x hx => hx.symm)
  have hintegrand_eq : ∀ᵐ z ∂(volume.restrict s),
      Acont z * Homogenization.vecDot
        ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
        ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
      = (a.val : SpatialCoordinates d → ℝ) z *
          ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2 := by
    filter_upwards [hvdot_s, hAeq_s] with z h1 h2
    rw [h1, h2]
  have hinteg_i : ∀ i : Fin d, Integrable
      (fun z => (a.val : SpatialCoordinates d → ℝ) z *
        ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2)
      (volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))) := by
    intro i
    have hint := integrable_weighted_inner a.val
      ((u : SobolevData (centeredCube y r hr)).2 i) ((u : SobolevData (centeredCube y r hr)).2 i)
    simpa [sq, RCLike.inner_apply, mul_comm] using hint
  have hinteg_sum : Integrable
      (fun z => (a.val : SpatialCoordinates d → ℝ) z *
        ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2)
      (volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))) := by
    have heq : (fun z => (a.val : SpatialCoordinates d → ℝ) z *
          ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2)
        = fun z => ∑ i : Fin d, (a.val : SpatialCoordinates d → ℝ) z *
          ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2 := by
      funext z; rw [Finset.mul_sum]
    rw [heq]
    exact integrable_finset_sum _ (fun i _ => hinteg_i i)
  have hinteg_sum_s : Integrable
      (fun z => (a.val : SpatialCoordinates d → ℝ) z *
        ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2)
      (volume.restrict s) := by
    rw [← Measure.restrict_restrict_of_subset hs_sub]
    exact hinteg_sum.restrict
  have hnonneg_s : 0 ≤ᵐ[volume.restrict s]
      (fun z => (a.val : SpatialCoordinates d → ℝ) z *
        ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs_sub
      (positiveCoefficient_ae_nonneg a)] with z hz2
    exact mul_nonneg hz2 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hLHS : (∫⁻ z in s, ENNReal.ofReal (Acont z * Homogenization.vecDot
      ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
      ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z))) =
      ENNReal.ofReal (∫ z in s, (a.val : SpatialCoordinates d → ℝ) z *
        ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hinteg_sum_s hnonneg_s]
    apply lintegral_congr_ae
    filter_upwards [hintegrand_eq] with z hz
    rw [hz]
  rw [hLHS]
  have hsum_integral : (∫ z in s, (a.val : SpatialCoordinates d → ℝ) z *
        ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2)
      = ∑ i : Fin d, ∫ z in s, (a.val : SpatialCoordinates d → ℝ) z *
          ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2 := by
    have heq : ∀ z, (a.val : SpatialCoordinates d → ℝ) z *
          ∑ i : Fin d, ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2
        = ∑ i : Fin d, (a.val : SpatialCoordinates d → ℝ) z *
          ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2 := by
      intro z; rw [Finset.mul_sum]
    simp_rw [heq]
    refine integral_finset_sum _ (fun i _ => ?_)
    rw [← Measure.restrict_restrict_of_subset hs_sub]
    exact (hinteg_i i).restrict
  rw [hsum_integral]
  have hsgrad_fun : ∀ i : Fin d,
      (sobolevGradient (u : SobolevData (centeredCube y r hr))) i
        = (u : SobolevData (centeredCube y r hr)).2 i := fun i => rfl
  have hset_eq : ∀ i : Fin d,
      (∫ z in s, (a.val : SpatialCoordinates d → ℝ) z *
          ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2)
        = ∫ z in s, (a.val : SpatialCoordinates d → ℝ) z *
            ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2
          ∂volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d)) := by
    intro i
    show (∫ z, (a.val : SpatialCoordinates d → ℝ) z *
        ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2 ∂(volume.restrict s))
      = ∫ z, (a.val : SpatialCoordinates d → ℝ) z *
          ((u : SobolevData (centeredCube y r hr)).2 i z) ^ 2
        ∂((volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))).restrict s)
    rw [Measure.restrict_restrict_of_subset hs_sub]
  rw [Finset.sum_congr rfl (fun i _ => hset_eq i)]
  rw [localGradientEnergy_eq_integral]
  simp only [hsgrad_fun]

/-- **(hCut layer i) Per-cell corrector.**  On a cube `P = centeredCube y r` with a positive coefficient `a`
that agrees a.e. with a continuous positive `Acont`, and a smooth `f ∈ [0,1]`: the zero-source Dirichlet
solution `u` with datum `f - f(y)` exists, and `e := u - b ∈ H¹₀(P)` satisfies `0 ≤ f + e ≤ 1` a.e. (weak
maximum principle, the datum lies in `[-f(y), 1-f(y)]`), and the `Acont`-energy of `∇f + ∇e (= ∇u)` on
`ball x ρ ∩ P` is `localGradientEnergy a` of `u`. -/
theorem aux_hcut_cell_corrector {d : ℕ} (y : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube y r hr)) (Acont : SpatialCoordinates d → ℝ)
    (hAc : Continuous Acont) (hApos : ∀ x, 0 < Acont x)
    (ha : ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
      (a.val : SpatialCoordinates d → ℝ) x = Acont x)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∃ (b u : weakSobolevGraph (centeredCube y r hr))
      (e : Homogenization.H10Function (centeredCube y r hr : Set (SpatialCoordinates d))),
      ((b : SobolevData (centeredCube y r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))]
          (fun w => f w - f y) ∧
      SolvesDirichlet a (fun _ => (0 : ℝ)) b u ∧
      (∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
        0 ≤ f x + e.toH1Function.toFun x ∧ f x + e.toH1Function.toFun x ≤ 1) ∧
      ∀ (x : SpatialCoordinates d) (ρ : ℝ), 0 < ρ →
        ∫⁻ z in Metric.ball x ρ ∩ (centeredCube y r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal (Acont z * Homogenization.vecDot
              ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
              ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)) =
          ENNReal.ofReal (localGradientEnergy a
            (s := Metric.ball x ρ ∩ (centeredCube y r hr : Set (SpatialCoordinates d)))
            (Metric.isOpen_ball.measurableSet.inter (centeredCube y r hr).isOpen.measurableSet)
            (sobolevGradient (u : SobolevData (centeredCube y r hr)))) := by
  classical
  set φ : SpatialCoordinates d → ℝ := fun w => f w - f y with hφdef
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hf.sub contDiff_const
  set b : weakSobolevGraph (centeredCube y r hr) :=
    aux_hcut_cell_corrector_smoothSobolev (centeredCube_isBounded y hr) φ hφ with hbdef
  have hbval : ((b : SobolevData (centeredCube y r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict ((centeredCube y r hr) : Set (SpatialCoordinates d))] φ :=
    aux_hcut_cell_corrector_smoothSobolev_val_coeFn (centeredCube_isBounded y hr) φ hφ
  have hbgrad : ∀ i : Fin d, ((b : SobolevData (centeredCube y r hr)).2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict ((centeredCube y r hr) : Set (SpatialCoordinates d))]
        (fun x => fderiv ℝ φ x (Homogenization.basisVec i)) :=
    fun i => aux_hcut_cell_corrector_smoothSobolev_grad_coeFn (centeredCube_isBounded y hr) φ hφ i
  have hφderiv : ∀ x i, fderiv ℝ φ x (Homogenization.basisVec i)
      = fderiv ℝ f x (Homogenization.basisVec i) := by
    intro x i
    have h1 : fderiv ℝ φ x = fderiv ℝ f x := by
      simp only [hφdef]
      exact fderiv_sub_const (f y)
    rw [h1]
  have hbgrad_f : ∀ i : Fin d, ((b : SobolevData (centeredCube y r hr)).2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict ((centeredCube y r hr) : Set (SpatialCoordinates d))]
        (fun x => fderiv ℝ f x (Homogenization.basisVec i)) := by
    intro i
    filter_upwards [hbgrad i] with x hx
    rw [hx, hφderiv]
  have hφ01M : ∀ x, φ x ≤ 1 - f y := by
    intro x; simp only [hφdef]; linarith [(hf01 x).2]
  have hφ01m : ∀ x, -(f y) ≤ φ x := by
    intro x; simp only [hφdef]; linarith [(hf01 x).1]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- Degenerate case: `Fin d` is empty, so every gradient sum vanishes and
    -- the datum itself already solves the (contentless) equation.
    haveI : IsEmpty (Fin d) := by rw [hd0]; infer_instance
    have hkilled0 : (b : SobolevData (centeredCube y r hr)) - (b : SobolevData (centeredCube y r hr)) ∈ killedSobolevGraph (centeredCube y r hr) := by
      rw [sub_self]; exact (killedSobolevGraph (centeredCube y r hr)).zero_mem
    obtain ⟨e, heval, hegrad⟩ := exists_nativeH10Function_of_killedSobolevGraph
      (⟨(b : SobolevData (centeredCube y r hr)) - (b : SobolevData (centeredCube y r hr)), hkilled0⟩ : killedSobolevGraph (centeredCube y r hr))
    refine ⟨b, b, e, hbval, ⟨hkilled0, ?_⟩, ?_, ?_⟩
    · intro ψ
      rw [sobolevCoefficientForm_apply]
      have hempty : (Finset.univ : Finset (Fin d)) = ∅ := Finset.univ_eq_empty
      rw [hempty, Finset.sum_empty]
      simp
    · have hz : ((b : SobolevData (centeredCube y r hr)) - (b : SobolevData (centeredCube y r hr))).1 = (0 : DomainL2 (centeredCube y r hr)) := by
        rw [sub_self]; rfl
      have he0 : (e : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube y r hr) : Set (SpatialCoordinates d))]
          (0 : SpatialCoordinates d → ℝ) := by
        have hzero := Lp.coeFn_zero ℝ 2 (volume.restrict ((centeredCube y r hr) : Set (SpatialCoordinates d)))
        filter_upwards [hzero] with xpt hxpt
        show (e : SpatialCoordinates d → ℝ) xpt = 0
        rw [congrFun heval xpt]
        show ((b : SobolevData (centeredCube y r hr)) - (b : SobolevData (centeredCube y r hr))).1 xpt = 0
        rw [hz]
        exact hxpt
      filter_upwards [he0] with x hx
      have hx' : e.toH1Function.toFun x = 0 := hx
      rw [hx']
      constructor
      · linarith [(hf01 x).1]
      · linarith [(hf01 x).2]
    · intro x rho _hrho
      have hvz : ∀ z, Homogenization.vecDot
          ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
          ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z) = 0 := by
        intro z; simp [Homogenization.vecDot]
      have hLHSzero : (∫⁻ z in Metric.ball x rho ∩ ((centeredCube y r hr) : Set (SpatialCoordinates d)),
          ENNReal.ofReal (Acont z * Homogenization.vecDot
            ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z)
            ((fun i => fderiv ℝ f z (Homogenization.basisVec i)) + e.toH1Function.grad z))) = 0 := by
        simp [hvz]
      have hRHSzero : localGradientEnergy a
          (s := Metric.ball x rho ∩ ((centeredCube y r hr) : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube y r hr).isOpen.measurableSet)
          (sobolevGradient (b : SobolevData (centeredCube y r hr))) = 0 := by
        simp [localGradientEnergy]
      rw [hLHSzero, hRHSzero]
      simp
  · haveI : NeZero d := ⟨hdpos.ne'⟩
    have hQconv : Homogenization.IsOpenBoundedConvexDomain (centeredCube y r hr : Set (SpatialCoordinates d)) :=
      lane2_isOpenBoundedConvexDomain_centeredCube y hr
    have hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube y r hr),
        ‖(v : SobolevData (centeredCube y r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube y r hr)) v‖ :=
      (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
        (centeredCube y r hr) hQconv).1
    have hsolve : SolvesDirichlet a (fun _ => (0 : ℝ)) b
        (dirichletMinimizer (killedResponseSpace hP) a b) :=
      aux_lem_finite_source_comparison_minimizer_solves_zero hP a b
    set u : weakSobolevGraph (centeredCube y r hr) :=
      dirichletMinimizer (killedResponseSpace hP) a b with hudef
    obtain ⟨e, heval, hegrad⟩ := exists_nativeH10Function_of_killedSobolevGraph
      (⟨(u : SobolevData (centeredCube y r hr)) - (b : SobolevData (centeredCube y r hr)),
        hsolve.1⟩ : killedSobolevGraph (centeredCube y r hr))
    exact ⟨b, u, e, hbval, hsolve,
      aux_hcut_cell_corrector_maxprinciple y hr a Acont hAc hApos ha f hf01 hQconv hP b hbval e heval,
      aux_hcut_cell_corrector_energy y hr a Acont ha f hP b hbgrad_f e hegrad⟩

end Paper
end
end

-- ===== module HCut.AssembleA =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hcut_cell_eq (h : ℝ) (hh : 0 < h) (k : Fin d → ℤ) :
    (centeredCube (HCut.aux_hcut_cc h k) h hh : Set (SpatialCoordinates d)) = HCut.aux_hcut_cell h k := rfl

/-- **Stage A (one pair, regime R2, fixed environment).**  Correctors on the transition cells plus a
uniform per-cell growth constant `Mcell` give an admissible cutoff with ball energy
`≤ 8^d · Mcell · Cfine² · h^{d-2-t} · h^{-1/2} · r^{d-1/2}`. -/
theorem aux_hcut_pair_R2 (hd : 1 ≤ d) (A : SpatialCoordinates d → ℝ) (hA : Continuous A)
    (hApos : ∀ x, 0 < A x)
    (a : ∀ (y : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), PositiveCoefficient (centeredCube y r hr))
    (ha : ∀ (y : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
        ((a y r hr).val : SpatialCoordinates d → ℝ) x = A x)
    (R1 R2 h t : ℝ) (hh : 0 < h) (hh1 : h ≤ 1 / 2) (ht : t = (d : ℝ) - 1 / 2)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hf1 : ∀ x, ‖x‖ ≤ R1 + h → f x = 1) (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0)
    (G : ℝ) (hG : 0 ≤ G)
    (hgrowth : ∀ k : Fin d → ℤ, HCut.aux_hcut_IsTrans h R1 R2 k →
      ∀ (b u : weakSobolevGraph (centeredCube (HCut.aux_hcut_cc h k) h hh)),
        ((b : SobolevData (centeredCube (HCut.aux_hcut_cc h k) h hh)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (HCut.aux_hcut_cc h k) h hh : Set (SpatialCoordinates d))]
          (fun w => f w - f (HCut.aux_hcut_cc h k)) →
        SolvesDirichlet (a (HCut.aux_hcut_cc h k) h hh) (fun _ => (0 : ℝ)) b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube (HCut.aux_hcut_cc h k) h hh →
          0 < rad → rad ≤ 1 →
          localGradientEnergy (a (HCut.aux_hcut_cc h k) h hh)
              (s := Metric.ball x rad ∩
                (centeredCube (HCut.aux_hcut_cc h k) h hh : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter
                (centeredCube (HCut.aux_hcut_cc h k) h hh).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube (HCut.aux_hcut_cc h k) h hh))) ≤
            G * rad ^ t) :
    ∃ chi : Homogenization.H10Function (Metric.ball (0 : SpatialCoordinates d) R2),
      (∀ x, 0 ≤ chi.toH1Function.toFun x ∧ chi.toH1Function.toFun x ≤ 1) ∧
      (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) R1, chi.toH1Function.toFun x = 1) ∧
      tsupport chi.toH1Function.toFun ⊆ Metric.ball (0 : SpatialCoordinates d) R2 ∧
      ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
        ∫⁻ z in Metric.ball x r ∩ Metric.ball (0 : SpatialCoordinates d) R2, ENNReal.ofReal (A z *
            Homogenization.vecDot (chi.toH1Function.grad z) (chi.toH1Function.grad z)) ≤
          ENNReal.ofReal (8 ^ d * G * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2)) := by
  refine HCut.aux_hcut_hcut_core hd A hApos R1 R2 h G hh hh1 hG f hf hf01 hf1 hf0 ?_
  intro k hk
  obtain ⟨b, u, e, htrace, hsolve, hbounds, henergy⟩ :=
    aux_hcut_cell_corrector (HCut.aux_hcut_cc h k) hh (a (HCut.aux_hcut_cc h k) h hh) A hA hApos (ha _ _ hh) f hf hf01
  refine ⟨e, hbounds, fun y hy ρ hρ hρ1 => ?_⟩
  refine (le_of_eq (henergy y ρ hρ)).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← ht]
  exact hgrowth k hk b u htrace hsolve y ρ hy hρ hρ1

end Paper
end
end

-- ===== module HCut.AssembleR2 =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The real bookkeeping of the R2 clause (weight `3^{-n}`). -/
lemma aux_hcut_R2_real {C0 g h B1 B2 Mc Kcut Crho rho0 : ℝ} (hC0 : 0 < C0) (hg : 0 < g) (hh : 0 < h)
    (h5 : 5 * h ≤ g) (hgr : g ≤ rho0 / 2) (hB1 : B1 = C0 / (g - 3 * h)) (hB2 : B2 = C0 / (g - 3 * h) ^ 2)
    (hMc : 0 ≤ Mc) (h3n : h⁻¹ ≤ Crho / g) (hCrho : 0 ≤ Crho)
    (hK : 8 ^ d * 25 * C0 ^ 2 * Crho * max 1 ((rho0 / 2) ^ 2) * (h * Mc) ≤ Kcut) :
    8 ^ d * (Mc * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 * h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2))) *
        h ^ (-(1 / 2 : ℝ)) ≤ Kcut * g ^ (-5 : ℝ) := by
  have hgh : 2 * g / 5 ≤ g - 3 * h := by linarith
  have hgh0 : 0 < g - 3 * h := by linarith
  have hexp : h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * h ^ (-(1 / 2 : ℝ)) = (h ^ 2)⁻¹ := by
    rw [← Real.rpow_add hh]
    have : (d : ℝ) - 2 - ((d : ℝ) - 1 / 2) + -(1 / 2) = -2 := by ring
    rw [this, Real.rpow_neg hh.le]; norm_cast
  have hC : h * B1 / 2 + h * B1 + h ^ 2 * B2 ≤ h * (5 * C0 / g) := by
    rw [hB1, hB2]
    have e1 : C0 / (g - 3 * h) ≤ C0 / (2 * g / 5) := div_le_div_of_nonneg_left hC0.le (by positivity) hgh
    have e2 : C0 / (g - 3 * h) ^ 2 ≤ C0 / (2 * g / 5) ^ 2 :=
      div_le_div_of_nonneg_left hC0.le (by positivity) (pow_le_pow_left₀ (by positivity) hgh 2)
    have e3 : h * (C0 / (2 * g / 5) ^ 2) ≤ C0 / (2 * g / 5) * (1 / 2) := by
      have ea : C0 / (2 * g / 5) ^ 2 = 25 * C0 / (4 * g ^ 2) := by field_simp; ring
      have eb : C0 / (2 * g / 5) * (1 / 2) = 5 * C0 / (4 * g) := by field_simp; ring
      rw [ea, eb]
      have hh5 : h ≤ g / 5 := by linarith
      calc h * (25 * C0 / (4 * g ^ 2)) ≤ (g / 5) * (25 * C0 / (4 * g ^ 2)) := by gcongr
        _ = 5 * C0 / (4 * g) := by field_simp; ring
    calc h * (C0 / (g - 3 * h)) / 2 + h * (C0 / (g - 3 * h)) + h ^ 2 * (C0 / (g - 3 * h) ^ 2)
        ≤ h * (C0 / (2 * g / 5)) / 2 + h * (C0 / (2 * g / 5)) + h * (h * (C0 / (2 * g / 5) ^ 2)) := by
          rw [show h ^ 2 * (C0 / (g - 3 * h) ^ 2) = h * (h * (C0 / (g - 3 * h) ^ 2)) by ring]
          gcongr
      _ ≤ h * (C0 / (2 * g / 5)) / 2 + h * (C0 / (2 * g / 5)) + h * (C0 / (2 * g / 5) * (1 / 2)) := by
          gcongr
      _ = h * (5 * C0 / g) := by field_simp; ring
  have hg5 : g ^ (-5 : ℝ) = (g ^ 5)⁻¹ := by rw [Real.rpow_neg hg.le]; norm_cast
  rw [hg5, mul_assoc, show Mc * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 *
      h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * h ^ (-(1 / 2 : ℝ)) =
      Mc * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 *
      (h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * h ^ (-(1 / 2 : ℝ))) by ring, hexp]
  have hCsq : (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 ≤ (h * (5 * C0 / g)) ^ 2 := by
    have h0 : 0 ≤ h * B1 / 2 + h * B1 + h ^ 2 * B2 := by
      rw [hB1, hB2]; positivity
    exact pow_le_pow_left₀ h0 hC 2
  have hg2 : g ^ 2 ≤ max 1 ((rho0 / 2) ^ 2) :=
    le_max_of_le_right (pow_le_pow_left₀ hg.le hgr 2)
  have hinv : h⁻¹ * g ≤ Crho := by rwa [le_div_iff₀ hg] at h3n
  rw [le_mul_inv_iff₀ (by positivity)]
  calc 8 ^ d * (Mc * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 * (h ^ 2)⁻¹) * g ^ 5
      ≤ 8 ^ d * (Mc * (h * (5 * C0 / g)) ^ 2 * (h ^ 2)⁻¹) * g ^ 5 := by gcongr
    _ = 8 ^ d * 25 * C0 ^ 2 * (h⁻¹ * g) * g ^ 2 * (h * Mc) := by field_simp; ring
    _ ≤ 8 ^ d * 25 * C0 ^ 2 * Crho * max 1 ((rho0 / 2) ^ 2) * (h * Mc) := by gcongr
    _ ≤ Kcut := hK

end Paper
end
end

-- ===== module HCut.CubeCutoffStmt =====
section
open Filter Topology Set

noncomputable section
namespace HCut

/-- A continuous function that vanishes outside `(0,1)` is globally bounded. -/
private lemma aux_cubecutoff_bound_of_vanishing (h : ℝ → ℝ) (hh : Continuous h)
    (hh0 : ∀ t, t < 0 → h t = 0) (hh1 : ∀ t, 1 < t → h t = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t, |h t| ≤ c := by
  obtain ⟨c, hc⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hh.continuousOn
  refine ⟨max c 0, le_max_right _ _, fun t => ?_⟩
  rcases lt_or_ge t 0 with ht | ht
  · simp [hh0 t ht]
  rcases lt_or_ge 1 t with ht' | ht'
  · simp [hh1 t ht']
  · exact (hc t ⟨ht, ht'⟩).trans (le_max_left _ _)

/-- Differentiability, continuity, and vanishing facts for `deriv Real.smoothTransition` and its
own derivative, all following from `Real.smoothTransition` being `ContDiff ℝ ⊤`. -/
private lemma aux_cubecutoff_T_facts :
    Differentiable ℝ Real.smoothTransition ∧ Differentiable ℝ (deriv Real.smoothTransition) ∧
      Continuous (deriv Real.smoothTransition) ∧ Continuous (deriv (deriv Real.smoothTransition)) ∧
      (∀ t, t < 0 → deriv Real.smoothTransition t = 0) ∧
      (∀ t, 1 < t → deriv Real.smoothTransition t = 0) ∧
      (∀ t, t < 0 → deriv (deriv Real.smoothTransition) t = 0) ∧
      (∀ t, 1 < t → deriv (deriv Real.smoothTransition) t = 0) := by
  have hTz : ∀ t, t ≤ 0 → Real.smoothTransition t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos ht
  have hTo : ∀ t, 1 ≤ t → Real.smoothTransition t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le ht
  have hTdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have hT2 : ContDiff ℝ (2 : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hT2' : ContDiff ℝ ((1 : ℕ∞) + 1) Real.smoothTransition := by convert hT2 using 2
  have hdT1 : ContDiff ℝ (1 : ℕ∞) (deriv Real.smoothTransition) :=
    (contDiff_succ_iff_deriv.mp hT2').2.2
  have hdTdiff : Differentiable ℝ (deriv Real.smoothTransition) := hdT1.differentiable (by norm_num)
  have hdTcont : Continuous (deriv Real.smoothTransition) := hdT1.continuous
  have hdT1' : ContDiff ℝ ((0 : ℕ∞) + 1) (deriv Real.smoothTransition) := by convert hdT1 using 2
  have hddTcont : Continuous (deriv (deriv Real.smoothTransition)) :=
    (contDiff_succ_iff_deriv.mp hdT1').2.2.continuous
  have hdTz : ∀ t, t < 0 → deriv Real.smoothTransition t = 0 := by
    intro t ht
    have heq : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) (fun s hs => hTz s hs.le)
    simpa using heq.deriv_eq
  have hdTo : ∀ t, 1 < t → deriv Real.smoothTransition t = 0 := by
    intro t ht
    have heq : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) (fun s hs => hTo s hs.le)
    simpa using heq.deriv_eq
  have hddTz : ∀ t, t < 0 → deriv (deriv Real.smoothTransition) t = 0 := by
    intro t ht
    have heq : deriv Real.smoothTransition =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) (fun s hs => hdTz s hs)
    simpa using heq.deriv_eq
  have hddTo : ∀ t, 1 < t → deriv (deriv Real.smoothTransition) t = 0 := by
    intro t ht
    have heq : deriv Real.smoothTransition =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) (fun s hs => hdTo s hs)
    simpa using heq.deriv_eq
  exact ⟨hTdiff, hdTdiff, hdTcont, hddTcont, hdTz, hdTo, hddTz, hddTo⟩

/-- `deriv Real.smoothTransition` is globally bounded. -/
theorem aux_smoothTransition_deriv_bounded :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ c := by
  obtain ⟨_, _, hdTcont, _, hdTz, hdTo, _, _⟩ := aux_cubecutoff_T_facts
  exact aux_cubecutoff_bound_of_vanishing _ hdTcont hdTz hdTo

/-- `deriv (deriv Real.smoothTransition)` is globally bounded. -/
theorem aux_smoothTransition_deriv2_bounded :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ c := by
  obtain ⟨_, _, _, hddTcont, _, _, hddTz, hddTo⟩ := aux_cubecutoff_T_facts
  exact aux_cubecutoff_bound_of_vanishing _ hddTcont hddTz hddTo

/-- 1-D profile of the smooth cube cutoff: `φ(s) = T((a2-s)/g)·T((a2+s)/g)`, `g = a2 - a1`. -/
def aux_cubecutoff_phi (a1 a2 s : ℝ) : ℝ :=
  Real.smoothTransition ((a2 - s) / (a2 - a1)) * Real.smoothTransition ((a2 + s) / (a2 - a1))

theorem aux_cubecutoff_phi_mem (a1 a2 s : ℝ) :
    0 ≤ aux_cubecutoff_phi a1 a2 s ∧ aux_cubecutoff_phi a1 a2 s ≤ 1 := by
  unfold aux_cubecutoff_phi
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)⟩

theorem aux_cubecutoff_phi_one (a1 a2 s : ℝ) (h1 : 0 < a1) (h12 : a1 < a2) (hs : |s| ≤ a1) :
    aux_cubecutoff_phi a1 a2 s = 1 := by
  unfold aux_cubecutoff_phi
  have hg : 0 < a2 - a1 := sub_pos.mpr h12
  rw [abs_le] at hs
  have h1' : (1 : ℝ) ≤ (a2 - s) / (a2 - a1) := by
    rw [le_div_iff₀ hg]; linarith [hs.2]
  have h2' : (1 : ℝ) ≤ (a2 + s) / (a2 - a1) := by
    rw [le_div_iff₀ hg]; linarith [hs.1]
  rw [Real.smoothTransition.one_of_one_le h1', Real.smoothTransition.one_of_one_le h2', one_mul]

theorem aux_cubecutoff_phi_zero (a1 a2 s : ℝ) (h1 : 0 < a1) (h12 : a1 < a2) (hs : a2 ≤ |s|) :
    aux_cubecutoff_phi a1 a2 s = 0 := by
  unfold aux_cubecutoff_phi
  have hg : 0 < a2 - a1 := sub_pos.mpr h12
  rcases le_abs.mp hs with h | h
  · have : (a2 - s) / (a2 - a1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hg.le
    rw [Real.smoothTransition.zero_of_nonpos this, zero_mul]
  · have : (a2 + s) / (a2 - a1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hg.le
    rw [Real.smoothTransition.zero_of_nonpos this, mul_zero]

theorem aux_cubecutoff_phi_contDiff (a1 a2 : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (aux_cubecutoff_phi a1 a2) := by
  unfold aux_cubecutoff_phi
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (a2 - s) / (a2 - a1)) :=
    (contDiff_const.sub contDiff_id).div_const _
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (a2 + s) / (a2 - a1)) :=
    (contDiff_const.add contDiff_id).div_const _
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

/-- `deriv (aux_cubecutoff_phi a1 a2)` is bounded by `K1 / (a2 - a1)` for a universal `K1`. -/
theorem aux_cubecutoff_phi_deriv1_bound :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ a1 a2 s : ℝ, 0 < a1 → a1 < a2 →
      |deriv (aux_cubecutoff_phi a1 a2) s| ≤ K1 / (a2 - a1) := by
  obtain ⟨c1, hc1nn, hc1⟩ := aux_smoothTransition_deriv_bounded
  obtain ⟨hTdiff, _, _, _, _, _, _, _⟩ := aux_cubecutoff_T_facts
  refine ⟨2 * c1, by positivity, fun a1 a2 s h1 h12 => ?_⟩
  set g := a2 - a1 with hg_def
  have hg_pos : 0 < g := sub_pos.mpr h12
  set u : ℝ → ℝ := fun s => (a2 - s) / g with hu_def
  set v : ℝ → ℝ := fun s => (a2 + s) / g with hv_def
  have hu_deriv : ∀ s, HasDerivAt u (-1 / g) s := fun s => by
    simpa [hu_def] using ((hasDerivAt_const s a2).sub (hasDerivAt_id s)).div_const g
  have hv_deriv : ∀ s, HasDerivAt v (1 / g) s := fun s => by
    simpa [hv_def] using ((hasDerivAt_const s a2).add (hasDerivAt_id s)).div_const g
  have hTu_deriv : ∀ s, HasDerivAt (fun s => Real.smoothTransition (u s))
      (deriv Real.smoothTransition (u s) * (-1 / g)) s := fun s =>
    (hTdiff.differentiableAt.hasDerivAt).comp s (hu_deriv s)
  have hTv_deriv : ∀ s, HasDerivAt (fun s => Real.smoothTransition (v s))
      (deriv Real.smoothTransition (v s) * (1 / g)) s := fun s =>
    (hTdiff.differentiableAt.hasDerivAt).comp s (hv_deriv s)
  have hφ_deriv : HasDerivAt (aux_cubecutoff_phi a1 a2)
      (deriv Real.smoothTransition (u s) * (-1 / g) * Real.smoothTransition (v s) +
        Real.smoothTransition (u s) * (deriv Real.smoothTransition (v s) * (1 / g))) s := by
    have := (hTu_deriv s).fun_mul (hTv_deriv s)
    simpa [aux_cubecutoff_phi, u, v, hu_def, hv_def, hg_def] using this
  rw [hφ_deriv.deriv]
  calc |deriv Real.smoothTransition (u s) * (-1 / g) * Real.smoothTransition (v s) +
        Real.smoothTransition (u s) * (deriv Real.smoothTransition (v s) * (1 / g))|
      ≤ |deriv Real.smoothTransition (u s) * (-1 / g) * Real.smoothTransition (v s)| +
        |Real.smoothTransition (u s) * (deriv Real.smoothTransition (v s) * (1 / g))| :=
        abs_add_le _ _
    _ = |deriv Real.smoothTransition (u s)| * (1 / g) * |Real.smoothTransition (v s)| +
        |Real.smoothTransition (u s)| * (|deriv Real.smoothTransition (v s)| * (1 / g)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_pos (by positivity : (0:ℝ) < 1/g),
          show |(-1:ℝ)/g| = 1/g by rw [abs_div]; simp [abs_of_pos hg_pos]]
    _ ≤ c1 * (1/g) * 1 + 1 * (c1 * (1/g)) := by
        gcongr
        · exact hc1 _
        · rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
        · rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
        · exact hc1 _
    _ = 2 * c1 / g := by ring

/-- `deriv (deriv (aux_cubecutoff_phi a1 a2))` is bounded by `K2 / (a2 - a1)^2` for a universal
`K2`. -/
theorem aux_cubecutoff_phi_deriv2_bound :
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ a1 a2 s : ℝ, 0 < a1 → a1 < a2 →
      |deriv (deriv (aux_cubecutoff_phi a1 a2)) s| ≤ K2 / (a2 - a1) ^ 2 := by
  obtain ⟨c1, hc1nn, hc1⟩ := aux_smoothTransition_deriv_bounded
  obtain ⟨c2, hc2nn, hc2⟩ := aux_smoothTransition_deriv2_bounded
  obtain ⟨hTdiff, hdTdiff, _, _, _, _, _, _⟩ := aux_cubecutoff_T_facts
  refine ⟨2 * c2 + 2 * c1 ^ 2, by positivity, fun a1 a2 s h1 h12 => ?_⟩
  set g := a2 - a1 with hg_def
  have hg_pos : 0 < g := sub_pos.mpr h12
  set u : ℝ → ℝ := fun s => (a2 - s) / g with hu_def
  set v : ℝ → ℝ := fun s => (a2 + s) / g with hv_def
  have hu_deriv : ∀ s, HasDerivAt u (-1 / g) s := fun s => by
    simpa [hu_def] using ((hasDerivAt_const s a2).sub (hasDerivAt_id s)).div_const g
  have hv_deriv : ∀ s, HasDerivAt v (1 / g) s := fun s => by
    simpa [hv_def] using ((hasDerivAt_const s a2).add (hasDerivAt_id s)).div_const g
  have hTu_deriv : ∀ s, HasDerivAt (fun s => Real.smoothTransition (u s))
      (deriv Real.smoothTransition (u s) * (-1 / g)) s := fun s =>
    (hTdiff.differentiableAt.hasDerivAt).comp s (hu_deriv s)
  have hTv_deriv : ∀ s, HasDerivAt (fun s => Real.smoothTransition (v s))
      (deriv Real.smoothTransition (v s) * (1 / g)) s := fun s =>
    (hTdiff.differentiableAt.hasDerivAt).comp s (hv_deriv s)
  have hφ_deriv_eq : ∀ s, deriv (aux_cubecutoff_phi a1 a2) s =
      deriv Real.smoothTransition (u s) * (-1 / g) * Real.smoothTransition (v s) +
        Real.smoothTransition (u s) * (deriv Real.smoothTransition (v s) * (1 / g)) := by
    intro s
    have hφ_deriv : HasDerivAt (aux_cubecutoff_phi a1 a2)
        (deriv Real.smoothTransition (u s) * (-1 / g) * Real.smoothTransition (v s) +
          Real.smoothTransition (u s) * (deriv Real.smoothTransition (v s) * (1 / g))) s := by
      have := (hTu_deriv s).fun_mul (hTv_deriv s)
      simpa [aux_cubecutoff_phi, u, v, hu_def, hv_def, hg_def] using this
    exact hφ_deriv.deriv
  have hddTu_deriv : ∀ s, HasDerivAt (fun s => deriv Real.smoothTransition (u s))
      (deriv (deriv Real.smoothTransition) (u s) * (-1 / g)) s := fun s =>
    (hdTdiff.differentiableAt.hasDerivAt).comp s (hu_deriv s)
  have hddTv_deriv : ∀ s, HasDerivAt (fun s => deriv Real.smoothTransition (v s))
      (deriv (deriv Real.smoothTransition) (v s) * (1 / g)) s := fun s =>
    (hdTdiff.differentiableAt.hasDerivAt).comp s (hv_deriv s)
  have hψ1_deriv : ∀ s, HasDerivAt
      (fun s => deriv Real.smoothTransition (u s) * (-1 / g) * Real.smoothTransition (v s))
      (deriv (deriv Real.smoothTransition) (u s) * (-1 / g) * (-1 / g) *
          Real.smoothTransition (v s) +
        deriv Real.smoothTransition (u s) * (-1 / g) *
          (deriv Real.smoothTransition (v s) * (1 / g))) s := fun s => by
    have h1 : HasDerivAt (fun s => deriv Real.smoothTransition (u s) * (-1 / g))
        (deriv (deriv Real.smoothTransition) (u s) * (-1 / g) * (-1 / g)) s := by
      simpa [mul_comm, mul_assoc] using (hddTu_deriv s).mul_const (-1 / g)
    exact h1.fun_mul (hTv_deriv s)
  have hψ2_deriv : ∀ s, HasDerivAt
      (fun s => Real.smoothTransition (u s) * (deriv Real.smoothTransition (v s) * (1 / g)))
      (deriv Real.smoothTransition (u s) * (-1 / g) *
          (deriv Real.smoothTransition (v s) * (1 / g)) +
        Real.smoothTransition (u s) *
          (deriv (deriv Real.smoothTransition) (v s) * (1 / g) * (1 / g))) s := fun s => by
    have h2 : HasDerivAt (fun s => deriv Real.smoothTransition (v s) * (1 / g))
        (deriv (deriv Real.smoothTransition) (v s) * (1 / g) * (1 / g)) s := by
      simpa [mul_comm, mul_assoc] using (hddTv_deriv s).mul_const (1 / g)
    exact (hTu_deriv s).fun_mul h2
  have hφ''_deriv_eq : deriv (deriv (aux_cubecutoff_phi a1 a2)) s =
      (deriv (deriv Real.smoothTransition) (u s) * (-1 / g) * (-1 / g) *
          Real.smoothTransition (v s) +
        deriv Real.smoothTransition (u s) * (-1 / g) *
          (deriv Real.smoothTransition (v s) * (1 / g))) +
        (deriv Real.smoothTransition (u s) * (-1 / g) *
            (deriv Real.smoothTransition (v s) * (1 / g)) +
          Real.smoothTransition (u s) *
            (deriv (deriv Real.smoothTransition) (v s) * (1 / g) * (1 / g))) := by
    have hcongr : deriv (aux_cubecutoff_phi a1 a2) =ᶠ[𝓝 s]
        (fun s => deriv Real.smoothTransition (u s) * (-1 / g) * Real.smoothTransition (v s) +
          Real.smoothTransition (u s) * (deriv Real.smoothTransition (v s) * (1 / g))) :=
      Filter.Eventually.of_forall hφ_deriv_eq
    have := (hψ1_deriv s).fun_add (hψ2_deriv s)
    exact (this.congr_of_eventuallyEq hcongr).deriv
  rw [hφ''_deriv_eq]
  have hA : |deriv (deriv Real.smoothTransition) (u s) * (-1 / g) * (-1 / g) *
      Real.smoothTransition (v s)| ≤ c2 / g ^ 2 := by
    have h1 : |deriv (deriv Real.smoothTransition) (u s) * (-1 / g) * (-1 / g) *
        Real.smoothTransition (v s)| =
        |deriv (deriv Real.smoothTransition) (u s)| * (1 / g) * (1 / g) *
          |Real.smoothTransition (v s)| := by
      rw [abs_mul, abs_mul, abs_mul,
        show |(-1:ℝ)/g| = 1/g by rw [abs_div]; simp [abs_of_pos hg_pos]]
    rw [h1]
    calc |deriv (deriv Real.smoothTransition) (u s)| * (1/g) * (1/g) * |Real.smoothTransition (v s)|
        ≤ c2 * (1/g) * (1/g) * 1 := by
          gcongr
          · exact hc2 _
          · rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
      _ = c2 / g ^ 2 := by ring
  have hB : |deriv Real.smoothTransition (u s) * (-1 / g) *
      (deriv Real.smoothTransition (v s) * (1 / g))| ≤ c1 ^ 2 / g ^ 2 := by
    have h1 : |deriv Real.smoothTransition (u s) * (-1 / g) *
        (deriv Real.smoothTransition (v s) * (1 / g))| =
        |deriv Real.smoothTransition (u s)| * (1 / g) *
          (|deriv Real.smoothTransition (v s)| * (1 / g)) := by
      rw [abs_mul, abs_mul, abs_mul,
        show |(-1:ℝ)/g| = 1/g by rw [abs_div]; simp [abs_of_pos hg_pos],
        abs_of_pos (by positivity : (0:ℝ) < 1/g)]
    rw [h1]
    calc |deriv Real.smoothTransition (u s)| * (1/g) * (|deriv Real.smoothTransition (v s)| * (1/g))
        ≤ c1 * (1/g) * (c1 * (1/g)) := by
          gcongr
          · exact hc1 _
          · exact hc1 _
      _ = c1 ^ 2 / g ^ 2 := by ring
  have hD : |Real.smoothTransition (u s) *
      (deriv (deriv Real.smoothTransition) (v s) * (1 / g) * (1 / g))| ≤ c2 / g ^ 2 := by
    have h1 : |Real.smoothTransition (u s) *
        (deriv (deriv Real.smoothTransition) (v s) * (1 / g) * (1 / g))| =
        |Real.smoothTransition (u s)| *
          (|deriv (deriv Real.smoothTransition) (v s)| * (1 / g) * (1 / g)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/g)]
    rw [h1]
    calc |Real.smoothTransition (u s)| *
          (|deriv (deriv Real.smoothTransition) (v s)| * (1/g) * (1/g))
        ≤ 1 * (c2 * (1/g) * (1/g)) := by
          gcongr
          · rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
          · exact hc2 _
      _ = c2 / g ^ 2 := by ring
  calc |(deriv (deriv Real.smoothTransition) (u s) * (-1 / g) * (-1 / g) *
          Real.smoothTransition (v s) +
        deriv Real.smoothTransition (u s) * (-1 / g) *
          (deriv Real.smoothTransition (v s) * (1 / g))) +
        (deriv Real.smoothTransition (u s) * (-1 / g) *
            (deriv Real.smoothTransition (v s) * (1 / g)) +
          Real.smoothTransition (u s) *
            (deriv (deriv Real.smoothTransition) (v s) * (1 / g) * (1 / g)))|
      ≤ |deriv (deriv Real.smoothTransition) (u s) * (-1 / g) * (-1 / g) *
            Real.smoothTransition (v s) +
          deriv Real.smoothTransition (u s) * (-1 / g) *
            (deriv Real.smoothTransition (v s) * (1 / g))| +
          |deriv Real.smoothTransition (u s) * (-1 / g) *
              (deriv Real.smoothTransition (v s) * (1 / g)) +
            Real.smoothTransition (u s) *
              (deriv (deriv Real.smoothTransition) (v s) * (1 / g) * (1 / g))| := abs_add_le _ _
    _ ≤ (|deriv (deriv Real.smoothTransition) (u s) * (-1 / g) * (-1 / g) *
              Real.smoothTransition (v s)| +
            |deriv Real.smoothTransition (u s) * (-1 / g) *
                (deriv Real.smoothTransition (v s) * (1 / g))|) +
          (|deriv Real.smoothTransition (u s) * (-1 / g) *
                (deriv Real.smoothTransition (v s) * (1 / g))| +
            |Real.smoothTransition (u s) *
                (deriv (deriv Real.smoothTransition) (v s) * (1 / g) * (1 / g))|) := by
        gcongr <;> exact abs_add_le _ _
    _ ≤ (c2/g^2 + c1^2/g^2) + (c1^2/g^2 + c2/g^2) := by gcongr
    _ = (2 * c2 + 2 * c1 ^ 2) / g ^ 2 := by ring

variable {d : ℕ} {φ : ℝ → ℝ}

theorem aux_cubecutoff_prod_abs (hφmem : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (y : Fin d → ℝ)
    (s : Finset (Fin d)) : |∏ j ∈ s, φ (y j)| ≤ 1 := by
  rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => (hφmem (y j)).1)]
  exact Finset.prod_le_one (fun j _ => (hφmem (y j)).1) (fun j _ => (hφmem (y j)).2)

theorem aux_cubecutoff_proj_norm (i : Fin d) :
    ‖(ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  simpa using norm_le_pi_norm v i

theorem aux_cubecutoff_prod_eq_one (r : ℝ) (hφone : ∀ t, |t| ≤ r → φ t = 1) (y : Fin d → ℝ)
    (hy : ‖y‖ ≤ r) : ∏ i, φ (y i) = 1 :=
  Finset.prod_eq_one fun i _ => hφone (y i) (norm_le_pi_norm y i |>.trans hy)

theorem aux_cubecutoff_prod_eq_zero (r : ℝ) (hr : 0 < r) (hφzero : ∀ t, r ≤ |t| → φ t = 0)
    (y : Fin d → ℝ) (hy : r ≤ ‖y‖) : ∏ i, φ (y i) = 0 := by
  have h_exists : ∃ i, r ≤ |y i| := by
    by_contra h_all
    push_neg at h_all
    have h_norm_lt : ‖y‖ < r := (pi_norm_lt_iff hr).mpr h_all
    linarith
  obtain ⟨i, hi⟩ := h_exists
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hφzero (y i) hi)

theorem aux_cubecutoff_prod_contDiff (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin d → ℝ => ∏ i, φ (y i)) :=
  contDiff_prod fun i _ => hφ.comp (contDiff_apply ℝ ℝ i)

theorem aux_cubecutoff_fderiv1 (hφdiff : Differentiable ℝ φ) (y : Fin d → ℝ) :
    HasFDerivAt (fun y : Fin d → ℝ => ∏ i, φ (y i))
      (∑ i : Fin d, (∏ j ∈ Finset.univ.erase i, φ (y j)) •
        (deriv φ (y i) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))) y := by
  have hfam : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun z : Fin d → ℝ => φ (z i))
        (deriv φ (y i) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) y :=
    fun i _ => (hφdiff.differentiableAt.hasDerivAt).comp_hasFDerivAt y (hasFDerivAt_apply i y)
  simpa using HasFDerivAt.finset_prod hfam

theorem aux_cubecutoff_fderiv1_bound (hφmem : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1)
    (hφdiff : Differentiable ℝ φ) (c1 : ℝ) (hc1 : ∀ t, |deriv φ t| ≤ c1) (y : Fin d → ℝ) :
    ‖fderiv ℝ (fun y : Fin d → ℝ => ∏ i, φ (y i)) y‖ ≤ (d : ℝ) * c1 := by
  rw [(aux_cubecutoff_fderiv1 hφdiff y).fderiv]
  calc ‖(∑ i : Fin d, (∏ j ∈ Finset.univ.erase i, φ (y j)) •
          (deriv φ (y i) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)))‖
      ≤ ∑ i : Fin d, ‖(∏ j ∈ Finset.univ.erase i, φ (y j)) •
          (deriv φ (y i) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (1 : ℝ) * (c1 * 1) := by
        have hc1nn : 0 ≤ c1 := (abs_nonneg _).trans (hc1 0)
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr <;>
          first
          | exact aux_cubecutoff_prod_abs hφmem y _
          | exact hc1 _
          | exact aux_cubecutoff_proj_norm i
    _ = (d : ℝ) * c1 := by simp

/-- The derivative of the "all but `i`" partial product, at a fixed base point `x`. -/
def aux_cubecutoff_DA (d : ℕ) (φ : ℝ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ j ∈ Finset.univ.erase i, (∏ k ∈ (Finset.univ.erase i).erase j, φ (x k)) •
    (deriv φ (x j) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ))

/-- The derivative of `y ↦ deriv φ (y i) * ∏_{j≠i} φ (y j)`, at a fixed base point `x`. -/
def aux_cubecutoff_Dg (d : ℕ) (φ : ℝ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  deriv φ (x i) • aux_cubecutoff_DA d φ x i +
    (∏ j ∈ Finset.univ.erase i, φ (x j)) •
      (deriv (deriv φ) (x i) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))

theorem aux_cubecutoff_fderiv2_B (hφdiff : Differentiable ℝ φ) (x : Fin d → ℝ) (i : Fin d) :
    HasFDerivAt (fun y : Fin d → ℝ => ∏ j ∈ Finset.univ.erase i, φ (y j))
      (aux_cubecutoff_DA d φ x i) x := by
  have hfam : ∀ j ∈ Finset.univ.erase i,
      HasFDerivAt (fun z : Fin d → ℝ => φ (z j))
        (deriv φ (x j) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)) x :=
    fun j _ => (hφdiff.differentiableAt.hasDerivAt).comp_hasFDerivAt x (hasFDerivAt_apply j x)
  exact HasFDerivAt.finset_prod hfam

theorem aux_cubecutoff_fderiv2_B_bound (hφmem : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (c1 : ℝ)
    (hc1 : ∀ t, |deriv φ t| ≤ c1) (x : Fin d → ℝ) (i : Fin d) :
    ‖aux_cubecutoff_DA d φ x i‖ ≤ ((Finset.univ.erase i).card : ℝ) * c1 := by
  unfold aux_cubecutoff_DA
  have hc1nn : 0 ≤ c1 := (abs_nonneg _).trans (hc1 0)
  calc ‖(∑ j ∈ Finset.univ.erase i, (∏ k ∈ (Finset.univ.erase i).erase j, φ (x k)) •
          (deriv φ (x j) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)))‖
      ≤ ∑ j ∈ Finset.univ.erase i, ‖(∏ k ∈ (Finset.univ.erase i).erase j, φ (x k)) •
          (deriv φ (x j) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) * (c1 * 1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr <;>
          first
          | exact aux_cubecutoff_prod_abs hφmem x _
          | exact hc1 _
          | exact aux_cubecutoff_proj_norm j
    _ = ((Finset.univ.erase i).card : ℝ) * c1 := by rw [Finset.sum_const]; push_cast; ring

theorem aux_cubecutoff_card_erase (i : Fin d) : ((Finset.univ.erase i).card : ℝ) = (d : ℝ) - 1 := by
  have hd1 : 1 ≤ d := lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub hd1, Nat.cast_one]

theorem aux_cubecutoff_fderiv2_g (hφdiff : Differentiable ℝ φ) (hφ'diff : Differentiable ℝ (deriv φ))
    (x : Fin d → ℝ) (i : Fin d) : HasFDerivAt
      (fun y : Fin d → ℝ => deriv φ (y i) * ∏ j ∈ Finset.univ.erase i, φ (y j))
      (aux_cubecutoff_Dg d φ x i) x := by
  have hA : HasFDerivAt (fun y : Fin d → ℝ => deriv φ (y i))
      (deriv (deriv φ) (x i) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) x :=
    (hφ'diff.differentiableAt.hasDerivAt).comp_hasFDerivAt x (hasFDerivAt_apply i x)
  exact hA.fun_mul (aux_cubecutoff_fderiv2_B hφdiff x i)

theorem aux_cubecutoff_fderiv2_g_bound (hφmem : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (c1 c2 : ℝ)
    (hc1 : ∀ t, |deriv φ t| ≤ c1) (hc2 : ∀ t, |deriv (deriv φ) t| ≤ c2) (x : Fin d → ℝ)
    (i : Fin d) :
    ‖aux_cubecutoff_Dg d φ x i‖ ≤ c1 * (((d : ℝ) - 1) * c1) + c2 := by
  unfold aux_cubecutoff_Dg
  have hc1nn : 0 ≤ c1 := (abs_nonneg _).trans (hc1 0)
  have hc2nn : 0 ≤ c2 := (abs_nonneg _).trans (hc2 0)
  have hDA_bound := aux_cubecutoff_fderiv2_B_bound hφmem c1 hc1 x i
  rw [aux_cubecutoff_card_erase i] at hDA_bound
  set DB := ((∏ j ∈ Finset.univ.erase i, φ (x j)) •
      (deriv (deriv φ) (x i) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))) with hDB_def
  have hDB_bound : ‖DB‖ ≤ c2 := by
    rw [hDB_def, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |∏ j ∈ Finset.univ.erase i, φ (x j)| *
          (|deriv (deriv φ) (x i)| * ‖(ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)‖)
        ≤ 1 * (c2 * 1) := by
          gcongr <;>
            first
            | exact aux_cubecutoff_prod_abs hφmem x _
            | exact hc2 _
            | exact aux_cubecutoff_proj_norm i
      _ = c2 := by ring
  calc ‖deriv φ (x i) • aux_cubecutoff_DA d φ x i + DB‖
      ≤ ‖deriv φ (x i) • aux_cubecutoff_DA d φ x i‖ + ‖DB‖ := norm_add_le _ _
    _ = |deriv φ (x i)| * ‖aux_cubecutoff_DA d φ x i‖ + ‖DB‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ c1 * (((d : ℝ) - 1) * c1) + c2 := by
        gcongr <;> first | exact hc1 _ | exact hDA_bound | exact hDB_bound

theorem aux_cubecutoff_fderiv2 (hφdiff : Differentiable ℝ φ) (hφ'diff : Differentiable ℝ (deriv φ))
    (x : Fin d → ℝ) : HasFDerivAt (fun y : Fin d → ℝ => ∑ i : Fin d,
        (deriv φ (y i) * ∏ j ∈ Finset.univ.erase i, φ (y j)) •
          (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))
      (∑ i : Fin d, (aux_cubecutoff_Dg d φ x i).smulRight
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) x := by
  have hfam : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun y : Fin d → ℝ => (deriv φ (y i) * ∏ j ∈ Finset.univ.erase i, φ (y j)) •
          (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))
        ((aux_cubecutoff_Dg d φ x i).smulRight
          (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) x :=
    fun i _ => (aux_cubecutoff_fderiv2_g hφdiff hφ'diff x i).smul_const
      (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)
  exact HasFDerivAt.fun_sum hfam

theorem aux_cubecutoff_fderiv2_eq (hφdiff : Differentiable ℝ φ)
    (hφ'diff : Differentiable ℝ (deriv φ)) (x : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ (fun y : Fin d → ℝ => ∏ i, φ (y i))) x =
      ∑ i : Fin d, (aux_cubecutoff_Dg d φ x i).smulRight
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) := by
  have hf1eq : fderiv ℝ (fun y : Fin d → ℝ => ∏ i, φ (y i)) = fun y : Fin d → ℝ => ∑ i : Fin d,
      (deriv φ (y i) * ∏ j ∈ Finset.univ.erase i, φ (y j)) •
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) := by
    funext y
    rw [(aux_cubecutoff_fderiv1 hφdiff y).fderiv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [hf1eq]
  exact (aux_cubecutoff_fderiv2 hφdiff hφ'diff x).fderiv

theorem aux_cubecutoff_fderiv2_bound (hφmem : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (c1 c2 : ℝ)
    (hc1 : ∀ t, |deriv φ t| ≤ c1) (hc2 : ∀ t, |deriv (deriv φ) t| ≤ c2) (x : Fin d → ℝ) :
    ‖(∑ i : Fin d, (aux_cubecutoff_Dg d φ x i).smulRight
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))‖ ≤
      (d : ℝ) * (c1 * (((d : ℝ) - 1) * c1) + c2) := by
  have hc2nn : 0 ≤ c2 := (abs_nonneg _).trans (hc2 0)
  have step1 : ‖(∑ i : Fin d, (aux_cubecutoff_Dg d φ x i).smulRight
      (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))‖ ≤
      ∑ i : Fin d, ‖(aux_cubecutoff_Dg d φ x i).smulRight
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)‖ :=
    norm_sum_le (Finset.univ : Finset (Fin d))
      (fun i => (aux_cubecutoff_Dg d φ x i).smulRight
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))
  have step2 : ∀ i : Fin d, ‖(aux_cubecutoff_Dg d φ x i).smulRight
      (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)‖ ≤ c1 * (((d : ℝ) - 1) * c1) + c2 := by
    intro i
    have hb_nonneg : 0 ≤ c1 * (((d : ℝ) - 1) * c1) + c2 := by
      have hd1 : 1 ≤ d := lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
      have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      nlinarith [sq_nonneg c1]
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc ‖aux_cubecutoff_Dg d φ x i‖ *
          ‖(ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)‖
        ≤ (c1 * (((d : ℝ) - 1) * c1) + c2) * 1 :=
          mul_le_mul (aux_cubecutoff_fderiv2_g_bound hφmem c1 c2 hc1 hc2 x i)
            (aux_cubecutoff_proj_norm i) (norm_nonneg _) hb_nonneg
      _ = c1 * (((d : ℝ) - 1) * c1) + c2 := mul_one _
  have step3 : ∑ i : Fin d, ‖(aux_cubecutoff_Dg d φ x i).smulRight
      (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)‖ ≤
      ∑ _i : Fin d, (c1 * (((d : ℝ) - 1) * c1) + c2) := Finset.sum_le_sum fun i _ => step2 i
  have step4 : ∑ _i : Fin d, (c1 * (((d : ℝ) - 1) * c1) + c2) =
      (d : ℝ) * (c1 * (((d : ℝ) - 1) * c1) + c2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith [step1, step3, step4.le, step4.ge]

theorem aux_cubecutoff_fderiv2_total_bound (hφmem : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1)
    (hφdiff : Differentiable ℝ φ) (hφ'diff : Differentiable ℝ (deriv φ)) (c1 c2 : ℝ)
    (hc1 : ∀ t, |deriv φ t| ≤ c1) (hc2 : ∀ t, |deriv (deriv φ) t| ≤ c2) (x : Fin d → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (fun y : Fin d → ℝ => ∏ i, φ (y i))) x‖ ≤
      (d : ℝ) * (c1 * (((d : ℝ) - 1) * c1) + c2) := by
  rw [aux_cubecutoff_fderiv2_eq hφdiff hφ'diff x]
  exact aux_cubecutoff_fderiv2_bound hφmem c1 c2 hc1 hc2 x

/-- **(M4) Smooth cube cutoff with C² bounds.** -/
theorem aux_hcut_cube_cutoff (d : ℕ) : ∃ C0 : ℝ, 0 < C0 ∧ ∀ a1 a2 : ℝ, 0 < a1 → a1 < a2 →
    ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ a1 → f x = 1) ∧ (∀ x, a2 ≤ ‖x‖ → f x = 0) ∧
      (∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (a2 - a1)) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (a2 - a1) ^ 2) := by
  obtain ⟨K1, hK1nn, hK1⟩ := aux_cubecutoff_phi_deriv1_bound
  obtain ⟨K2, hK2nn, hK2⟩ := aux_cubecutoff_phi_deriv2_bound
  refine ⟨max 1 (max ((d : ℝ) * K1) ((d : ℝ) * (((d : ℝ) - 1) * K1 ^ 2) + (d : ℝ) * K2)),
    lt_of_lt_of_le one_pos (le_max_left _ _), fun a1 a2 ha1 hlt => ?_⟩
  set C0 : ℝ := max 1 (max ((d : ℝ) * K1) ((d : ℝ) * (((d : ℝ) - 1) * K1 ^ 2) + (d : ℝ) * K2))
    with hC0_def
  refine ⟨fun x => ∏ i, aux_cubecutoff_phi a1 a2 (x i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact aux_cubecutoff_prod_contDiff (aux_cubecutoff_phi_contDiff a1 a2)
  · exact fun x => ⟨Finset.prod_nonneg fun i _ => (aux_cubecutoff_phi_mem a1 a2 (x i)).1,
      Finset.prod_le_one (fun i _ => (aux_cubecutoff_phi_mem a1 a2 (x i)).1)
        (fun i _ => (aux_cubecutoff_phi_mem a1 a2 (x i)).2)⟩
  · exact fun x hx => aux_cubecutoff_prod_eq_one a1 (fun t ht => aux_cubecutoff_phi_one a1 a2 t ha1 hlt ht) x hx
  · exact fun x hx => aux_cubecutoff_prod_eq_zero a2 (lt_trans ha1 hlt)
      (fun t ht => aux_cubecutoff_phi_zero a1 a2 t ha1 hlt ht) x hx
  · have hg : 0 < a2 - a1 := sub_pos.mpr hlt
    have hφdiff : Differentiable ℝ (aux_cubecutoff_phi a1 a2) :=
      (aux_cubecutoff_phi_contDiff a1 a2).differentiable (by norm_num)
    have hc1 : ∀ t, |deriv (aux_cubecutoff_phi a1 a2) t| ≤ K1 / (a2 - a1) :=
      fun t => hK1 a1 a2 t ha1 hlt
    intro x
    have hb := aux_cubecutoff_fderiv1_bound (aux_cubecutoff_phi_mem a1 a2) hφdiff
      (K1 / (a2 - a1)) hc1 x
    have hCK1 : (d : ℝ) * K1 ≤ C0 := by
      rw [hC0_def]; exact (le_max_left _ _).trans (le_max_right _ _)
    calc ‖fderiv ℝ (fun x => ∏ i, aux_cubecutoff_phi a1 a2 (x i)) x‖
        ≤ (d : ℝ) * (K1 / (a2 - a1)) := hb
      _ = (d : ℝ) * K1 / (a2 - a1) := by ring
      _ ≤ C0 / (a2 - a1) := by gcongr
  · have hφtop : ContDiff ℝ (⊤ : ℕ∞) (aux_cubecutoff_phi a1 a2) := aux_cubecutoff_phi_contDiff a1 a2
    have hφ2 : ContDiff ℝ (2 : ℕ∞) (aux_cubecutoff_phi a1 a2) := hφtop.of_le (by exact_mod_cast le_top)
    have hφ2' : ContDiff ℝ ((1 : ℕ∞) + 1) (aux_cubecutoff_phi a1 a2) := by convert hφ2 using 2
    have hφdiff : Differentiable ℝ (aux_cubecutoff_phi a1 a2) := hφtop.differentiable (by norm_num)
    have hφ'1 : ContDiff ℝ (1 : ℕ∞) (deriv (aux_cubecutoff_phi a1 a2)) :=
      (contDiff_succ_iff_deriv.mp hφ2').2.2
    have hφ'diff : Differentiable ℝ (deriv (aux_cubecutoff_phi a1 a2)) :=
      hφ'1.differentiable (by norm_num)
    have hc1 : ∀ t, |deriv (aux_cubecutoff_phi a1 a2) t| ≤ K1 / (a2 - a1) :=
      fun t => hK1 a1 a2 t ha1 hlt
    have hc2 : ∀ t, |deriv (deriv (aux_cubecutoff_phi a1 a2)) t| ≤ K2 / (a2 - a1) ^ 2 :=
      fun t => hK2 a1 a2 t ha1 hlt
    have hg : 0 < a2 - a1 := sub_pos.mpr hlt
    have hCK2 : (d : ℝ) * (((d : ℝ) - 1) * K1 ^ 2) + (d : ℝ) * K2 ≤ C0 := by
      rw [hC0_def]; exact (le_max_right _ _).trans (le_max_right _ _)
    intro x
    have hb := aux_cubecutoff_fderiv2_total_bound (aux_cubecutoff_phi_mem a1 a2) hφdiff hφ'diff
      (K1 / (a2 - a1)) (K2 / (a2 - a1) ^ 2) hc1 hc2 x
    calc ‖fderiv ℝ (fderiv ℝ (fun x => ∏ i, aux_cubecutoff_phi a1 a2 (x i))) x‖
        ≤ (d : ℝ) * ((K1 / (a2 - a1)) * (((d : ℝ) - 1) * (K1 / (a2 - a1))) + K2 / (a2 - a1) ^ 2) := hb
      _ = ((d : ℝ) * (((d : ℝ) - 1) * K1 ^ 2) + (d : ℝ) * K2) / (a2 - a1) ^ 2 := by
          field_simp
      _ ≤ C0 / (a2 - a1) ^ 2 := by gcongr
end HCut
end
end

-- ===== module HCut.AssembleR1 =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hcut_vecDot_grad_le {f : SpatialCoordinates d → ℝ} (z : SpatialCoordinates d) {B1 : ℝ}
    (hB1 : ‖fderiv ℝ f z‖ ≤ B1) :
    Homogenization.vecDot (fun i => fderiv ℝ f z (Homogenization.basisVec i))
      (fun i => fderiv ℝ f z (Homogenization.basisVec i)) ≤ d * B1 ^ 2 := by
  unfold Homogenization.vecDot
  have hB0 : 0 ≤ B1 := (norm_nonneg _).trans hB1
  have h1 : ∀ i : Fin d, |fderiv ℝ f z (Homogenization.basisVec i)| ≤ B1 := by
    intro i
    have hb : ‖(Homogenization.basisVec i : SpatialCoordinates d)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      by_cases hij : j = i
      · subst hij; simp [Homogenization.basisVec]
      · simp [Homogenization.basisVec, hij]
    calc |fderiv ℝ f z (Homogenization.basisVec i)| = ‖fderiv ℝ f z (Homogenization.basisVec i)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ f z‖ * ‖(Homogenization.basisVec i : SpatialCoordinates d)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ B1 * 1 := mul_le_mul hB1 hb (norm_nonneg _) hB0
      _ = B1 := mul_one _
  calc ∑ i, fderiv ℝ f z (Homogenization.basisVec i) * fderiv ℝ f z (Homogenization.basisVec i)
      ≤ ∑ _i : Fin d, B1 ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1 i) 2
    _ = d * B1 ^ 2 := by simp

/-- **R1 energy**: the smooth cutoff's ball energy, from the upper mass bound. -/
lemma aux_hcut_R1_energy [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (R2 Rc : ℝ) (hRc : R2 + 1 ≤ Rc)
    (f : SpatialCoordinates d → ℝ) (B1 : ℝ) (hB1 : ∀ z, ‖fderiv ℝ f z‖ ≤ B1) (Kup : ℝ)
    (hmass : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      x ∈ Metric.ball (0 : SpatialCoordinates d) Rc →
      volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z)) (Metric.ball x r) ≤
        ENNReal.ofReal (Kup * r ^ ((d : ℝ) - 1 / 2)))
    (x : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ z in Metric.ball x r ∩ Metric.ball (0 : SpatialCoordinates d) R2,
        ENNReal.ofReal (cutoffCoefficient M H om N z * Homogenization.vecDot
          (fun i => fderiv ℝ f z (Homogenization.basisVec i))
          (fun i => fderiv ℝ f z (Homogenization.basisVec i))) ≤
      ENNReal.ofReal (d * B1 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * (Kup * r ^ ((d : ℝ) - 1 / 2))) := by
  by_cases hx : x ∈ Metric.ball (0 : SpatialCoordinates d) Rc
  · have hB0 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
    have hah : 0 < (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ :=
      inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
    have hpt : ∀ z, ENNReal.ofReal (cutoffCoefficient M H om N z * Homogenization.vecDot
          (fun i => fderiv ℝ f z (Homogenization.basisVec i))
          (fun i => fderiv ℝ f z (Homogenization.basisVec i))) ≤
        ENNReal.ofReal (d * B1 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) *
          ENNReal.ofReal (cutoffSpeedDensity M H om N z) := by
      intro z
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hv := aux_hcut_vecDot_grad_le z (hB1 z)
      have hρ : 0 ≤ cutoffSpeedDensity M H om N z := (Real.exp_pos _).le
      unfold cutoffCoefficient
      change (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * cutoffSpeedDensity M H om N z * _ ≤ _
      calc (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * cutoffSpeedDensity M H om N z *
            Homogenization.vecDot (fun i => fderiv ℝ f z (Homogenization.basisVec i))
              (fun i => fderiv ℝ f z (Homogenization.basisVec i))
          ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * cutoffSpeedDensity M H om N z * (d * B1 ^ 2) := by
            gcongr
        _ = d * B1 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * cutoffSpeedDensity M H om N z := by
            ring
    have hcont : Continuous (cutoffPotential H om N) := by
      unfold cutoffPotential
      exact (H om).continuous.add
        (continuous_finset_sum _ fun j _ => (om (-(Int.ofNat j))).continuous)
    have hmeas : Measurable fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z) := by
      refine ENNReal.measurable_ofReal.comp ?_
      unfold cutoffSpeedDensity
      exact (Real.continuous_exp.comp (hcont.sub continuous_const)).measurable
    calc ∫⁻ z in Metric.ball x r ∩ Metric.ball (0 : SpatialCoordinates d) R2,
          ENNReal.ofReal (cutoffCoefficient M H om N z * Homogenization.vecDot
            (fun i => fderiv ℝ f z (Homogenization.basisVec i))
            (fun i => fderiv ℝ f z (Homogenization.basisVec i)))
        ≤ ∫⁻ z in Metric.ball x r, ENNReal.ofReal (d * B1 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) *
            ENNReal.ofReal (cutoffSpeedDensity M H om N z) :=
          (lintegral_mono_set Set.inter_subset_left).trans (lintegral_mono fun z => hpt z)
      _ = ENNReal.ofReal (d * B1 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) *
            volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
              (Metric.ball x r) := by
          rw [lintegral_const_mul _ hmeas, withDensity_apply _ Metric.isOpen_ball.measurableSet]
      _ ≤ ENNReal.ofReal (d * B1 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) *
            ENNReal.ofReal (Kup * r ^ ((d : ℝ) - 1 / 2)) := by
          gcongr; exact hmass x r hr hr1 hx
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  · have hemp : Metric.ball x r ∩ Metric.ball (0 : SpatialCoordinates d) R2 = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Metric.mem_ball, Set.mem_empty_iff_false, iff_false, not_and]
      intro hz hz0
      apply hx
      rw [Metric.mem_ball, dist_zero_right]
      rw [dist_zero_right] at hz0
      have h1 : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
        calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      rw [← dist_eq_norm] at h1
      have h2 : dist x z < r := by rw [dist_comm]; exact hz
      linarith
    rw [hemp, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le _

lemma aux_hcut_R1_real {d : ℕ} {C0 g Kup Kcut ah0 ah rho0 : ℝ} (hC0 : 0 < C0) (hg : 0 < g)
    (hgr : g ≤ rho0 / 2) (hKup : 0 ≤ Kup) (hah0 : 0 < ah0) (hah : 0 < ah)
    (hahg : ah⁻¹ ≤ ah0⁻¹ * max 1 (5 / g))
    (hK : 20 * d * C0 ^ 2 * ah0⁻¹ * max 1 ((rho0 / 2) ^ 3) * Kup ≤ Kcut) :
    d * (C0 / (g / 2)) ^ 2 * ah⁻¹ * Kup ≤ Kcut * g ^ (-5 : ℝ) := by
  have hg5 : g ^ (-5 : ℝ) = (g ^ 5)⁻¹ := by
    rw [Real.rpow_neg hg.le]; norm_cast
  rw [hg5]
  have hgpos : 0 < g ^ 5 := by positivity
  have hkey : g ^ 3 * max 1 (5 / g) ≤ 5 * max 1 ((rho0 / 2) ^ 3) := by
    have hm1 : 1 ≤ max 1 ((rho0 / 2) ^ 3) := le_max_left _ _
    have hg3 : g ^ 3 ≤ max 1 ((rho0 / 2) ^ 3) :=
      le_max_of_le_right (pow_le_pow_left₀ hg.le hgr 3)
    have hg2 : g ^ 2 ≤ max 1 ((rho0 / 2) ^ 3) := by
      rcases le_or_gt g 1 with hg1 | hg1
      · have : g ^ 2 ≤ 1 := pow_le_one₀ hg.le hg1
        linarith
      · have : g ^ 2 ≤ g ^ 3 := pow_le_pow_right₀ hg1.le (by norm_num)
        linarith
    rcases le_total 1 (5 / g) with h5 | h5
    · rw [max_eq_right h5]
      have : g ^ 3 * (5 / g) = 5 * g ^ 2 := by field_simp
      rw [this]; linarith
    · rw [max_eq_left h5]; linarith
  rw [le_mul_inv_iff₀ hgpos]
  calc d * (C0 / (g / 2)) ^ 2 * ah⁻¹ * Kup * g ^ 5
      ≤ d * (C0 / (g / 2)) ^ 2 * (ah0⁻¹ * max 1 (5 / g)) * Kup * g ^ 5 := by gcongr
    _ = 4 * d * C0 ^ 2 * ah0⁻¹ * (g ^ 3 * max 1 (5 / g)) * Kup := by field_simp; ring
    _ ≤ 4 * d * C0 ^ 2 * ah0⁻¹ * (5 * max 1 ((rho0 / 2) ^ 3)) * Kup := by gcongr
    _ = 20 * d * C0 ^ 2 * ah0⁻¹ * max 1 ((rho0 / 2) ^ 3) * Kup := by ring
    _ ≤ Kcut := hK

/-- **R1 pair**: a smooth cutoff between `ball 0 R1` and `ball 0 R2` meeting the clause bound. -/
lemma aux_hcut_pair_R1 [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (C0 : ℝ) (hC0 : 0 < C0)
    (hcube : ∀ a1 a2 : ℝ, 0 < a1 → a1 < a2 →
      ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
        (∀ x, ‖x‖ ≤ a1 → f x = 1) ∧ (∀ x, a2 ≤ ‖x‖ → f x = 0) ∧
        (∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (a2 - a1)) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (a2 - a1) ^ 2))
    (rho0 R1 R2 Kup Kcut : ℝ) (hR1 : 0 < R1) (hR12 : R1 < R2) (hR2 : R2 ≤ rho0 / 2) (hKup : 0 ≤ Kup)
    (hahg : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ ≤
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * max 1 (5 / (R2 - R1)))
    (hmass : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2 + 2) →
      volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z)) (Metric.ball x r) ≤
        ENNReal.ofReal (Kup * r ^ ((d : ℝ) - 1 / 2)))
    (hK : 20 * d * C0 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * max 1 ((rho0 / 2) ^ 3) * Kup ≤ Kcut) :
    ∃ chi : Homogenization.H10Function (Metric.ball (0 : SpatialCoordinates d) R2),
      (∀ x, 0 ≤ chi.toH1Function.toFun x ∧ chi.toH1Function.toFun x ≤ 1) ∧
      (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) R1, chi.toH1Function.toFun x = 1) ∧
      tsupport chi.toH1Function.toFun ⊆ Metric.ball (0 : SpatialCoordinates d) R2 ∧
      ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
        ∫⁻ z in Metric.ball x r ∩ Metric.ball (0 : SpatialCoordinates d) R2,
          ENNReal.ofReal (cutoffCoefficient M H om N z *
            Homogenization.vecDot (chi.toH1Function.grad z) (chi.toH1Function.grad z)) ≤
          ENNReal.ofReal (Kcut * (R2 - R1) ^ (-5 : ℝ) * r ^ ((d : ℝ) - 1 / 2)) := by
  set g := R2 - R1 with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  obtain ⟨f, hf, hf01, hf1, hf0, hD1, -⟩ := hcube R1 (R2 - g / 2) hR1 (by linarith)
  have hfsub : tsupport f ⊆ Metric.ball (0 : SpatialCoordinates d) R2 :=
    (HCut.aux_hcut_f_tsupport (R2 := R2 - g / 2 + 2 * (g / 8)) (h := g / 8) (by positivity)
      (fun x hx => hf0 x (by linarith))).trans (Metric.closedBall_subset_ball (by linarith))
  refine ⟨HCut.aux_hcut_h10OfSmooth Metric.isOpen_ball hf (HCut.aux_hcut_f_compact (R2 := R2 - g / 2) (h := 0)
      (fun x hx => hf0 x (by linarith))) hfsub, ?_, ?_, ?_, ?_⟩
  · exact hf01
  · intro x hx
    exact hf1 x (by rw [Metric.mem_ball, dist_zero_right] at hx; exact hx.le)
  · exact hfsub
  · intro x r hr hr1
    have hB : ∀ z, ‖fderiv ℝ f z‖ ≤ C0 / (g / 2) := fun z => by
      have := hD1 z; rwa [show R2 - g / 2 - R1 = g / 2 by rw [hg]; ring] at this
    have hE := aux_hcut_R1_energy M H om N R2 (rho0 / 2 + 2) (by linarith) f (C0 / (g / 2)) hB Kup
      hmass x r hr hr1
    refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
    have hrt : 0 ≤ r ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg hr.le _
    have hreal := aux_hcut_R1_real (d := d) hC0 hg0 (by linarith) hKup
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N) hahg hK
    calc d * (C0 / (g / 2)) ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * (Kup * r ^ ((d : ℝ) - 1 / 2))
        = (d * (C0 / (g / 2)) ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * Kup) *
            r ^ ((d : ℝ) - 1 / 2) := by ring
      _ ≤ (Kcut * g ^ (-5 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by gcongr
      _ = Kcut * g ^ (-5 : ℝ) * r ^ ((d : ℝ) - 1 / 2) := by ring

end Paper
end
end

-- ===== module HCut.AssembleClause =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- Mesh level for a gap `0 < g ≤ ρ0/2`: `n ≥ 1`, `5·3^{-n} ≤ g`, `3^n ≤ (3ρ0/2+15)/g`, and whenever
`N < n` the cutoff scale satisfies `3^N ≤ max 1 (5/g)` (the R1 regime). -/
lemma aux_hcut_mesh_level {g rho0 : ℝ} (hg : 0 < g) (hgr : g ≤ rho0 / 2) :
    ∃ n : ℕ, 1 ≤ n ∧ 5 * ((3 : ℝ) ^ n)⁻¹ ≤ g ∧ ((3 : ℝ) ^ n) ≤ (3 * rho0 / 2 + 15) / g ∧
      ∀ N : ℕ, N < n → (3 : ℝ) ^ N ≤ max 1 (5 / g) := by
  classical
  have hex : ∃ n : ℕ, 5 / g ≤ (3 : ℝ) ^ n :=
    (pow_unbounded_of_one_lt (5 / g) (by norm_num : (1 : ℝ) < 3)).imp fun n hn => hn.le
  set m := Nat.find hex with hm
  have hmspec : 5 / g ≤ (3 : ℝ) ^ m := Nat.find_spec hex
  have hmin : ∀ k < m, (3 : ℝ) ^ k < 5 / g := fun k hk => not_le.1 (Nat.find_min hex hk)
  refine ⟨max 1 m, le_max_left _ _, ?_, ?_, ?_⟩
  · have h1 : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ (max 1 m) := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    have h2 : 5 / g ≤ (3 : ℝ) ^ (max 1 m) := hmspec.trans h1
    rw [div_le_iff₀ hg] at h2
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  · rw [le_div_iff₀ hg]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, max_eq_left (by norm_num : (0 : ℕ) ≤ 1), pow_one]
      linarith
    · rw [max_eq_right hpos]
      have hprev := hmin (m - 1) (by omega)
      have hpow : (3 : ℝ) ^ m = 3 * (3 : ℝ) ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hpow]
      rw [lt_div_iff₀ hg] at hprev
      nlinarith
  · intro N hN
    by_cases hNm : N < m
    · exact (hmin N hNm).le.trans (le_max_right _ _)
    · have hm0 : m = 0 := by
        have : max 1 m = 1 ∨ max 1 m = m := by
          rcases le_total 1 m with h | h
          · right; exact max_eq_right h
          · left; exact max_eq_left h
        rcases this with h | h <;> omega
      have hN0 : N = 0 := by omega
      rw [hN0, pow_zero]
      exact le_max_left _ _

/-- **R2 branch of the clause** (fixed environment). -/
lemma aux_hcut_clause_R2 [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 1 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (C0 : ℝ) (hC0 : 0 < C0)
    (hcube : ∀ a1 a2 : ℝ, 0 < a1 → a1 < a2 →
      ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
        (∀ x, ‖x‖ ≤ a1 → f x = 1) ∧ (∀ x, a2 ≤ ‖x‖ → f x = 0) ∧
        (∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (a2 - a1)) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (a2 - a1) ^ 2))
    (rho0 R1 R2 Kcut Mn : ℝ) (n : ℕ) (hR1 : 0 < R1) (hR12 : R1 < R2) (hR2 : R2 ≤ rho0 / 2)
    (hn1 : 1 ≤ n) (hn5 : 5 * ((3 : ℝ) ^ n)⁻¹ ≤ R2 - R1)
    (hn3 : ((3 : ℝ) ^ n) ≤ (3 * rho0 / 2 + 15) / (R2 - R1)) (hMn : 0 ≤ Mn)
    (hcell : ∀ k : Fin d → ℤ, HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2) →
      ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ 2 f → ∀ B1 B2 : ℝ,
        (∀ x, ‖fderiv ℝ f x‖ ≤ B1) → (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B2) →
      ∀ (hr : 0 < ((3 : ℝ) ^ n)⁻¹)
        (b u : weakSobolevGraph (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr)),
        ((b : SobolevData (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr)).1 :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr :
              Set (SpatialCoordinates d))]
          (fun w => f w - f (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k)) →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) hr)
          (fun _ => (0 : ℝ)) b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr →
          0 < rad → rad ≤ 1 →
          localGradientEnergy (cutoffPositiveCoefficient M H om N (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) hr)
              (s := Metric.ball x rad ∩
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr))) ≤
            Mn * (((3 : ℝ) ^ n)⁻¹ * B1 / 2 + ((3 : ℝ) ^ n)⁻¹ * B1 + (((3 : ℝ) ^ n)⁻¹) ^ 2 * B2) ^ 2 *
              (((3 : ℝ) ^ n)⁻¹) ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * rad ^ ((d : ℝ) - 1 / 2))
    (hK2 : 8 ^ d * 25 * C0 ^ 2 * (3 * rho0 / 2 + 15) * max 1 ((rho0 / 2) ^ 2) *
      (((3 : ℝ) ^ n)⁻¹ * Mn) ≤ Kcut) :
    ∃ chi : Homogenization.H10Function (Metric.ball (0 : SpatialCoordinates d) R2),
      (∀ x, 0 ≤ chi.toH1Function.toFun x ∧ chi.toH1Function.toFun x ≤ 1) ∧
      (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) R1, chi.toH1Function.toFun x = 1) ∧
      tsupport chi.toH1Function.toFun ⊆ Metric.ball (0 : SpatialCoordinates d) R2 ∧
      ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
        ∫⁻ z in Metric.ball x r ∩ Metric.ball (0 : SpatialCoordinates d) R2,
          ENNReal.ofReal (cutoffCoefficient M H om N z *
            Homogenization.vecDot (chi.toH1Function.grad z) (chi.toH1Function.grad z)) ≤
          ENNReal.ofReal (Kcut * (R2 - R1) ^ (-5 : ℝ) * r ^ ((d : ℝ) - 1 / 2)) := by
  set h : ℝ := ((3 : ℝ) ^ n)⁻¹ with hhdef
  have hh : 0 < h := by positivity
  have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ n := by
    calc (3 : ℝ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn1
  have hh1 : h ≤ 1 / 2 := by
    rw [hhdef]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set g := R2 - R1 with hg
  have hg0 : 0 < g := by linarith
  obtain ⟨f, hf, hf01, hf1, hf0, hD1, hD2⟩ := hcube (R1 + h) (R2 - 2 * h) (by linarith) (by linarith)
  set B1 := C0 / (R2 - 2 * h - (R1 + h)) with hB1
  set B2 := C0 / (R2 - 2 * h - (R1 + h)) ^ 2 with hB2
  have hgap : R2 - 2 * h - (R1 + h) = g - 3 * h := by rw [hg]; ring
  have hcoef : ∀ (y : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ᵐ x ∂(volume.restrict (centeredCube y r hr : Set (SpatialCoordinates d))),
        ((cutoffPositiveCoefficient M H om N y hr).val : SpatialCoordinates d → ℝ) x =
          cutoffCoefficient M H om N x :=
    fun y r hr => aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M H om N y hr
  have hAc : Continuous (cutoffCoefficient M H om N) := by
    have hcont : Continuous (cutoffPotential H om N) := by
      unfold cutoffPotential
      exact (H om).continuous.add
        (continuous_finset_sum _ fun j _ => (om (-(Int.ofNat j))).continuous)
    unfold cutoffCoefficient
    exact continuous_const.mul (Real.continuous_exp.comp (hcont.sub continuous_const))
  have hApos : ∀ x, 0 < cutoffCoefficient M H om N x := fun x =>
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  have hG0 : 0 ≤ Mn * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 * h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) := by
    have := Real.rpow_nonneg hh.le ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2))
    positivity
  obtain ⟨chi, h01, hone, hsupp, henergy⟩ := aux_hcut_pair_R2 hd (cutoffCoefficient M H om N) hAc hApos
    (fun y r hr => cutoffPositiveCoefficient M H om N y hr) hcoef R1 R2 h ((d : ℝ) - 1 / 2) hh hh1 rfl
    f hf hf01 hf1 hf0 _ hG0 (fun k hk b u htrace hsolve x rad hx hrad0 hrad1 => by
      have hcc : HCut.aux_hcut_cc h k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2) := by
        have := HCut.aux_hcut_trans_cell_subset hh hk (Metric.mem_closedBall_self (by positivity))
        exact Metric.ball_subset_closedBall (Metric.ball_subset_ball hR2 this)
      have := hcell k hcc f (hf.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) B1 B2 hD1 hD2 hh
        b u htrace hsolve x rad hx hrad0 hrad1
      exact this)
  refine ⟨chi, h01, hone, hsupp, fun x r hr hr1 => (henergy x r hr hr1).trans ?_⟩
  refine ENNReal.ofReal_le_ofReal ?_
  have hreal := aux_hcut_R2_real (d := d) (C0 := C0) (g := g) (h := h) (B1 := B1) (B2 := B2) (Mc := Mn)
    (Kcut := Kcut) (Crho := 3 * rho0 / 2 + 15) (rho0 := rho0) hC0 hg0 hh (by rw [hg]; linarith)
    (by rw [hg]; linarith) (by rw [hB1, hgap]) (by rw [hB2, hgap]) hMn
    (by rw [hhdef, inv_inv]; exact hn3) (by linarith) hK2
  have hrt : 0 ≤ r ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg hr.le _
  calc 8 ^ d * (Mn * (h * B1 / 2 + h * B1 + h ^ 2 * B2) ^ 2 * h ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2))) *
        h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2)
      ≤ Kcut * g ^ (-5 : ℝ) * r ^ ((d : ℝ) - 1 / 2) := by gcongr
    _ = Kcut * (R2 - R1) ^ (-5 : ℝ) * r ^ ((d : ℝ) - 1 / 2) := by rw [hg]

/-- **The cutoff clause for one environment** (both regimes). -/
lemma aux_hcut_clause [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 1 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (C0 : ℝ) (hC0 : 0 < C0)
    (hcube : ∀ a1 a2 : ℝ, 0 < a1 → a1 < a2 →
      ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
        (∀ x, ‖x‖ ≤ a1 → f x = 1) ∧ (∀ x, a2 ≤ ‖x‖ → f x = 0) ∧
        (∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (a2 - a1)) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (a2 - a1) ^ 2))
    (rho0 Kup Kcut : ℝ) (Mn : ℕ → ℝ) (hrho : 1 ≤ rho0) (hKup : 0 ≤ Kup)
    (hmass : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2 + 2) →
      volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z)) (Metric.ball x r) ≤
        ENNReal.ofReal (Kup * r ^ ((d : ℝ) - 1 / 2)))
    (hahom : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ ≤
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * (3 : ℝ) ^ N)
    (hMn : ∀ n, 0 ≤ Mn n)
    (hcell : ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ k : Fin d → ℤ,
      HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2) →
      ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ 2 f → ∀ B1 B2 : ℝ,
        (∀ x, ‖fderiv ℝ f x‖ ≤ B1) → (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B2) →
      ∀ (hr : 0 < ((3 : ℝ) ^ n)⁻¹)
        (b u : weakSobolevGraph (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr)),
        ((b : SobolevData (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr)).1 :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr :
              Set (SpatialCoordinates d))]
          (fun w => f w - f (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k)) →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) hr)
          (fun _ => (0 : ℝ)) b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr →
          0 < rad → rad ≤ 1 →
          localGradientEnergy (cutoffPositiveCoefficient M H om N (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) hr)
              (s := Metric.ball x rad ∩
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData
                (centeredCube (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) ((3 : ℝ) ^ n)⁻¹ hr))) ≤
            Mn n * (((3 : ℝ) ^ n)⁻¹ * B1 / 2 + ((3 : ℝ) ^ n)⁻¹ * B1 + (((3 : ℝ) ^ n)⁻¹) ^ 2 * B2) ^ 2 *
              (((3 : ℝ) ^ n)⁻¹) ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) * rad ^ ((d : ℝ) - 1 / 2))
    (hK1 : 20 * d * C0 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * max 1 ((rho0 / 2) ^ 3) * Kup ≤ Kcut)
    (hK2 : ∀ n : ℕ, 1 ≤ n → n ≤ N → 8 ^ d * 25 * C0 ^ 2 * (3 * rho0 / 2 + 15) *
      max 1 ((rho0 / 2) ^ 2) * (((3 : ℝ) ^ n)⁻¹ * Mn n) ≤ Kcut) :
    ∀ q1 q2 : ℚ, 0 < q1 → q1 < q2 → q2 ≤ 1 →
      ∃ chi : Homogenization.H10Function
          (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2), chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2) ∧
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          ∫⁻ z in Metric.ball x r ∩
              Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
            ENNReal.ofReal ((cutoffCoefficient M H om N z) *
              Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
            ENNReal.ofReal
              (Kcut * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-5 : ℝ) * r ^ ((d : ℝ) - 1 / 2)) := by
  intro q1 q2 hq1 hq12 hq2
  have hq1r : (0 : ℝ) < q1 := by exact_mod_cast hq1
  have hq12r : (q1 : ℝ) < q2 := by exact_mod_cast hq12
  have hq2r : (q2 : ℝ) ≤ 1 := by exact_mod_cast hq2
  have hrho0 : 0 < rho0 := by linarith
  have hR1 : 0 < rho0 * (q1 : ℝ) / 2 := by positivity
  have hR12 : rho0 * (q1 : ℝ) / 2 < rho0 * (q2 : ℝ) / 2 := by
    have := mul_lt_mul_of_pos_left hq12r hrho0; linarith
  have hR2 : rho0 * (q2 : ℝ) / 2 ≤ rho0 / 2 := by
    have := mul_le_mul_of_nonneg_left hq2r hrho0.le; linarith
  have hgeq : rho0 * (q2 : ℝ) / 2 - rho0 * (q1 : ℝ) / 2 = rho0 * ((q2 : ℝ) - q1) / 2 := by ring
  have hg0 : 0 < rho0 * (q2 : ℝ) / 2 - rho0 * (q1 : ℝ) / 2 := by linarith
  have hgr : rho0 * (q2 : ℝ) / 2 - rho0 * (q1 : ℝ) / 2 ≤ rho0 / 2 := by
    have : 0 ≤ rho0 * (q1 : ℝ) / 2 := hR1.le; linarith
  obtain ⟨n, hn1, hn5, hn3, hnR1⟩ := aux_hcut_mesh_level hg0 hgr
  rw [← hgeq]
  by_cases hnN : n ≤ N
  · exact aux_hcut_clause_R2 hd M H om N C0 hC0 hcube rho0 _ _ Kcut (Mn n) n hR1 hR12 hR2 hn1 hn5 hn3
      (hMn n) (hcell n hn1 hnN) (hK2 n hn1 hnN)
  · have h3N := hnR1 N (not_le.1 hnN)
    have hahg : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ *
        max 1 (5 / (rho0 * (q2 : ℝ) / 2 - rho0 * (q1 : ℝ) / 2)) :=
      hahom.trans (mul_le_mul_of_nonneg_left h3N
        (inv_nonneg.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0).le))
    exact aux_hcut_pair_R1 M H om N C0 hC0 hcube rho0 _ _ Kup Kcut hR1 hR12 hR2 hKup hahg hmass hK1

end Paper
end
end

-- ===== module HCut.StageB =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The level-`n` cells centred in the closed reference ball of radius `rho0/2`. -/
def aux_hcut_S (rho0 : ℝ) (n : ℕ) : Finset (Fin d → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-(⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ)) (⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ)).filter
    fun k => HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2)

lemma aux_hcut_mem_S {rho0 : ℝ} (hrho : 1 ≤ rho0) {n : ℕ} {k : Fin d → ℤ}
    (hk : HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2)) :
    k ∈ aux_hcut_S rho0 n := by
  classical
  unfold aux_hcut_S
  rw [Finset.mem_filter]
  refine ⟨Fintype.mem_piFinset.2 fun i => ?_, hk⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hk
  have hci : |HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k i| ≤ rho0 / 2 := by
    have := norm_le_pi_norm (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) i
    rw [Real.norm_eq_abs] at this; linarith
  simp only [HCut.aux_hcut_cc] at hci
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.2 h3)] at hci
  have h2 : |(k i : ℝ) + 1 / 2| ≤ rho0 / 2 * (3 : ℝ) ^ n := by
    rw [inv_mul_le_iff₀ h3] at hci
    calc |(k i : ℝ) + 1 / 2| ≤ (3 : ℝ) ^ n * (rho0 / 2) := hci
      _ = rho0 / 2 * (3 : ℝ) ^ n := mul_comm _ _
  have h1 : |(k i : ℝ)| ≤ rho0 * (3 : ℝ) ^ n := by
    have e : ((k i : ℝ) + 1 / 2) - 1 / 2 = (k i : ℝ) := by ring
    have h4 := abs_sub ((k i : ℝ) + 1 / 2) (1 / 2)
    rw [e] at h4
    have h5 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    have h6 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have h7 : 1 ≤ rho0 * (3 : ℝ) ^ n := one_le_mul_of_one_le_of_one_le hrho h6
    linarith
  have hc : rho0 * (3 : ℝ) ^ n ≤ (⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℝ) := Nat.le_ceil _
  rw [abs_le] at h1
  rw [Finset.mem_Icc]
  constructor
  · have : -((⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ) : ℝ) ≤ (k i : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (k i : ℝ) ≤ ((⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

lemma aux_hcut_card_S {rho0 : ℝ} (hrho : 0 ≤ rho0) (n : ℕ) :
    ((aux_hcut_S (d := d) rho0 n).card : ℝ) ≤ ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d := by
  classical
  have hsub : aux_hcut_S (d := d) rho0 n ⊆ Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-(⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ)) (⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ) := by
    unfold aux_hcut_S; exact Finset.filter_subset _ _
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc] at hcard
  have hL : ((⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ) + 1 - -(⌈rho0 * (3 : ℝ) ^ n⌉₊ : ℤ)).toNat =
      2 * ⌈rho0 * (3 : ℝ) ^ n⌉₊ + 1 := by omega
  rw [hL] at hcard
  have h1 : ((2 * ⌈rho0 * (3 : ℝ) ^ n⌉₊ + 1 : ℕ) : ℝ) ≤ (2 * rho0 + 3) * (3 : ℝ) ^ n := by
    have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ rho0 * (3 : ℝ) ^ n)
    have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    push_cast
    nlinarith
  calc ((aux_hcut_S (d := d) rho0 n).card : ℝ) ≤ (((2 * ⌈rho0 * (3 : ℝ) ^ n⌉₊ + 1) ^ d : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ((2 * ⌈rho0 * (3 : ℝ) ^ n⌉₊ + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
    _ ≤ ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d := pow_le_pow_left₀ (by positivity) h1 d

end Paper
end
end

-- ===== module HCut.Moments =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric TopologicalSpace
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]




/-- Each individual layer evaluated at the origin has an exponential moment bound
uniform in the layer index, at rate `q^2 * delta^2 / 4` (independent of the layer and of
the sign of `q`), via assumption (g2) (`M.G2.regularity_expectation`). -/
theorem aux_tight_static_layer_abs_exp_moment
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (q : ℝ) (hq : 0 ≤ q) :
    ∫ om, Real.exp (q * |om m 0|) ∂(chaosSampleLaw M).toMeasure ≤
      2 * Real.exp (q ^ 2 * M.delta ^ 2 / 4) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  set E : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable with hEdef
  set Z : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * max (E g) 0) ^ (2 : ℝ)) with hZdef
  have hZint : Integrable Z (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    simpa [hZdef, hEdef, SubdiffusiveProcess.OGammaLE] using M.G2.regularity_expectation.1
  have hZbound : ∫ g, Z g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤ 2 := by
    simpa [hZdef, hEdef, SubdiffusiveProcess.OGammaLE] using M.G2.regularity_expectation.2
  have h0 : (0 : Homogenization.Vec d) ∈ Metric.closedBall
      (Homogenization.cubeCenter (Homogenization.originCube d 0))
      (Homogenization.cubeRadius (Homogenization.originCube d 0)) := by
    have hc0 : Homogenization.cubeCenter (Homogenization.originCube d 0) = 0 := by
      funext i
      simp [Homogenization.cubeCenter, Homogenization.originCube]
    rw [hc0]
    exact Metric.mem_closedBall_self (Homogenization.cubeRadius_pos _).le
  have hmeasEv : Measurable fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => g 0 := by
    have hforget : Continuous fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        (g.1.1 : C(SpatialCoordinates d, ℝ)) := continuous_subtype_val.fst
    exact ((continuous_eval_const (0 : SpatialCoordinates d)).comp hforget).measurable
  have hmeasF0 : Measurable fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      Real.exp (q * |g 0|) := (measurable_const.mul (continuous_abs.measurable.comp hmeasEv)).exp
  have hdom : ∀ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      Real.exp (q * |g 0|) ≤ Real.exp ((q * M.delta) ^ 2 / 4) * Z g := by
    intro g
    have hE0 : 0 ≤ E g := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg g
    have hg0 : |g 0| ≤ E g :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.abs_apply_le_g2Observable_of_mem_closedBall g h0
    have hZg : Z g = Real.exp ((M.delta⁻¹ * E g) ^ (2 : ℕ)) := by
      simp only [hZdef, max_eq_left hE0]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hZg, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hexpand : (q * M.delta) ^ 2 / 4 + (M.delta⁻¹ * E g) ^ (2 : ℕ) - q * E g
        = (E g - q * M.delta ^ 2 / 2) ^ 2 / M.delta ^ 2 := by
      field_simp
      ring
    have h2 : 0 ≤ (q * M.delta) ^ 2 / 4 + (M.delta⁻¹ * E g) ^ (2 : ℕ) - q * E g := by
      rw [hexpand]; positivity
    have h3 : q * |g 0| ≤ q * E g := mul_le_mul_of_nonneg_left hg0 hq
    linarith
  have hintF0 : Integrable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      Real.exp (q * |g 0|)) (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
    (hZint.const_mul (Real.exp ((q * M.delta) ^ 2 / 4))).mono'
      hmeasF0.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]; exact hdom g)
  have hboundZero0 :
      ∫ g, Real.exp (q * |g 0|) ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤
      Real.exp ((q * M.delta) ^ 2 / 4) * 2 := by
    calc ∫ g, Real.exp (q * |g 0|) ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤
        ∫ g, Real.exp ((q * M.delta) ^ 2 / 4) * Z g
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
          integral_mono hintF0 (hZint.const_mul _) hdom
      _ = Real.exp ((q * M.delta) ^ 2 / 4) *
            ∫ g, Z g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := integral_const_mul _ _
      _ ≤ Real.exp ((q * M.delta) ^ 2 / 4) * 2 :=
          mul_le_mul_of_nonneg_left hZbound (Real.exp_pos _).le
  set F : C(SpatialCoordinates d, ℝ) → ℝ := fun f => Real.exp (q * |f 0|) with hF
  have hFm : Measurable F :=
    (measurable_const.mul (continuous_abs.measurable.comp
      (continuous_eval_const (0 : SpatialCoordinates d)).measurable)).exp
  set laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun n =>
    (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ)) with hlaws
  have hev := measurePreserving_eval_infinitePi laws m
  have hboundLaw : ∫ f, F f ∂(laws m) ≤ Real.exp ((q * M.delta) ^ 2 / 4) * 2 := by
    have hptwise : ∀ f, F (layerScaling d m f) = F f := by
      intro f
      simp [hF, layerScaling]
    simp only [hlaws, scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
    rw [integral_map (layerScaling d m).continuous.measurable.aemeasurable
        hFm.aestronglyMeasurable]
    simp only [hptwise]
    simp only [chaosRootFieldLaw, ProbabilityMeasure.toMeasure_map]
    rw [integral_map (ContinuousMap.continuous _).measurable.aemeasurable
      hFm.aestronglyMeasurable]
    exact hboundZero0
  have hboundInfinitePi : ∫ om, F (om m) ∂(Measure.infinitePi laws) ≤
      Real.exp ((q * M.delta) ^ 2 / 4) * 2 := by
    have heq : ∫ om, F (om m) ∂(Measure.infinitePi laws) = ∫ f, F f ∂(laws m) := by
      rw [← hev.map_eq]
      exact (integral_map hev.measurable.aemeasurable hFm.aestronglyMeasurable).symm
    rw [heq]
    exact hboundLaw
  rw [aux_prop_growth_large_root_chaosSampleLaw_eq]
  have : (fun om : BilateralField d => Real.exp (q * |om m 0|)) = fun om => F (om m) := rfl
  rw [this]
  calc ∫ om, F (om m) ∂(Measure.infinitePi laws) ≤
      Real.exp ((q * M.delta) ^ 2 / 4) * 2 := hboundInfinitePi
    _ = 2 * Real.exp (q ^ 2 * M.delta ^ 2 / 4) := by
      rw [mul_comm]
      congr 2
      ring

/-- Each individual layer evaluated at the origin has an exponential moment bound
uniform in the layer index and in the sign of `q`, at rate `q^2 * delta^2 / 4`. -/
theorem aux_tight_static_layer_exp_moment
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (q : ℝ) :
    Integrable (fun om : BilateralField d => Real.exp (q * om m 0))
      (chaosSampleLaw M).toMeasure ∧
    ∫ om, Real.exp (q * om m 0) ∂(chaosSampleLaw M).toMeasure ≤
      2 * Real.exp (q ^ 2 * M.delta ^ 2 / 4) := by
  have habs := aux_prop_growth_large_root_integrable_exp_mul_abs_layer M m |q| (abs_nonneg q)
  have hle : ∀ om : BilateralField d, Real.exp (q * om m 0) ≤ Real.exp (|q| * |om m 0|) := by
    intro om
    apply Real.exp_le_exp.2
    calc q * om m 0 ≤ |q * om m 0| := le_abs_self _
      _ = |q| * |om m 0| := abs_mul _ _
  have hmeas : Measurable (fun om : BilateralField d => Real.exp (q * om m 0)) :=
    (measurable_const.mul
      ((continuous_eval_const (0 : SpatialCoordinates d)).measurable.comp
        (measurable_pi_apply m))).exp
  have hint : Integrable (fun om : BilateralField d => Real.exp (q * om m 0))
      (chaosSampleLaw M).toMeasure :=
    habs.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun om => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact hle om)
  refine ⟨hint, ?_⟩
  have habsbound := aux_tight_static_layer_abs_exp_moment M m |q| (abs_nonneg q)
  calc ∫ om, Real.exp (q * om m 0) ∂(chaosSampleLaw M).toMeasure ≤
      ∫ om, Real.exp (|q| * |om m 0|) ∂(chaosSampleLaw M).toMeasure :=
        integral_mono hint habs hle
    _ ≤ 2 * Real.exp (|q| ^ 2 * M.delta ^ 2 / 4) := habsbound
    _ = 2 * Real.exp (q ^ 2 * M.delta ^ 2 / 4) := by rw [sq_abs]

/-- All layers, evaluated at the origin, are jointly independent (they are disjoint
coordinates of the underlying infinite product law). -/
theorem aux_tight_static_layer_iIndepFun (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    iIndepFun (fun k : ℤ => fun om : BilateralField d => om k 0) (chaosSampleLaw M).toMeasure := by
  rw [aux_prop_growth_large_root_chaosSampleLaw_eq]
  have hfull : iIndepFun (fun k : ℤ => fun om : ℤ → C(SpatialCoordinates d, ℝ) => om k)
      (Measure.infinitePi (fun n : ℤ =>
        (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ)))) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hG : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f 0) :=
    (continuous_eval_const (0 : SpatialCoordinates d)).measurable
  exact hfull.comp (fun _ => fun f : C(SpatialCoordinates d, ℝ) => f 0) (fun _ => hG)

/-- The layer `n + 1` value is independent of the sum of the first `n` layer values
(disjoint index sets under the product law). -/
theorem aux_tight_static_irAnchor_indepFun (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) :
    IndepFun (fun om : BilateralField d => om ((n : ℤ) + 1) 0)
      (fun om : BilateralField d => aux_prop_growth_large_root_irAnchor n om)
      (chaosSampleLaw M).toMeasure := by
  have hindep := aux_tight_static_layer_iIndepFun M
  have hmeas : ∀ k : ℤ, Measurable (fun om : BilateralField d => om k 0) := by
    intro k
    exact (continuous_eval_const (0 : SpatialCoordinates d)).measurable.comp
      (measurable_pi_apply k)
  set s : Finset ℤ := (Finset.range n).image (fun k : ℕ => (k : ℤ) + 1) with hs
  have hnotmem : ((n : ℤ) + 1) ∉ s := by
    simp only [hs, Finset.mem_image, Finset.mem_range]
    rintro ⟨k, hk, hk2⟩
    have hk2' : (k : ℤ) + 1 = (n : ℤ) + 1 := hk2
    omega
  have hsum := hindep.indepFun_finset_sum_of_notMem hmeas hnotmem
  have hfun : (∑ j ∈ s, fun om : BilateralField d => om j 0) =
      fun om : BilateralField d => aux_prop_growth_large_root_irAnchor n om := by
    funext om
    rw [Finset.sum_apply]
    unfold aux_prop_growth_large_root_irAnchor
    rw [hs, Finset.sum_image (fun a _ b _ hab => by
      have hab' : (a : ℤ) + 1 = (b : ℤ) + 1 := hab
      omega)]
    rfl
  rw [hfun] at hsum
  exact hsum.symm

/-- The layer-sum exponential moment: `E[exp(q * irAnchor_j)] ≤ (2 exp(q^2 delta^2 / 4))^j`,
by independence of the layers (product of per-layer moment generating functions). -/
theorem aux_tight_static_irAnchor_moment
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (q : ℝ) :
    Integrable (fun om : BilateralField d =>
        Real.exp (q * aux_prop_growth_large_root_irAnchor j om))
      (chaosSampleLaw M).toMeasure ∧
    ∫ om, Real.exp (q * aux_prop_growth_large_root_irAnchor j om)
        ∂(chaosSampleLaw M).toMeasure ≤
      (2 * Real.exp (q ^ 2 * M.delta ^ 2 / 4)) ^ j := by
  induction j with
  | zero =>
    constructor
    · simpa [aux_prop_growth_large_root_irAnchor] using integrable_const (1 : ℝ)
    · simp [aux_prop_growth_large_root_irAnchor]
  | succ n ih =>
    obtain ⟨ihint, ihbound⟩ := ih
    have hstep := aux_tight_static_layer_exp_moment M ((n : ℤ) + 1) q
    have hindepFun := aux_tight_static_irAnchor_indepFun M n
    have hindepExp : IndepFun (fun om : BilateralField d => Real.exp (q * (om ((n : ℤ) + 1) 0)))
        (fun om : BilateralField d => Real.exp (q * aux_prop_growth_large_root_irAnchor n om))
        (chaosSampleLaw M).toMeasure :=
      hindepFun.comp (Measurable.exp (measurable_const.mul measurable_id))
        (Measurable.exp (measurable_const.mul measurable_id))
    have hrec : ∀ om : BilateralField d,
        Real.exp (q * aux_prop_growth_large_root_irAnchor (n + 1) om) =
          Real.exp (q * (om ((n : ℤ) + 1) 0)) *
            Real.exp (q * aux_prop_growth_large_root_irAnchor n om) := by
      intro om
      rw [← Real.exp_add]
      congr 1
      unfold aux_prop_growth_large_root_irAnchor
      rw [Finset.sum_range_succ]
      simp only [Int.ofNat_eq_natCast]
      push_cast
      ring_nf
    have hintProd : Integrable (fun om : BilateralField d =>
        Real.exp (q * (om ((n : ℤ) + 1) 0)) *
          Real.exp (q * aux_prop_growth_large_root_irAnchor n om))
        (chaosSampleLaw M).toMeasure :=
      hindepExp.integrable_mul hstep.1 ihint
    refine ⟨?_, ?_⟩
    · simpa only [← hrec] using hintProd
    · calc
        ∫ om, Real.exp (q * aux_prop_growth_large_root_irAnchor (n + 1) om)
            ∂(chaosSampleLaw M).toMeasure =
            ∫ om, Real.exp (q * (om ((n : ℤ) + 1) 0)) *
              Real.exp (q * aux_prop_growth_large_root_irAnchor n om)
              ∂(chaosSampleLaw M).toMeasure := by
          simp only [hrec]
        _ = (∫ om, Real.exp (q * (om ((n : ℤ) + 1) 0)) ∂(chaosSampleLaw M).toMeasure) *
              ∫ om, Real.exp (q * aux_prop_growth_large_root_irAnchor n om)
                ∂(chaosSampleLaw M).toMeasure :=
          hindepExp.integral_fun_mul_eq_mul_integral hstep.1.aestronglyMeasurable
            ihint.aestronglyMeasurable
        _ ≤ (2 * Real.exp (q ^ 2 * M.delta ^ 2 / 4)) * (2 * Real.exp (q ^ 2 * M.delta ^ 2 / 4)) ^ n := by
          apply mul_le_mul hstep.2 ihbound
          · exact (integral_nonneg fun om => (Real.exp_pos _).le)
          · positivity
        _ = (2 * Real.exp (q ^ 2 * M.delta ^ 2 / 4)) ^ (n + 1) := by ring

/- ===================================================================================
   End of copied C-moment chain. The two target theorems follow.
   =================================================================================== -/



theorem aux_hcut_exp_H_moment (hd : 2 ≤ d) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ R →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (C * lam ^ 2 * M.delta ^ 2) := by
  obtain ⟨Cf, hCf, hmain⟩ :=
    SubdiffusiveProcess.exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall (0 : SpatialCoordinates d) R, isCompact_closedBall 0 R⟩
  refine ⟨Cf K, hCf K, ?_⟩
  intro M H hH lam hlam y hy
  have hyK : y ∈ (K : Set (SpatialCoordinates d)) := by
    change dist y (0 : SpatialCoordinates d) ≤ R
    rwa [dist_zero_right]
  obtain ⟨hIntK, hBoundK⟩ := hmain M H hH K lam hlam
  have hptwise : ∀ om : BilateralField d,
      |H om y| ≤ ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ := by
    intro om
    have hb := ContinuousMap.norm_coe_le_norm
      ((H om).restrict (K : Set (SpatialCoordinates d))) (⟨y, hyK⟩ : K)
    rwa [ContinuousMap.restrict_apply, Real.norm_eq_abs] at hb
  have hmeas : Measurable (fun om : BilateralField d => Real.exp (lam * |H om y|)) :=
    (measurable_const.mul (continuous_abs.measurable.comp
      ((continuous_eval_const y).measurable.comp hH.1))).exp
  have hInt : Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure := by
    apply hIntK.mono' hmeas.aestronglyMeasurable
    filter_upwards with om
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (hptwise om) hlam
  refine ⟨hInt, ?_⟩
  calc ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure
      ≤ ∫ om, Real.exp (lam * ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
          ∂(chaosSampleLaw M).toMeasure :=
        integral_mono hInt hIntK (fun om => Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hptwise om) hlam))
    _ ≤ 2 * Real.exp (Cf K * lam ^ 2 * M.delta ^ 2) := hBoundK

/-- **(M2) Moments of the scale envelope, linear in `n`.** `shiftEnv M n om = exp(n|τ²| +
|X_n om|)` with `X_n = irAnchor n`. Raising to the `p`-th power and splitting `exp(p|X_n|) ≤
exp(p X_n) + exp(-p X_n)` reduces to the two signed layer-sum moments
`aux_tight_static_irAnchor_moment M n (±p)`. -/
theorem aux_hcut_shiftEnv_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    ∫ om, aux_prop_growth_large_root_shiftEnv M n om ^ p ∂(chaosSampleLaw M).toMeasure ≤
      2 * (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4 + p * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n := by
  set τ2 : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P with hτ2def
  have hInt1 := aux_tight_static_irAnchor_moment M n p
  have hInt2 := aux_tight_static_irAnchor_moment M n (-p)
  have hInt2' : Integrable (fun om : BilateralField d =>
      Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om))) (chaosSampleLaw M).toMeasure := by
    have heq : (fun om : BilateralField d => Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om))) =
        (fun om : BilateralField d => Real.exp ((-p) * aux_prop_growth_large_root_irAnchor n om)) := by
      funext om; congr 1; ring
    rw [heq]; exact hInt2.1
  have hb2 : ∫ om, Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om))
      ∂(chaosSampleLaw M).toMeasure ≤ (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4)) ^ n := by
    have heq : (fun om : BilateralField d => Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om))) =
        (fun om : BilateralField d => Real.exp ((-p) * aux_prop_growth_large_root_irAnchor n om)) := by
      funext om; congr 1; ring
    rw [heq]
    have h := hInt2.2
    have heqsq : (-p) ^ 2 = p ^ 2 := by ring
    rwa [heqsq] at h
  have hbound : ∀ om : BilateralField d,
      aux_prop_growth_large_root_shiftEnv M n om ^ p ≤
        Real.exp (p * (n : ℝ) * |τ2|) * Real.exp (p * aux_prop_growth_large_root_irAnchor n om) +
        Real.exp (p * (n : ℝ) * |τ2|) *
          Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om)) := by
    intro om
    have hEq : aux_prop_growth_large_root_shiftEnv M n om ^ p =
        Real.exp (p * (n : ℝ) * |τ2|) *
          Real.exp (p * |aux_prop_growth_large_root_irAnchor n om|) := by
      unfold aux_prop_growth_large_root_shiftEnv
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
      congr 1
      ring
    have hsplit : Real.exp (p * |aux_prop_growth_large_root_irAnchor n om|) ≤
        Real.exp (p * aux_prop_growth_large_root_irAnchor n om) +
          Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om)) := by
      rcases le_or_lt 0 (aux_prop_growth_large_root_irAnchor n om) with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_neg hx]
        have hxeq : p * -(aux_prop_growth_large_root_irAnchor n om) =
            -(p * aux_prop_growth_large_root_irAnchor n om) := by ring
        rw [hxeq]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    rw [hEq]
    calc Real.exp (p * (n : ℝ) * |τ2|) *
        Real.exp (p * |aux_prop_growth_large_root_irAnchor n om|)
        ≤ Real.exp (p * (n : ℝ) * |τ2|) *
            (Real.exp (p * aux_prop_growth_large_root_irAnchor n om) +
              Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om))) :=
          mul_le_mul_of_nonneg_left hsplit (Real.exp_pos _).le
      _ = _ := by ring
  have hIntG : Integrable (fun om : BilateralField d =>
      Real.exp (p * (n : ℝ) * |τ2|) * Real.exp (p * aux_prop_growth_large_root_irAnchor n om) +
      Real.exp (p * (n : ℝ) * |τ2|) *
        Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om)))
      (chaosSampleLaw M).toMeasure :=
    (hInt1.1.const_mul _).add (hInt2'.const_mul _)
  have hmain : ∫ om, aux_prop_growth_large_root_shiftEnv M n om ^ p
      ∂(chaosSampleLaw M).toMeasure ≤
      ∫ om, (Real.exp (p * (n : ℝ) * |τ2|) *
          Real.exp (p * aux_prop_growth_large_root_irAnchor n om) +
        Real.exp (p * (n : ℝ) * |τ2|) *
          Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om)))
        ∂(chaosSampleLaw M).toMeasure :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun om =>
      Real.rpow_nonneg (Real.exp_pos _).le p) hIntG (Filter.Eventually.of_forall hbound)
  have hsplitInt : ∫ om, (Real.exp (p * (n : ℝ) * |τ2|) *
        Real.exp (p * aux_prop_growth_large_root_irAnchor n om) +
      Real.exp (p * (n : ℝ) * |τ2|) *
        Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om)))
      ∂(chaosSampleLaw M).toMeasure =
      Real.exp (p * (n : ℝ) * |τ2|) *
        (∫ om, Real.exp (p * aux_prop_growth_large_root_irAnchor n om)
          ∂(chaosSampleLaw M).toMeasure) +
      Real.exp (p * (n : ℝ) * |τ2|) *
        (∫ om, Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om))
          ∂(chaosSampleLaw M).toMeasure) := by
    rw [integral_add (hInt1.1.const_mul _) (hInt2'.const_mul _), integral_const_mul,
      integral_const_mul]
  have hfinal : Real.exp (p * (n : ℝ) * |τ2|) *
        (∫ om, Real.exp (p * aux_prop_growth_large_root_irAnchor n om)
          ∂(chaosSampleLaw M).toMeasure) +
      Real.exp (p * (n : ℝ) * |τ2|) *
        (∫ om, Real.exp (-(p * aux_prop_growth_large_root_irAnchor n om))
          ∂(chaosSampleLaw M).toMeasure) ≤
      Real.exp (p * (n : ℝ) * |τ2|) * (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4)) ^ n +
      Real.exp (p * (n : ℝ) * |τ2|) * (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4)) ^ n :=
    add_le_add (mul_le_mul_of_nonneg_left hInt1.2 (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_left hb2 (Real.exp_pos _).le)
  have hcollapseTerm : Real.exp (p * (n : ℝ) * |τ2|) * (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4)) ^ n =
      (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4 + p * |τ2|)) ^ n := by
    have hB : Real.exp (p * (n : ℝ) * |τ2|) = (Real.exp (p * |τ2|)) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hB, Real.exp_add]
    simp only [mul_pow]
    ring
  have hcollapse : Real.exp (p * (n : ℝ) * |τ2|) * (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4)) ^ n +
      Real.exp (p * (n : ℝ) * |τ2|) * (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4)) ^ n =
      2 * (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4 + p * |τ2|)) ^ n := by
    rw [hcollapseTerm]; ring
  calc ∫ om, aux_prop_growth_large_root_shiftEnv M n om ^ p ∂(chaosSampleLaw M).toMeasure
      ≤ _ := hmain
    _ = _ := hsplitInt
    _ ≤ _ := hfinal
    _ = _ := hcollapse

end Paper
end
end

-- ===== module HCut.StageBMom =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Cauchy–Schwarz for `ofReal` of powers of products. -/
lemma aux_hcut_cs_ofReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (p : ℝ) (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal ((f ω * g ω) ^ p) ∂μ ≤
      (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * p)) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * p)) ∂μ) ^ (1 / 2 : ℝ) := by
  have hF : AEMeasurable (fun ω => ENNReal.ofReal (f ω ^ p)) μ :=
    (ENNReal.measurable_ofReal.comp (hf.pow_const p)).aemeasurable
  have hG : AEMeasurable (fun ω => ENNReal.ofReal (g ω ^ p)) μ :=
    (ENNReal.measurable_ofReal.comp (hg.pow_const p)).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hF hG
  have e1 : ∀ ω, ENNReal.ofReal ((f ω * g ω) ^ p) =
      (fun ω => ENNReal.ofReal (f ω ^ p)) ω * (fun ω => ENNReal.ofReal (g ω ^ p)) ω := fun ω => by
    simp only
    rw [Real.mul_rpow (hf0 ω) (hg0 ω), ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 ω) _)]
  have e2 : ∀ (u : Ω → ℝ), (∀ ω, 0 ≤ u ω) → ∀ ω,
      ENNReal.ofReal (u ω ^ p) ^ (2 : ℝ) = ENNReal.ofReal (u ω ^ (2 * p)) := fun u hu ω => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hu ω) _) (by norm_num),
      ← Real.rpow_mul (hu ω), mul_comm]
  simp_rw [e1]
  refine h.trans (le_of_eq ?_)
  simp only [one_div]
  congr 2
  · exact lintegral_congr fun ω => e2 f hf0 ω
  · exact lintegral_congr fun ω => e2 g hg0 ω

section Cell
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hcut_measurable_cellEnv (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (y : SpatialCoordinates d)
    (n : ℕ) : Measurable (aux_hcut_cellEnv (d := d) y n) :=
  (aux_hcut_measurePreserving_cellEnv M y n).measurable

lemma aux_hcut_measurable_shiftConst (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j N : ℕ) :
    Measurable (aux_prop_growth_large_root_shiftConst M j N) := by
  unfold aux_prop_growth_large_root_shiftConst
  exact measurable_const.mul (measurable_const.sub
    (aux_prop_growth_large_root_measurable_irAnchor j)).exp

lemma aux_hcut_measurable_cellConst (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) (n N : ℕ) : Measurable (aux_hcut_cellConst M H y n N) := by
  unfold aux_hcut_cellConst
  have hHy : Measurable fun om => H om y :=
    (continuous_eval_const y).measurable.comp hH.1
  exact hHy.exp.mul ((aux_hcut_measurable_shiftConst M n (N - n)).comp
    (aux_hcut_measurable_cellEnv M y n)).inv

/-- Envelope of the cell constant (`n ≥ 1`). -/
lemma aux_hcut_cellConst_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d) {n N : ℕ}
    (hn : 1 ≤ n) (om : BilateralField d) :
    aux_hcut_cellConst M H y n N om ≤
      Real.exp (|H om y|) * aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om) := by
  unfold aux_hcut_cellConst
  exact mul_le_mul (Real.exp_le_exp.2 (le_abs_self _))
    (aux_prop_growth_large_root_shiftConst_inv_le M Rm n (N - n) (by omega) _)
    (inv_nonneg.2 (aux_prop_growth_large_root_shiftConst_pos M Rm _ _ _).le) (Real.exp_pos _).le

/-- `∫⁻ ofReal(shiftEnv^p) ≤ ofReal(M2 bound)`. -/
lemma aux_hcut_shiftEnv_lintegral (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    ∫⁻ om, ENNReal.ofReal (aux_prop_growth_large_root_shiftEnv M n om ^ p) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (2 * Real.exp (p ^ 2 * M.delta ^ 2 / 4 +
        p * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) := by
  have hmem := aux_prop_growth_large_root_memLp_shiftEnv M n p hp
  have hint : Integrable (fun om => aux_prop_growth_large_root_shiftEnv M n om ^ p)
      (chaosSampleLaw M).toMeasure := by
    have h0 : ∀ om, 0 ≤ aux_prop_growth_large_root_shiftEnv M n om := fun om =>
      le_trans zero_le_one (aux_prop_growth_large_root_one_le_shiftEnv M n om)
    have := hmem.integrable_norm_rpow (by positivity) (by simp)
    refine this.congr (Eventually.of_forall fun om => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (h0 om), ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ p)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun om =>
    Real.rpow_nonneg (le_trans zero_le_one (aux_prop_growth_large_root_one_le_shiftEnv M n om)) _)]
  exact ENNReal.ofReal_le_ofReal (aux_hcut_shiftEnv_moment M n p hp)

/-- **Per-cell moment bound.** -/
lemma aux_hcut_X_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) {n N : ℕ} (hn : 1 ≤ n)
    (K : BilateralField d → ℝ) (hK : Measurable K) (hK0 : ∀ om, 0 ≤ K om) (p : ℝ) (hp : 1 ≤ p)
    (EH : ℝ≥0∞)
    (hEH : ∫⁻ om, ENNReal.ofReal (Real.exp (4 * p * |H om y|)) ∂(chaosSampleLaw M).toMeasure ≤ EH) :
    ∫⁻ om, ENNReal.ofReal ((aux_hcut_cellConst M H y n N om * K (aux_hcut_cellEnv y n om)) ^ p)
        ∂(chaosSampleLaw M).toMeasure ≤
      (EH ^ (1 / 2 : ℝ) * ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
          (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ om, ENNReal.ofReal (K om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hmp := aux_hcut_measurePreserving_cellEnv M y n
  have hc := aux_hcut_measurable_cellConst M hH y n N
  have hc0 : ∀ om, 0 ≤ aux_hcut_cellConst M H y n N om := fun om =>
    (aux_hcut_cellConst_pos M Rm H y n N om).le
  have h1 := aux_hcut_cs_ofReal (chaosSampleLaw M).toMeasure (aux_hcut_cellConst M H y n N)
    (fun om => K (aux_hcut_cellEnv y n om)) hc (hK.comp hmp.measurable) hc0 (fun om => hK0 _) p hp0
  have h2 : ∫⁻ om, ENNReal.ofReal (K (aux_hcut_cellEnv y n om) ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure =
      ∫⁻ om, ENNReal.ofReal (K om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure :=
    hmp.lintegral_comp (f := fun om => ENNReal.ofReal (K om ^ (2 * p)))
      (ENNReal.measurable_ofReal.comp (hK.pow_const _))
  -- the cell constant
  have hHy : Measurable fun om => H om y := (continuous_eval_const y).measurable.comp hH.1
  have hS : Measurable fun om => aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om) := by
    unfold aux_prop_growth_large_root_shiftEnv
    exact (measurable_const.add ((aux_prop_growth_large_root_measurable_irAnchor n).comp
      hmp.measurable).abs).exp
  have h3 : ∫⁻ om, ENNReal.ofReal (aux_hcut_cellConst M H y n N om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤
      ∫⁻ om, ENNReal.ofReal ((Real.exp (|H om y|) *
        aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om)) ^ (2 * p))
        ∂(chaosSampleLaw M).toMeasure :=
    lintegral_mono fun om => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (hc0 om) (aux_hcut_cellConst_le M Rm H y hn om) (by positivity))
  have h4 := aux_hcut_cs_ofReal (chaosSampleLaw M).toMeasure (fun om => Real.exp (|H om y|))
    (fun om => aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om)) hHy.abs.exp hS
    (fun om => (Real.exp_pos _).le)
    (fun om => le_trans zero_le_one (aux_prop_growth_large_root_one_le_shiftEnv M n _)) (2 * p) (by positivity)
  have h5 : ∫⁻ om, ENNReal.ofReal (Real.exp (|H om y|) ^ (2 * (2 * p))) ∂(chaosSampleLaw M).toMeasure ≤ EH := by
    refine le_trans (le_of_eq (lintegral_congr fun om => ?_)) hEH
    rw [← Real.exp_mul]; ring_nf
  have h6 : ∫⁻ om, ENNReal.ofReal (aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om) ^ (2 * (2 * p)))
      ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
          (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) := by
    rw [hmp.lintegral_comp (f := fun om => ENNReal.ofReal
      (aux_prop_growth_large_root_shiftEnv M n om ^ (2 * (2 * p))))
      (ENNReal.measurable_ofReal.comp (by
        unfold aux_prop_growth_large_root_shiftEnv
        exact ((measurable_const.add (aux_prop_growth_large_root_measurable_irAnchor n).abs).exp).pow_const _))]
    have e : 2 * (2 * p) = 4 * p := by ring
    rw [e]
    exact aux_hcut_shiftEnv_lintegral M n (4 * p) (by linarith)
  calc ∫⁻ om, ENNReal.ofReal ((aux_hcut_cellConst M H y n N om * K (aux_hcut_cellEnv y n om)) ^ p)
        ∂(chaosSampleLaw M).toMeasure
      ≤ (∫⁻ om, ENNReal.ofReal (aux_hcut_cellConst M H y n N om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^
            (1 / 2 : ℝ) *
          (∫⁻ om, ENNReal.ofReal (K (aux_hcut_cellEnv y n om) ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^
            (1 / 2 : ℝ) := h1
    _ ≤ (EH ^ (1 / 2 : ℝ) * ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
          (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ om, ENNReal.ofReal (K om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ) := by
        rw [h2]
        gcongr
        exact h3.trans (h4.trans (by gcongr))

/-- Real form of the per-cell moment under the smallness condition. -/
lemma aux_hcut_X_moment_real (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (R CH : ℝ) (hCH : ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ R →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (y : SpatialCoordinates d) (hy : ‖y‖ ≤ R) {n N : ℕ} (hn : 1 ≤ n)
    (K : BilateralField d → ℝ) (hK : Measurable K) (hK0 : ∀ om, 0 ≤ K om) (p : ℝ) (hp : 1 ≤ p)
    (Cb2 : ℝ) (hCb2 : 0 ≤ Cb2)
    (hKb : ∫⁻ om, ENNReal.ofReal (K om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb2)
    (hsmall : Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2) :
    ∫⁻ om, ENNReal.ofReal ((aux_hcut_cellConst M H y n N om * K (aux_hcut_cellEnv y n om)) ^ p)
        ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) *
        (2 * 4 ^ n) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hint, hbd⟩ := hCH (4 * p) (by positivity) y hy
  have hEH : ∫⁻ om, ENNReal.ofReal (Real.exp (4 * p * |H om y|)) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun om => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hbd
  have hX := aux_hcut_X_moment M Rm hH y (N := N) hn K hK hK0 p hp _ hEH
  refine hX.trans ?_
  have hS : ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
      (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) ≤ ENNReal.ofReal (2 * 4 ^ n) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have : 2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 4 := by
      linarith
    have h0 : 0 ≤ 2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) := by
      positivity
    gcongr
  have hA0 : 0 ≤ 2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2) := by positivity
  calc (ENNReal.ofReal (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
            (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ om, ENNReal.ofReal (K om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (2 * 4 ^ n) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) * ENNReal.ofReal Cb2 ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal ((2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) *
          (2 * 4 ^ n) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hCb2 (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hA0,
          ← Real.rpow_mul (by positivity)]
        norm_num

end Cell

end Paper
end
end

-- ===== module HCut.ProbLp =====
section
open MeasureTheory Filter
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace HCut

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- (L1) `∫⁻ ofReal(f^q) = ‖f‖_q^q` for nonnegative `f`. -/
lemma aux_hcut_lintegral_ofReal_rpow_eq {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) {q : ℝ} (hq : 0 < q) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ = eLpNorm f (ENNReal.ofReal q) μ ^ q := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hq.le]

/-- (L2) The `ℓ^Q` aggregate of a finite family has `Q`-moment equal to the sum of the `Q`-moments. -/
lemma aux_hcut_lintegral_lpsum {ι : Type*} (S : Finset ι) (X : ι → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hX0 : ∀ k ω, 0 ≤ X k ω) {Q : ℝ} (hQ : 0 < Q) :
    ∫⁻ ω, ENNReal.ofReal (((∑ k ∈ S, X k ω ^ Q) ^ (1 / Q)) ^ Q) ∂μ =
      ∑ k ∈ S, ∫⁻ ω, ENNReal.ofReal (X k ω ^ Q) ∂μ := by
  have hs : ∀ ω, 0 ≤ ∑ k ∈ S, X k ω ^ Q := fun ω =>
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hX0 k ω) _
  have e : ∀ ω, ((∑ k ∈ S, X k ω ^ Q) ^ (1 / Q)) ^ Q = ∑ k ∈ S, X k ω ^ Q := fun ω => by
    rw [← Real.rpow_mul (hs ω), one_div, inv_mul_cancel₀ hQ.ne', Real.rpow_one]
  simp_rw [e]
  have hm : ∀ k ∈ S, Measurable fun ω => ENNReal.ofReal (X k ω ^ Q) := fun k _ =>
    ENNReal.measurable_ofReal.comp ((hX k).pow_const Q)
  rw [← lintegral_finset_sum S hm]
  refine lintegral_congr fun ω => ?_
  exact ENNReal.ofReal_sum_of_nonneg fun k _ => Real.rpow_nonneg (hX0 k ω) _

/-- (L4) Lyapunov on a probability space. -/
lemma aux_hcut_eLpNorm_mono_exp [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {q q' : ℝ} (hq : 0 < q) (hqq : q ≤ q') :
    eLpNorm f (ENNReal.ofReal q) μ ≤ eLpNorm f (ENNReal.ofReal q') μ :=
  eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqq) hf

/-- (L3) Minkowski for `1 + C₁ Kup + C₂ Σₙ aₙ Mₙ`. -/
lemma aux_hcut_eLpNorm_Kcut_le [IsProbabilityMeasure μ] (Kup : Ω → ℝ) (Mn : ℕ → Ω → ℝ) (I : Finset ℕ)
    (a : ℕ → ℝ) (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (ha : ∀ n, 0 ≤ a n)
    (hKup : AEStronglyMeasurable Kup μ) (hMn : ∀ n, AEStronglyMeasurable (Mn n) μ)
    {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun ω => 1 + C1 * Kup ω + C2 * ∑ n ∈ I, a n * Mn n ω) (ENNReal.ofReal q) μ ≤
      1 + ENNReal.ofReal C1 * eLpNorm Kup (ENNReal.ofReal q) μ +
        ENNReal.ofReal C2 * ∑ n ∈ I, ENNReal.ofReal (a n) * eLpNorm (Mn n) (ENNReal.ofReal q) μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hconst : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal q) μ = 1 := by
    rw [eLpNorm_const (1 : ℝ) hq0 (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow,
      mul_one]
    simp
  have hsm : ∀ n, AEStronglyMeasurable (fun ω => a n * Mn n ω) μ := fun n => (hMn n).const_mul _
  have hsum : AEStronglyMeasurable (fun ω => ∑ n ∈ I, a n * Mn n ω) μ :=
    Finset.aestronglyMeasurable_fun_sum I (fun n _ => hsm n)
  have hS : eLpNorm (fun ω => ∑ n ∈ I, a n * Mn n ω) (ENNReal.ofReal q) μ ≤
      ∑ n ∈ I, ENNReal.ofReal (a n) * eLpNorm (Mn n) (ENNReal.ofReal q) μ := by
    have h := eLpNorm_sum_le (s := I) (f := fun n => fun ω => a n * Mn n ω) (fun n _ => hsm n) hp1
    have e : (∑ n ∈ I, fun ω => a n * Mn n ω) = fun ω => ∑ n ∈ I, a n * Mn n ω := by
      funext ω; simp [Finset.sum_apply]
    rw [e] at h
    refine h.trans (Finset.sum_le_sum fun n _ => le_of_eq ?_)
    beta_reduce
    have : (fun ω => a n * Mn n ω) = a n • Mn n := by funext ω; simp
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (ha n)]
  have hK1 : eLpNorm (fun ω => C1 * Kup ω) (ENNReal.ofReal q) μ = ENNReal.ofReal C1 * eLpNorm Kup (ENNReal.ofReal q) μ := by
    have : (fun ω => C1 * Kup ω) = C1 • Kup := by funext ω; simp
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hC1]
  have hK2 : eLpNorm (fun ω => C2 * ∑ n ∈ I, a n * Mn n ω) (ENNReal.ofReal q) μ =
      ENNReal.ofReal C2 * eLpNorm (fun ω => ∑ n ∈ I, a n * Mn n ω) (ENNReal.ofReal q) μ := by
    have : (fun ω => C2 * ∑ n ∈ I, a n * Mn n ω) = C2 • (fun ω => ∑ n ∈ I, a n * Mn n ω) := by
      funext ω; simp
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hC2]
  calc eLpNorm (fun ω => 1 + C1 * Kup ω + C2 * ∑ n ∈ I, a n * Mn n ω) (ENNReal.ofReal q) μ
      ≤ eLpNorm (fun ω => 1 + C1 * Kup ω) (ENNReal.ofReal q) μ +
          eLpNorm (fun ω => C2 * ∑ n ∈ I, a n * Mn n ω) (ENNReal.ofReal q) μ :=
        eLpNorm_add_le (aestronglyMeasurable_const.add (hKup.const_mul _)) (hsum.const_mul _) hp1
    _ ≤ (eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal q) μ +
          eLpNorm (fun ω => C1 * Kup ω) (ENNReal.ofReal q) μ) +
          eLpNorm (fun ω => C2 * ∑ n ∈ I, a n * Mn n ω) (ENNReal.ofReal q) μ := by
        gcongr
        exact eLpNorm_add_le aestronglyMeasurable_const (hKup.const_mul _) hp1
    _ ≤ _ := by
        rw [hconst, hK1, hK2]
        gcongr

end HCut
end
end

-- ===== module HCut.SupHelpers =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hcut_term_le_lpsum {ι : Type*} (S : Finset ι) (X : ι → ℝ) (hX0 : ∀ k, 0 ≤ X k) {Q : ℝ}
    (hQ : 0 < Q) {k : ι} (hk : k ∈ S) : X k ≤ (∑ j ∈ S, X j ^ Q) ^ (1 / Q) := by
  have h1 : X k = (X k ^ Q) ^ (1 / Q) := by
    rw [← Real.rpow_mul (hX0 k), mul_one_div_cancel hQ.ne', Real.rpow_one]
  rw [h1]
  exact Real.rpow_le_rpow (Real.rpow_nonneg (hX0 k) _)
    (Finset.single_le_sum (f := fun j => X j ^ Q) (fun j _ => Real.rpow_nonneg (hX0 j) _) hk)
    (by positivity)

lemma aux_hcut_ahom_inv_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (hsmall : 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ Real.log 3) :
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * (3 : ℝ) ^ N := by
  have hN := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have h0 := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0
  have hratio := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.ahom_ratio_eq_exp_normalizerLogError M N 0
  have herr := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.abs_normalizerLogError_le_of_le M (Nat.zero_le N)
  have htau := (M.G4.tauSq_pos).le
  have hle : SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤ (3 : ℝ) ^ N := by
    rw [hratio]
    have hexp : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((N - 0 : ℕ) : ℝ) +
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.normalizerLogError M N 0 ≤ (N : ℝ) * Real.log 3 := by
      have := (abs_le.1 herr).2
      simp only [Nat.sub_zero] at this ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    calc Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((N - 0 : ℕ) : ℝ) +
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.normalizerLogError M N 0)
        ≤ Real.exp ((N : ℝ) * Real.log 3) := Real.exp_le_exp.2 hexp
      _ = (3 : ℝ) ^ N := by rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [div_le_iff₀ hN] at hle
  rw [inv_le_iff_one_le_mul₀ hN]
  calc (1 : ℝ) = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 := by
        field_simp
    _ ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * ((3 : ℝ) ^ N * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
        gcongr
    _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * (3 : ℝ) ^ N * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := by
        ring

lemma aux_hcut_geom_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, r ^ n ≤ 2 := by
  calc ∑ n ∈ Finset.Icc 1 N, r ^ n ≤ ∑ n ∈ Finset.range (N + 1), r ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
          simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_range]; omega)
          (fun n _ _ => pow_nonneg hr0 n)
    _ ≤ ∑' n, r ^ n := (summable_geometric_of_lt_one hr0 (by linarith)).sum_le_tsum _
          (fun n _ => pow_nonneg hr0 n)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 (by linarith)
    _ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith

end Paper
end
end

-- ===== module HCut.Supplier1 =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hcut_S_spec {rho0 : ℝ} {n : ℕ} {k : Fin d → ℤ} (hk : k ∈ aux_hcut_S (d := d) rho0 n) :
    HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2) := by
  classical
  unfold aux_hcut_S at hk
  exact (Finset.mem_filter.1 hk).2

/-- The per-cell random constant. -/
def aux_hcut_X (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : ℕ → BilateralField d → ℝ) (N n : ℕ) (k : Fin d → ℤ) (om : BilateralField d) : ℝ :=
  aux_hcut_cellConst M H (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) n N om *
    K (N - n) (aux_hcut_cellEnv (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) n om)

/-- The level-`n` aggregate `(Σ_{k∈S_n} X^Q)^{1/Q}`. -/
def aux_hcut_M (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : ℕ → BilateralField d → ℝ) (rho0 Q : ℝ) (N n : ℕ) (om : BilateralField d) : ℝ :=
  (∑ k ∈ aux_hcut_S (d := d) rho0 n, aux_hcut_X M H K N n k om ^ Q) ^ (1 / Q)

lemma aux_hcut_X_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : ℕ → BilateralField d → ℝ)
    (hK1 : ∀ m om, 1 ≤ K m om) (N n : ℕ) (k : Fin d → ℤ) (om : BilateralField d) :
    0 ≤ aux_hcut_X M H K N n k om :=
  mul_nonneg (aux_hcut_cellConst_pos M Rm H _ n N om).le (le_trans zero_le_one (hK1 _ _))

lemma aux_hcut_measurable_X (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (K : ℕ → BilateralField d → ℝ) (hKm : ∀ m, Measurable (K m)) (N n : ℕ) (k : Fin d → ℤ) :
    Measurable (aux_hcut_X M H K N n k) :=
  (aux_hcut_measurable_cellConst M hH _ n N).mul ((hKm _).comp (aux_hcut_measurable_cellEnv M _ n))

lemma aux_hcut_measurable_M (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (K : ℕ → BilateralField d → ℝ) (hKm : ∀ m, Measurable (K m)) (rho0 Q : ℝ) (N n : ℕ) :
    Measurable (aux_hcut_M M H K rho0 Q N n) := by
  unfold aux_hcut_M
  exact (Finset.measurable_sum _ fun k _ => (aux_hcut_measurable_X M hH K hKm N n k).pow_const Q).pow_const _

lemma aux_hcut_M_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : ℕ → BilateralField d → ℝ) (hK1 : ∀ m om, 1 ≤ K m om) (rho0 Q : ℝ) (N n : ℕ)
    (om : BilateralField d) : 0 ≤ aux_hcut_M M H K rho0 Q N n om :=
  Real.rpow_nonneg (Finset.sum_nonneg fun k _ =>
    Real.rpow_nonneg (aux_hcut_X_nonneg M Rm H K hK1 N n k om) _) _

lemma aux_hcut_ratio_le (d : ℕ) {Q : ℝ} (hQd : 8 * ((d : ℝ) + 1) ≤ Q) :
    (4 * (3 : ℝ) ^ d) ^ (1 / Q) ≤ 3 / 2 := by
  have hQ0 : 0 < Q := by have : (0 : ℝ) ≤ d := by positivity
                         linarith
  have h1 : 4 * (3 : ℝ) ^ d ≤ (3 / 2 : ℝ) ^ Q := by
    have h8 : (25 : ℝ) ≤ (3 / 2) ^ (8 : ℕ) := by norm_num
    have h2 : (25 : ℝ) ^ (d + 1) ≤ ((3 / 2 : ℝ) ^ (8 : ℕ)) ^ (d + 1) := pow_le_pow_left₀ (by norm_num) h8 _
    have h3 : 4 * (3 : ℝ) ^ d ≤ (25 : ℝ) ^ (d + 1) := by
      rw [pow_succ]
      have : (3 : ℝ) ^ d ≤ 25 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
      have h0 : (0 : ℝ) ≤ 25 ^ d := by positivity
      linarith
    have h4 : ((3 / 2 : ℝ) ^ (8 : ℕ)) ^ (d + 1) = (3 / 2 : ℝ) ^ (8 * ((d : ℝ) + 1)) := by
      rw [← pow_mul, ← Real.rpow_natCast]; push_cast; ring_nf
    have h5 : (3 / 2 : ℝ) ^ (8 * ((d : ℝ) + 1)) ≤ (3 / 2 : ℝ) ^ Q :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hQd
    linarith
  calc (4 * (3 : ℝ) ^ d) ^ (1 / Q) ≤ ((3 / 2 : ℝ) ^ Q) ^ (1 / Q) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = 3 / 2 := by rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hQ0.ne', Real.rpow_one]

/-- **(P1a) Level aggregate moment.** -/
lemma aux_hcut_M_eLpNorm (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (rho0 : ℝ) (hrho : 1 ≤ rho0) (K : ℕ → BilateralField d → ℝ) (hKm : ∀ m, Measurable (K m))
    (hK1 : ∀ m om, 1 ≤ K m om) (Q : ℝ) (hQ1 : 1 ≤ Q) (hQd : 8 * ((d : ℝ) + 1) ≤ Q) (N n : ℕ) (hn : 1 ≤ n)
    (CH : ℝ) (hCH : ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ rho0 →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (Cb2 : ℝ) (hCb2 : 0 ≤ Cb2)
    (hKb : ∀ m, ∫⁻ om, ENNReal.ofReal (K m om ^ (2 * Q)) ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb2)
    (hsmall : Real.exp ((4 * Q) ^ 2 * M.delta ^ 2 / 4 + (4 * Q) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2) :
    eLpNorm (aux_hcut_M M H K rho0 Q N n) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((2 * rho0 + 3) ^ d * (2 * (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) *
        Cb2 ^ (1 / 2 : ℝ))) ^ (1 / Q) * (3 / 2) ^ n) := by
  have hQ0 : 0 < Q := by linarith
  set E1 : ℝ := 2 * (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ) with hE1
  have hE10 : 0 ≤ E1 := by positivity
  have hXk : ∀ k ∈ aux_hcut_S (d := d) rho0 n,
      ∫⁻ om, ENNReal.ofReal (aux_hcut_X M H K N n k om ^ Q) ∂(chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (E1 * 4 ^ n) := by
    intro k hk
    have hcc : ‖HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k‖ ≤ rho0 := by
      have h := aux_hcut_S_spec hk
      rw [Metric.mem_closedBall, dist_zero_right] at h
      linarith
    have hm := aux_hcut_X_moment_real hd M Rm hH rho0 CH hCH _ hcc (N := N) hn (K (N - n)) (hKm _)
      (fun om => le_trans zero_le_one (hK1 _ _)) Q hQ1 Cb2 hCb2 (hKb _) hsmall
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have h24 : (2 * (4 : ℝ) ^ n) ^ (1 / 4 : ℝ) ≤ 2 * 4 ^ n := by
      have h1 : (1 : ℝ) ≤ 2 * 4 ^ n := by
        have := one_le_pow₀ (M₀ := ℝ) (a := 4) (by norm_num) (n := n); linarith
      calc (2 * (4 : ℝ) ^ n) ^ (1 / 4 : ℝ) ≤ (2 * (4 : ℝ) ^ n) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = 2 * 4 ^ n := Real.rpow_one _
    have hA : 0 ≤ (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) := by positivity
    have hB : 0 ≤ Cb2 ^ (1 / 2 : ℝ) := by positivity
    calc (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * (2 * 4 ^ n) ^ (1 / 4 : ℝ) *
          Cb2 ^ (1 / 2 : ℝ)
        ≤ (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * (2 * 4 ^ n) * Cb2 ^ (1 / 2 : ℝ) := by
          gcongr
      _ = E1 * 4 ^ n := by rw [hE1]; ring
  have hint : ∫⁻ om, ENNReal.ofReal (aux_hcut_M M H K rho0 Q N n om ^ Q) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d * (E1 * 4 ^ n)) := by
    have hL2 := HCut.aux_hcut_lintegral_lpsum (chaosSampleLaw M).toMeasure (aux_hcut_S (d := d) rho0 n)
      (fun k => aux_hcut_X M H K N n k) (fun k => aux_hcut_measurable_X M hH K hKm N n k)
      (fun k om => aux_hcut_X_nonneg M Rm H K hK1 N n k om) hQ0
    unfold aux_hcut_M
    rw [hL2]
    refine (Finset.sum_le_sum hXk).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (aux_hcut_card_S (by linarith) n) (by positivity))
  have hL1 := HCut.aux_hcut_lintegral_ofReal_rpow_eq (chaosSampleLaw M).toMeasure
    (aux_hcut_M_nonneg M Rm H K hK1 rho0 Q N n) hQ0
  rw [hL1] at hint
  have hroot : eLpNorm (aux_hcut_M M H K rho0 Q N n) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d * (E1 * 4 ^ n)) ^ (1 / Q) := by
    have := ENNReal.rpow_le_rpow hint (by positivity : (0 : ℝ) ≤ 1 / Q)
    rwa [← ENNReal.rpow_mul, mul_one_div_cancel hQ0.ne', ENNReal.rpow_one] at this
  refine hroot.trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d * (E1 * 4 ^ n) =
      ((2 * rho0 + 3) ^ d * E1) * (4 * (3 : ℝ) ^ d) ^ n := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm n d]; ring
  rw [hsplit, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (4 * (3 : ℝ) ^ d) n,
    ← Real.rpow_mul (by positivity), mul_comm (n : ℝ) (1 / Q), Real.rpow_mul (by positivity),
    Real.rpow_natCast]
  have hr := aux_hcut_ratio_le d hQd
  gcongr

end Paper
end
end

-- ===== module HCut.Supplier2 =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The cutoff constant. -/
def aux_hcut_Kcut (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : ℕ → BilateralField d → ℝ) (Kup : BilateralField d → ℝ) (rho0 Q C1 C2 : ℝ) (N : ℕ)
    (om : BilateralField d) : ℝ :=
  1 + C1 * Kup om + C2 * ∑ n ∈ Finset.Icc 1 N, ((3 : ℝ) ^ n)⁻¹ * aux_hcut_M M H K rho0 Q N n om

/-- The moment bound of the cutoff constant. -/
lemma aux_hcut_Kcut_moment (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (rho0 : ℝ) (hrho : 1 ≤ rho0) (K : ℕ → BilateralField d → ℝ) (hKm : ∀ m, Measurable (K m))
    (hK1 : ∀ m om, 1 ≤ K m om) (q Q : ℝ) (hq : 1 ≤ q) (hqQ : q ≤ Q) (hQd : 8 * ((d : ℝ) + 1) ≤ Q)
    (CH : ℝ) (hCH : ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ rho0 →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (Cb2 : ℝ) (hCb2 : 0 ≤ Cb2)
    (hKb : ∀ m, ∫⁻ om, ENNReal.ofReal (K m om ^ (2 * Q)) ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb2)
    (hsmall : Real.exp ((4 * Q) ^ 2 * M.delta ^ 2 / 4 + (4 * Q) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2)
    (Kup : BilateralField d → ℝ) (hKupm : Measurable Kup) (hKup1 : ∀ om, 1 ≤ Kup om) (Cup : ℝ) (hCup : 0 ≤ Cup)
    (hKupq : ∫⁻ om, ENNReal.ofReal (Kup om ^ q) ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cup)
    (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (N : ℕ) :
    ∫⁻ om, ENNReal.ofReal (aux_hcut_Kcut M H K Kup rho0 Q C1 C2 N om ^ q) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((1 + C1 * Cup ^ (1 / q) + C2 * (2 * ((2 * rho0 + 3) ^ d *
        (2 * (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ))) ^ (1 / Q))) ^ q) := by
  have hq0 : 0 < q := by linarith
  have hQ1 : 1 ≤ Q := hq.trans hqQ
  set D : ℝ := ((2 * rho0 + 3) ^ d * (2 * (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) *
    Cb2 ^ (1 / 2 : ℝ))) ^ (1 / Q) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hKc0 : ∀ om, 0 ≤ aux_hcut_Kcut M H K Kup rho0 Q C1 C2 N om := fun om => by
    unfold aux_hcut_Kcut
    have := Finset.sum_nonneg fun n (_ : n ∈ Finset.Icc 1 N) =>
      mul_nonneg (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ n))
        (aux_hcut_M_nonneg M Rm H K hK1 rho0 Q N n om)
    have := hKup1 om
    positivity
  rw [HCut.aux_hcut_lintegral_ofReal_rpow_eq _ hKc0 hq0, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
  refine ENNReal.rpow_le_rpow ?_ hq0.le
  -- Minkowski
  have hMin := HCut.aux_hcut_eLpNorm_Kcut_le (chaosSampleLaw M).toMeasure Kup (aux_hcut_M M H K rho0 Q N)
    (Finset.Icc 1 N) (fun n => ((3 : ℝ) ^ n)⁻¹) C1 C2 hC1 hC2 (fun n => by positivity)
    hKupm.aestronglyMeasurable (fun n => (aux_hcut_measurable_M M hH K hKm rho0 Q N n).aestronglyMeasurable) hq
  refine hMin.trans ?_
  -- the three terms
  have hKupN : eLpNorm Kup (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cup ^ (1 / q)) := by
    have h := HCut.aux_hcut_lintegral_ofReal_rpow_eq (chaosSampleLaw M).toMeasure
      (fun om => le_trans zero_le_one (hKup1 om)) hq0 (f := Kup)
    rw [h] at hKupq
    have := ENNReal.rpow_le_rpow hKupq (by positivity : (0 : ℝ) ≤ 1 / q)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at this
    rwa [ENNReal.ofReal_rpow_of_nonneg hCup (by positivity)] at this
  have hMn : ∀ n ∈ Finset.Icc 1 N, ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
      eLpNorm (aux_hcut_M M H K rho0 Q N n) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (D * (1 / 2) ^ n) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hmono := HCut.aux_hcut_eLpNorm_mono_exp (chaosSampleLaw M).toMeasure
      (aux_hcut_measurable_M M hH K hKm rho0 Q N n).aestronglyMeasurable hq0 hqQ
    have hP := aux_hcut_M_eLpNorm hd M Rm hH rho0 hrho K hKm hK1 Q hQ1 hQd N n hn1 CH hCH Cb2 hCb2 hKb hsmall
    calc ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          eLpNorm (aux_hcut_M M H K rho0 Q N n) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) * ENNReal.ofReal (D * (3 / 2) ^ n) := by
          gcongr; exact hmono.trans hP
      _ = ENNReal.ofReal (D * (1 / 2) ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ((3 : ℝ) / 2) ^ n = 3 ^ n * (1 / 2) ^ n by rw [← mul_pow]; norm_num]
          field_simp
  have hsum : ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
      eLpNorm (aux_hcut_M M H K rho0 Q N n) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * D) := by
    refine (Finset.sum_le_sum hMn).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.mul_sum]
    have := aux_hcut_geom_sum_le (r := 1 / 2) (by norm_num) le_rfl N
    nlinarith
  calc 1 + ENNReal.ofReal C1 * eLpNorm Kup (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure +
        ENNReal.ofReal C2 * ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          eLpNorm (aux_hcut_M M H K rho0 Q N n) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure
      ≤ 1 + ENNReal.ofReal C1 * ENNReal.ofReal (Cup ^ (1 / q)) + ENNReal.ofReal C2 * ENNReal.ofReal (2 * D) := by
        gcongr
    _ = ENNReal.ofReal (1 + C1 * Cup ^ (1 / q) + C2 * (2 * D)) := by
        rw [← ENNReal.ofReal_mul hC1, ← ENNReal.ofReal_mul hC2, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **The almost-sure cutoff clause for `Kcut`.** -/
lemma aux_hcut_Kcut_clause (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H H0 : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (hH0 : InfraredCharacterization M H0) (alpha : ℝ) (K : ℕ → BilateralField d → ℝ)
    (hK1 : ∀ m om, 1 ≤ K m om)
    (hG0 : ∀ᵐ om' ∂(chaosSampleLaw M).toMeasure,
      aux_prop_growth_large_root_GrowthAt M H0 0 1 one_pos ((d : ℝ) - 1 / 2) alpha om'
        (fun m => K m om'))
    (rho0 : ℝ) (hrho : 1 ≤ rho0) (Q : ℝ) (hQ1 : 1 ≤ Q) (C0 : ℝ) (hC0 : 0 < C0)
    (hcube : ∀ a1 a2 : ℝ, 0 < a1 → a1 < a2 →
      ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
        (∀ x, ‖x‖ ≤ a1 → f x = 1) ∧ (∀ x, a2 ≤ ‖x‖ → f x = 0) ∧
        (∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (a2 - a1)) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (a2 - a1) ^ 2))
    (Kup : BilateralField d → ℝ) (hKup1 : ∀ om, 1 ≤ Kup om)
    (hKupae : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
        x ∈ Metric.ball (0 : SpatialCoordinates d) ((rho0 + 4) / 2) →
        volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
            (Metric.ball x r) ≤ ENNReal.ofReal (Kup om * r ^ ((d : ℝ) - 1 / 2)))
    (hsmall2 : 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ Real.log 3) (N : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ q1 q2 : ℚ, 0 < q1 → q1 < q2 → q2 ≤ 1 →
      ∃ chi : Homogenization.H10Function
          (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2), chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2) ∧
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          ∫⁻ z in Metric.ball x r ∩
              Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
            ENNReal.ofReal ((cutoffCoefficient M H om N z) *
              Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
            ENNReal.ofReal
              (aux_hcut_Kcut M H K Kup rho0 Q
                  (20 * d * C0 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * max 1 ((rho0 / 2) ^ 3))
                  (8 ^ d * 25 * C0 ^ 2 * (3 * rho0 / 2 + 15) * max 1 ((rho0 / 2) ^ 2)) N om *
                (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-5 : ℝ) * r ^ ((d : ℝ) - 1 / 2)) := by
  have hQ0 : 0 < Q := by linarith
  set C1 : ℝ := 20 * d * C0 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * max 1 ((rho0 / 2) ^ 3) with hC1
  set C2 : ℝ := 8 ^ d * 25 * C0 ^ 2 * (3 * rho0 / 2 + 15) * max 1 ((rho0 / 2) ^ 2) with hC2
  have hinv : 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ :=
    inv_nonneg.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0).le
  have hC10 : 0 ≤ C1 := by
    rw [hC1]
    exact mul_nonneg (mul_nonneg (by positivity) hinv) (le_trans zero_le_one (le_max_left _ _))
  have hrho0 : (0 : ℝ) ≤ rho0 := by linarith
  have hC20 : 0 ≤ C2 := by
    rw [hC2]
    exact mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _))
  filter_upwards [hKupae, aux_hcut_ae_cells hd M Rm hH hH0 alpha K hK1 hG0 N] with om hup hcells
  have hsumnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ((3 : ℝ) ^ n)⁻¹ * aux_hcut_M M H K rho0 Q N n om :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (aux_hcut_M_nonneg M Rm H K hK1 rho0 Q N n om)
  refine aux_hcut_clause (by omega) M H om N C0 hC0 hcube rho0 (Kup om)
    (aux_hcut_Kcut M H K Kup rho0 Q C1 C2 N om) (fun n => aux_hcut_M M H K rho0 Q N n om) hrho
    (le_trans zero_le_one (hKup1 om)) ?_ (aux_hcut_ahom_inv_le M N hsmall2)
    (fun n => aux_hcut_M_nonneg M Rm H K hK1 rho0 Q N n om) ?_ ?_ ?_
  · intro x r hr hr1 hx
    exact hup N x r hr hr1 (by rw [show (rho0 + 4) / 2 = rho0 / 2 + 2 by ring]; exact hx)
  · intro n hn1 hnN k hk f hf B1 B2 hB1 hB2 hr b u htr hs x rad hx h0 h1
    have hX := hcells n hn1 hnN k f hf B1 B2 hB1 hB2 hr b u htr hs x rad hx h0 h1
    refine hX.trans ?_
    have hXM : aux_hcut_X M H K N n k om ≤ aux_hcut_M M H K rho0 Q N n om :=
      aux_hcut_term_le_lpsum (aux_hcut_S (d := d) rho0 n) (fun j => aux_hcut_X M H K N n j om)
        (fun j => aux_hcut_X_nonneg M Rm H K hK1 N n j om) hQ0 (aux_hcut_mem_S hrho hk)
    have hr3 : 0 ≤ (((3 : ℝ) ^ n)⁻¹) ^ ((d : ℝ) - 2 - ((d : ℝ) - 1 / 2)) := Real.rpow_nonneg (by positivity) _
    have hrt : 0 ≤ rad ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg h0.le _
    have hsq : 0 ≤ (((3 : ℝ) ^ n)⁻¹ * B1 / 2 + ((3 : ℝ) ^ n)⁻¹ * B1 + (((3 : ℝ) ^ n)⁻¹) ^ 2 * B2) ^ 2 :=
      sq_nonneg _
    change aux_hcut_X M H K N n k om * _ * _ * _ ≤ _
    gcongr
  · -- `C1 Kup ≤ Kcut`
    unfold aux_hcut_Kcut
    have := mul_nonneg hC20 hsumnn
    linarith
  · intro n hn1 hnN
    unfold aux_hcut_Kcut
    have hmem : n ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨hn1, hnN⟩
    have hsingle := Finset.single_le_sum (f := fun n => ((3 : ℝ) ^ n)⁻¹ * aux_hcut_M M H K rho0 Q N n om)
      (fun j _ => mul_nonneg (by positivity) (aux_hcut_M_nonneg M Rm H K hK1 rho0 Q N j om)) hmem
    have h1 : C2 * (((3 : ℝ) ^ n)⁻¹ * aux_hcut_M M H K rho0 Q N n om) ≤
        C2 * ∑ n ∈ Finset.Icc 1 N, ((3 : ℝ) ^ n)⁻¹ * aux_hcut_M M H K rho0 Q N n om :=
      mul_le_mul_of_nonneg_left hsingle hC20
    have h2 : 0 ≤ C1 * Kup om := mul_nonneg hC10 (le_trans zero_le_one (hKup1 om))
    rw [← hC2]
    linarith

end Paper
end
end

-- ===== module HCut.Supplier3 =====
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hcut_small_facts (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Q : ℝ} (hQ1 : 1 ≤ Q)
    (hM : M.delta ≤ 1 / (8 * Q)) :
    Real.exp ((4 * Q) ^ 2 * M.delta ^ 2 / 4 + (4 * Q) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2 ∧
      2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ Real.log 3 := by
  have hδ := M.shellPrefix.delta_pos
  have hτ := M.G4.tauSq_pos
  have hτδ := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hQ0 : 0 < Q := by linarith
  have hδ2 : M.delta ^ 2 ≤ 1 / (64 * Q ^ 2) := by
    have h1 : M.delta ^ 2 ≤ (1 / (8 * Q)) ^ 2 := pow_le_pow_left₀ hδ.le hM 2
    calc M.delta ^ 2 ≤ (1 / (8 * Q)) ^ 2 := h1
      _ = 1 / (64 * Q ^ 2) := by field_simp; ring
  have hQ2 : 1 ≤ Q ^ 2 := by nlinarith
  have hδ2' : M.delta ^ 2 ≤ 1 / 64 := hδ2.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hτ' : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 0.35 * M.delta ^ 2 := by nlinarith
  constructor
  · rw [abs_of_pos hτ]
    have h1 : (4 * Q) ^ 2 * M.delta ^ 2 / 4 ≤ 1 / 16 := by
      have : (4 * Q) ^ 2 * M.delta ^ 2 / 4 = 4 * (Q ^ 2 * M.delta ^ 2) := by ring
      rw [this]
      have : Q ^ 2 * M.delta ^ 2 ≤ 1 / 64 := by
        calc Q ^ 2 * M.delta ^ 2 ≤ Q ^ 2 * (1 / (64 * Q ^ 2)) := by gcongr
          _ = 1 / 64 := by field_simp
      linarith
    have h2 : (4 * Q) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 1 / 16 := by
      have : (4 * Q) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 4 * Q * (0.35 * (1 / (64 * Q ^ 2))) := by
        gcongr; exact hτ'.trans (by gcongr)
      refine this.trans ?_
      have : 4 * Q * (0.35 * (1 / (64 * Q ^ 2))) = 0.35 / (16 * Q) := by field_simp; ring
      rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc Real.exp ((4 * Q) ^ 2 * M.delta ^ 2 / 4 + (4 * Q) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  · have h3 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    nlinarith

lemma aux_hcut_K_mod {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (K0 : ℕ → Ω → ℝ)
    (hK0 : ∀ m, AEStronglyMeasurable (K0 m) μ) (hK01 : ∀ᵐ ω ∂μ, ∀ m, 1 ≤ K0 m ω) :
    ∃ K1 : ℕ → Ω → ℝ, (∀ m, Measurable (K1 m)) ∧ (∀ m ω, 1 ≤ K1 m ω) ∧
      ∀ᵐ ω ∂μ, ∀ m, K1 m ω = K0 m ω := by
  refine ⟨fun m ω => max 1 ((hK0 m).mk (K0 m) ω), fun m => measurable_const.max
    (hK0 m).stronglyMeasurable_mk.measurable, fun m ω => le_max_left _ _, ?_⟩
  have hae : ∀ᵐ ω ∂μ, ∀ m, (hK0 m).mk (K0 m) ω = K0 m ω :=
    ae_all_iff.2 fun m => (hK0 m).ae_eq_mk.symm
  filter_upwards [hae, hK01] with ω h1 h2 m
  rw [h1 m, max_eq_right (h2 m)]

/-- **The cutoff supplier of `tight_static`** (clause 3 with `B = 5`), standalone with its own disorder
threshold.  `hupper` is `aux_tight_static_upper` (the upper mass supplier, in tight_static's file). -/
theorem tight_static_cut [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : Lane4.SobolevFoundationalInput d hd) (W : Lane4.SmallPerturbationInput d)
    (Cp : Lane4.CampanatoInput d)
    (hupper : ∀ q : ℝ, 1 ≤ q → ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ rho0 : ℝ, 1 ≤ rho0 → ∃ C : ℝ, 0 < C ∧
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∃ K : BilateralField d → ℝ, Measurable K ∧ (∀ om, 1 ≤ K om) ∧
        (∫⁻ om, ENNReal.ofReal (K om ^ q) ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
          ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
            x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
            volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
                (Metric.ball x r) ≤ ENNReal.ofReal (K om * r ^ ((d : ℝ) - 1 / 2)))
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 →
      ∀ rho0 : ℝ, 1 ≤ rho0 → ∃ Ccut : ℝ, 0 < Ccut ∧
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → ∀ N : ℕ,
      ∃ Kcut : BilateralField d → ℝ, Measurable Kcut ∧ (∀ omega, 1 ≤ Kcut omega) ∧
        (∫⁻ omega, ENNReal.ofReal (Kcut omega ^ q)
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal Ccut ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ q1 q2 : ℚ, 0 < q1 → q1 < q2 → q2 ≤ 1 →
            ∃ chi : Homogenization.H10Function
                (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
              (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
              (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2),
                chi.toFun x = 1) ∧
              tsupport chi.toFun ⊆
                Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2) ∧
            ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
                ∫⁻ z in Metric.ball x r ∩
                    Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
                  ENNReal.ofReal ((cutoffCoefficient M H omega N z) *
                    Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
                  ENNReal.ofReal
                    (Kcut omega * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-5 : ℝ) *
                      r ^ ((d : ℝ) - 1 / 2)) := by
  -- exponents
  set Q : ℝ := ((⌈max q (8 * ((d : ℝ) + 1))⌉₊ : ℕ) : ℝ) with hQdef
  have hQmax : max q (8 * ((d : ℝ) + 1)) ≤ Q := Nat.le_ceil _
  have hqQ : q ≤ Q := (le_max_left _ _).trans hQmax
  have hQd : 8 * ((d : ℝ) + 1) ≤ Q := (le_max_right _ _).trans hQmax
  have hQ1 : 1 ≤ Q := hq.trans hqQ
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨dpg, hdpg, hpg⟩ := prop_growth d hd Jc Pc Xc W Cp Sf ((d : ℝ) - 1 / 2) (1 / 2) 1
    (fun _ => 2 * Q) (by linarith) (by linarith) (by norm_num) (by norm_num) (fun _ => by linarith)
  obtain ⟨dup, hdup, hup⟩ := hupper q hq
  refine ⟨min dpg (min dup (1 / (8 * Q))), lt_min hdpg (lt_min hdup (by positivity)), ?_⟩
  intro M Rm Sreg It hM rho0 hrho
  have hMpg : M.delta ≤ dpg := hM.trans (min_le_left _ _)
  have hMup : M.delta ≤ dup := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMs : M.delta ≤ 1 / (8 * Q) := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hsmall, hsmall2⟩ := aux_hcut_small_facts M hQ1 hMs
  obtain ⟨Cup, hCup, hupM⟩ := hup M hMup (rho0 + 4) (by linarith)
  obtain ⟨H0, hH0⟩ := exists_infraredCharacterization hd M
  obtain ⟨K0, Cb, hK0mem, hK0bd, hK01, hK0G⟩ := hpg M Rm Sreg It H0 hH0 hMpg 0 1 one_pos le_rfl
  obtain ⟨K1, hK1m, hK11, hK1ae⟩ := aux_hcut_K_mod (μ := (chaosSampleLaw M).toMeasure) K0
    (fun m => (hK0mem 0 m).aestronglyMeasurable) hK01
  have hK1G : ∀ᵐ om' ∂(chaosSampleLaw M).toMeasure,
      aux_prop_growth_large_root_GrowthAt M H0 0 1 one_pos ((d : ℝ) - 1 / 2) (1 / 2) om'
        (fun m => K1 m om') := by
    filter_upwards [hK0G, hK1ae] with om' hg he
    have hfun : (fun m => K1 m om') = fun m => K0 m om' := funext he
    rw [hfun]
    exact hg
  set Cb2 : ℝ := (max (Cb 0) 0) ^ (2 * Q) with hCb2
  have hCb20 : 0 ≤ Cb2 := by rw [hCb2]; positivity
  have hKb : ∀ m, ∫⁻ om, ENNReal.ofReal (K1 m om ^ (2 * Q)) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cb2 := by
    intro m
    have h2Q : 0 < 2 * Q := by linarith
    rw [HCut.aux_hcut_lintegral_ofReal_rpow_eq _ (fun om => le_trans zero_le_one (hK11 m om)) h2Q]
    have heq : eLpNorm (K1 m) (ENNReal.ofReal (2 * Q)) (chaosSampleLaw M).toMeasure =
        eLpNorm (K0 m) (ENNReal.ofReal (2 * Q)) (chaosSampleLaw M).toMeasure :=
      eLpNorm_congr_ae (hK1ae.mono fun om h => h m)
    rw [heq, hCb2, ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) h2Q.le]
    refine ENNReal.rpow_le_rpow ((hK0bd 0 m).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) h2Q.le
  obtain ⟨CH, hCH0, hCHall⟩ := aux_hcut_exp_H_moment hd rho0
  obtain ⟨C0, hC0, hcube⟩ := HCut.aux_hcut_cube_cutoff d
  set C1 : ℝ := 20 * d * C0 ^ 2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * max 1 ((rho0 / 2) ^ 3) with hC1
  set C2 : ℝ := 8 ^ d * 25 * C0 ^ 2 * (3 * rho0 / 2 + 15) * max 1 ((rho0 / 2) ^ 2) with hC2
  have hinv : 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ :=
    inv_nonneg.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0).le
  have hC10 : 0 ≤ C1 := by
    rw [hC1]
    exact mul_nonneg (mul_nonneg (by positivity) hinv) (le_trans zero_le_one (le_max_left _ _))
  have hrho0 : (0 : ℝ) ≤ rho0 := by linarith
  have hC20 : 0 ≤ C2 := by
    rw [hC2]
    exact mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _))
  set C3 : ℝ := 1 + C1 * Cup ^ (1 / q) + C2 * (2 * ((2 * rho0 + 3) ^ d *
    (2 * (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ))) ^ (1 / Q)) with hC3
  have hC31 : 1 ≤ C3 := by
    rw [hC3]
    have h1 : 0 ≤ C1 * Cup ^ (1 / q) := mul_nonneg hC10 (Real.rpow_nonneg hCup.le _)
    have h2 : 0 ≤ C2 * (2 * ((2 * rho0 + 3) ^ d *
        (2 * (2 * Real.exp (CH * (4 * Q) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * Cb2 ^ (1 / 2 : ℝ))) ^ (1 / Q)) :=
      mul_nonneg hC20 (by positivity)
    linarith
  refine ⟨C3 ^ q, by positivity, ?_⟩
  intro H hH N
  obtain ⟨Kup, hKupm, hKup1, hKupq, hKupae⟩ := hupM H hH
  refine ⟨aux_hcut_Kcut M H K1 Kup rho0 Q C1 C2 N, ?_, ?_, ?_, ?_⟩
  · unfold aux_hcut_Kcut
    exact (measurable_const.add (measurable_const.mul hKupm)).add (measurable_const.mul
      (Finset.measurable_sum _ fun n _ => measurable_const.mul
        (aux_hcut_measurable_M M hH K1 hK1m rho0 Q N n)))
  · intro om
    unfold aux_hcut_Kcut
    have h1 : 0 ≤ C1 * Kup om := mul_nonneg hC10 (le_trans zero_le_one (hKup1 om))
    have h2 : 0 ≤ C2 * ∑ n ∈ Finset.Icc 1 N, ((3 : ℝ) ^ n)⁻¹ * aux_hcut_M M H K1 rho0 Q N n om :=
      mul_nonneg hC20 (Finset.sum_nonneg fun n _ => mul_nonneg (by positivity)
        (aux_hcut_M_nonneg M Rm H K1 hK11 rho0 Q N n om))
    linarith
  · exact aux_hcut_Kcut_moment hd M Rm hH rho0 hrho K1 hK1m hK11 q Q hq hqQ hQd CH
      (hCHall M H hH) Cb2 hCb20 hKb hsmall Kup hKupm hKup1 Cup hCup.le hKupq C1 C2 hC10 hC20 N
  · exact aux_hcut_Kcut_clause hd M Rm hH hH0 (1 / 2) K1 hK11 hK1G rho0 hrho Q hQ1 C0 hC0 hcube
      Kup hKup1 hKupae hsmall2 N

end Paper
end
end
