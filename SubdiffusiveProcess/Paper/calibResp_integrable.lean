import SubdiffusiveProcess.Paper.calibResp
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative
import SubdiffusiveProcess.Paper.cor_37
import SubdiffusiveProcess.Probability.FineDensityMean
import SubdiffusiveProcess.Lane1.ChaosBasic
import SubdiffusiveProcess.Main.FineDensity
import SubdiffusiveProcess.Sobolev.AffineResponses

/-! Infrared-free affine Dirichlet responses on the calibration cubes: measurability, sign, integrability
and the uniform `L¹` bound for `k ≥ K0` (from `cor_37`), hence tightness of the represented coordinates. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal
noncomputable section
namespace Paper

/-- The infrared-free coefficient is `ahom⁻¹` times the fine density. -/
theorem aux_calibResp_integrable_zero_coeff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (β : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) β N x =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * fineDensity M N β x := by
  simp [cutoffCoefficient, cutoffPotential, fineDensity, finePotential]

/-- The mass of a cube under the fine density is integrable in the chaos law. -/
theorem aux_calibResp_integrable_cube_mass {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Integrable (fun β : BilateralField d =>
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), fineDensity M N β x)
      (chaosSampleLaw M).toMeasure := by
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hjoint : StronglyMeasurable
      (fun p : BilateralField d × SpatialCoordinates d => fineDensity M N p.1 p.2) := by
    unfold fineDensity finePotential
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun p : BilateralField d × SpatialCoordinates d => fineDensity M N p.1 p.2)
      (P.prod (volume.restrict Q)) := hjoint.aestronglyMeasurable
  have hpoint : ∀ x : SpatialCoordinates d,
      Integrable (fun β : BilateralField d => fineDensity M N β x) P := by
    intro x
    exact integrable_of_integral_eq_one (integral_fineDensity_chaosSampleLaw M N x)
  have hQfin : volume Q ≠ ∞ := by
    dsimp [Q]
    rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hnorm : Integrable (fun x : SpatialCoordinates d =>
      ∫ β : BilateralField d, ‖fineDensity M N β x‖ ∂P) (volume.restrict Q) := by
    have heq : (fun x : SpatialCoordinates d =>
        ∫ β : BilateralField d, ‖fineDensity M N β x‖ ∂P) =ᵐ[volume.restrict Q]
        (fun _ => (1 : ℝ)) := by
      filter_upwards with x
      rw [← integral_fineDensity_chaosSampleLaw M N x]
      apply integral_congr_ae
      filter_upwards with β
      exact Real.norm_of_nonneg (Real.exp_pos _ |>.le)
    exact (integrableOn_const hQfin).congr heq.symm
  have hprod : Integrable (fun p : BilateralField d × SpatialCoordinates d =>
      fineDensity M N p.1 p.2) (P.prod (volume.restrict Q)) := by
    rw [integrable_prod_iff' hmeas]
    exact ⟨ae_of_all _ hpoint, hnorm⟩
  have hmass := hprod.integral_prod_left
  simpa [Q] using hmass

/-- The calibration response is measurable in the field. -/
theorem aux_calibResp_integrable_measurable (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k N : ℕ) :
    Measurable (calibResp d hd M k N) := by
  haveI : NeZero d := ⟨by omega⟩
  exact aux_thm_c1_envcal_response_measurable M N k _ _

/-- The calibration response is nonnegative. -/
theorem aux_calibResp_integrable_nonneg (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k N : ℕ) (β : BilateralField d) :
    0 ≤ calibResp d hd M k N β := by
  unfold calibResp
  exact dirichletResponse_nonneg _ _ _

/-- The elementary primal upper bound by the mass of the coefficient. -/
theorem aux_calibResp_integrable_le_mass (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k N : ℕ) (β : BilateralField d) :
    calibResp d hd M k N β ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
      ∫ x in (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d)),
        fineDensity M N β x := by
  haveI : NeZero d := ⟨by omega⟩
  unfold calibResp
  refine (affineDirichletResponse_le_affine_energy _ _ _ _).trans ?_
  have hsq := aux_thm_c1_envcal_e0_sq d (by omega : 0 < d)
  rw [← hsq, one_pow, one_mul]
  have hrep := (cutoffPositiveCoefficient_representative M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
    β N (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)).2.2.2
  rw [integral_congr_ae hrep]
  have : ∀ x, cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) β N x =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * fineDensity M N β x :=
    fun x => aux_calibResp_integrable_zero_coeff M β N x
  simp_rw [this]
  rw [integral_const_mul]

/-- The calibration response is integrable in the chaos law. -/
theorem calibResp_integrable (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k N : ℕ) :
    Integrable (calibResp d hd M k N) (chaosSampleLaw M).toMeasure := by
  refine Integrable.mono' ((aux_calibResp_integrable_cube_mass M N (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)).const_mul
      ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹)) (aux_calibResp_integrable_measurable d hd M k N).aestronglyMeasurable
    (Eventually.of_forall fun β => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (aux_calibResp_integrable_nonneg d hd M k N β)]
  exact aux_calibResp_integrable_le_mass d hd M k N β

end Paper
