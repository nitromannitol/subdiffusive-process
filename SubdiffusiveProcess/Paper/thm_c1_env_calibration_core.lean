import SubdiffusiveProcess.Paper.cor_37
import SubdiffusiveProcess.Paper.thm_c1_scalar
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Variational.DualEnergy
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Sobolev.CompactResponses
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic




set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

noncomputable section
namespace Paper

/-- The global zero-infrared log-potential of the normalized cutoff coefficient. -/
noncomputable def aux_thm_c1_envcal_logPotential {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
    ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
    ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i))

theorem aux_thm_c1_envcal_logPotential_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measurable (aux_thm_c1_envcal_logPotential M N) :=
  measurable_const.add
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i)))

theorem aux_thm_c1_envcal_rootLog_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ) (om : BilateralField d) :
    continuousPositiveLog
      (Lane4.cutoffCoefficientCM M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))
      (Lane4.cutoffCoefficientCM_pos M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) =
      (aux_thm_c1_envcal_logPotential M N om).restrict
        (closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d)) := by
  ext x
  simp only [continuousPositiveLog, aux_thm_c1_envcal_logPotential,
    Lane4.cutoffCoefficientCM, ContinuousMap.coe_mk]
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
    (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  simp only [cutoffPotential]
  dsimp [ContinuousMap.restrict]
  simp only [ContinuousMap.sum_apply]
  ring

/-- The cutoff coefficient on `Q_{3^k}` as an exponential of a compact potential. -/
noncomputable def aux_thm_c1_envcal_expCoeff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ) (om : BilateralField d) :
    PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) := by
  let Om := centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  let K := closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)⟩
  exact expPotentialCoefficient (compactPotentialToLp K
    ((aux_thm_c1_envcal_logPotential M N om).restrict (K : Set (SpatialCoordinates d))))

theorem aux_thm_c1_envcal_coeff_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ) (om : BilateralField d) :
    Lane4.cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) =
    aux_thm_c1_envcal_expCoeff M N k om := by
  let Om := centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  let K := closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)⟩
  unfold Lane4.cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
    aux_thm_c1_envcal_expCoeff
  rw [aux_thm_c1_envcal_rootLog_eq]
  simp only [Real.log_one, ContinuousMap.const_zero, sub_zero]

/-- The actual zero-infrared cutoff response on `Q_{3^k}` is measurable in the field. -/
theorem aux_thm_c1_envcal_response_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N k : ℕ)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
          ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))) w‖)
    (p : Fin d → ℝ) :
    Measurable (fun om : BilateralField d => affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) hP
      (Lane4.cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p) := by
  let Om := centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  let K := closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)⟩
  have hD := ((continuous_dirichletResponse_compact (killedResponseSpace hP) K
      (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p 0)).comp
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d)))).measurable.comp
      (aux_thm_c1_envcal_logPotential_measurable M N)
  convert hD using 1
  funext om
  rw [aux_thm_c1_envcal_coeff_eq M N k om]
  rfl

/-- Transfer of the calibration integral from the common-scale law to `P`. -/
theorem aux_thm_c1_envcal_transfer {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (hfield : Measurable field)
    (hmap : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (k N : ℕ)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
          ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))) w‖)
    (p : Fin d → ℝ) (L : Ω → ℝ) (v : ℝ)
    (hL : ∀ᵐ ω ∂P, L ω = affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) hP
        (Lane4.cutoffPositiveCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (field ω) N 0 (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p)
    (hv : v = (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal) :
    ∫ ω, |L ω / v - ∑ i : Fin d, p i ^ 2| ∂P =
      ∫ om, |affineDirichletResponse
          (centeredCube_isBounded (0 : SpatialCoordinates d)
            (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) hP
          (Lane4.cutoffPositiveCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
            om N 0 (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p /
          (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
            (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal -
          ∑ i : Fin d, p i ^ 2| ∂(chaosSampleLaw model).toMeasure := by
  subst hv
  have hg := continuous_abs.measurable.comp
    (((aux_thm_c1_envcal_response_measurable model N k hP p).div_const
      (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal).sub_const
      (∑ i : Fin d, p i ^ 2))
  rw [← hmap]
  symm
  refine (integral_map hfield.aemeasurable hg.aestronglyMeasurable).trans ?_
  refine integral_congr_ae ?_
  filter_upwards [hL] with ω hω
  simp only [Function.comp_apply]
  rw [hω]


/-- Fatou's lemma along a candidate subsequence: the limit inherits the uniform
`L¹` calibration bound and is integrable. -/
theorem aux_thm_c1_envcal_fatou {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (G : Ω → ℝ) (s eps : ℝ) (heps : 0 ≤ eps)
    (hint : ∀ n, Integrable (F n) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)))
    (hbound : ∀ n, ∫ ω, |F n ω - s| ∂P ≤ eps) :
    Integrable G P ∧ ∫ ω, |G ω - s| ∂P ≤ eps := by
  have hGm : AEStronglyMeasurable G P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hint n).aestronglyMeasurable) hconv
  have hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal |F n ω - s|) P := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable
        ((hint n).aestronglyMeasurable.aemeasurable.sub_const s))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal |F n ω - s|) atTop
      (𝓝 (ENNReal.ofReal |G ω - s|)) := by
    filter_upwards [hconv] with ω hω
    exact ENNReal.tendsto_ofReal ((hω.sub_const s).abs)
  have hn : ∀ n, ∫⁻ ω, ENNReal.ofReal |F n ω - s| ∂P ≤ ENNReal.ofReal eps := by
    intro n
    have hi : Integrable (fun ω => |F n ω - s|) P :=
      ((hint n).sub (integrable_const s)).abs
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hG : ∫⁻ ω, ENNReal.ofReal |G ω - s| ∂P ≤ ENNReal.ofReal eps := by
    calc ∫⁻ ω, ENNReal.ofReal |G ω - s| ∂P
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal |F n ω - s|) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with ω hω
          exact hω.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal |F n ω - s| ∂P) atTop :=
          lintegral_liminf_le' hmeas
      _ ≤ ENNReal.ofReal eps :=
          liminf_le_of_frequently_le' (Frequently.of_forall hn)
  have hGs : Integrable (fun ω => G ω - s) P := by
    refine ⟨hGm.sub aestronglyMeasurable_const, ?_⟩
    show ∫⁻ ω, ‖G ω - s‖ₑ ∂P < ⊤
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hG ENNReal.ofReal_lt_top
  refine ⟨(hGs.add (integrable_const s)).congr
    (Filter.Eventually.of_forall fun ω => by simp), ?_⟩
  have hGa : Integrable (fun ω => |G ω - s|) P := hGs.abs
  rw [← ofReal_integral_eq_lintegral_ofReal hGa
    (Filter.Eventually.of_forall fun ω => abs_nonneg _)] at hG
  exact (ENNReal.ofReal_le_ofReal_iff heps).1 hG

/-- The deviation of the normalized mean is at most the mean absolute deviation. -/
theorem aux_thm_c1_envcal_mean_dev {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (f : Ω → ℝ) (v s : ℝ) (hf : Integrable (fun ω => f ω / v) P) :
    |(∫ ω, f ω ∂P) / v - s| ≤ ∫ ω, |f ω / v - s| ∂P := by
  have h1 : (∫ ω, f ω ∂P) / v - s = ∫ ω, (f ω / v - s) ∂P := by
    rw [integral_sub hf (integrable_const s), integral_div]
    simp
  rw [h1]
  exact abs_integral_le_integral_abs

theorem aux_thm_c1_envcal_tendsto_zero (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (h : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → f k ≤ eps) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨k0, hk0⟩ := h (eps / 2) (half_pos heps)
  refine ⟨k0, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf k)]
  linarith [hk0 k hk]

/-- Passage of the finite calibration to a candidate subsequence (Fatou). -/
theorem aux_thm_c1_envcal_limit_calibration {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (LN : ℕ → ℕ → Ω → ℝ) (L : ℕ → Ω → ℝ) (vol : ℕ → ℝ) (s : ℝ) (NS : ℕ → ℕ)
    (hint : ∀ k N, Integrable (fun ω => LN k N ω / vol k) P)
    (hconv : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => LN k (NS n) ω) atTop (𝓝 (L k ω)))
    (hcal : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ N,
      ∫ ω, |LN k N ω / vol k - s| ∂P ≤ eps) :
    ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      Integrable (fun ω => L k ω / vol k) P ∧ ∫ ω, |L k ω / vol k - s| ∂P ≤ eps := by
  intro eps heps
  obtain ⟨k0, hk0⟩ := hcal eps heps
  refine ⟨k0, fun k hk => ?_⟩
  exact aux_thm_c1_envcal_fatou P (fun n ω => LN k (NS n) ω / vol k) (fun ω => L k ω / vol k)
    s eps heps.le (fun n => hint k (NS n))
    ((hconv k).mono fun ω hω => hω.div_const (vol k))
    (fun n => hk0 k hk (NS n))

/-- The normalized expected candidate responses converge to the calibration value. -/
theorem aux_thm_c1_envcal_expect_tendsto {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (L : ℕ → Ω → ℝ) (vol : ℕ → ℝ) (s : ℝ)
    (h : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      Integrable (fun ω => L k ω / vol k) P ∧ ∫ ω, |L k ω / vol k - s| ∂P ≤ eps) :
    Tendsto (fun k => |(∫ ω, L k ω ∂P) / vol k - s|) atTop (𝓝 0) := by
  refine aux_thm_c1_envcal_tendsto_zero _ (fun k => abs_nonneg _) fun eps heps => ?_
  obtain ⟨k0, hk0⟩ := h eps heps
  exact ⟨k0, fun k hk =>
    (aux_thm_c1_envcal_mean_dev P (L k) (vol k) s (hk0 k hk).1).trans (hk0 k hk).2⟩


open scoped Pointwise in
/-- Scalar response scaling (paper 3990--3991): if the candidate limit energies are
proportional with constant `c`, then so are the boundary minima of the
infrared-removed forms on every inner set. -/
theorem aux_thm_c1_envcal_sInf_scale {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E F E0 F0 : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GamE : DirichletForm.EnergyMeasure E) (GamF : DirichletForm.EnergyMeasure F)
    (GamE0 : DirichletForm.EnergyMeasure E0) (GamF0 : DirichletForm.EnergyMeasure F0)
    (rho : SpatialCoordinates d → ℝ)
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hwE : DirichletForm.IsWeightedForm E E0 GamE rho)
    (hwF : DirichletForm.IsWeightedForm F F0 GamF rho)
    (hE : ∀ u, E.energy u = limitFormEnergy GE u)
    (hF : ∀ u, F.energy u = limitFormEnergy GF u)
    (c : ℝ) (hc : 0 < c)
    (hprop : limitFormDomain GE = limitFormDomain GF ∧
      ∀ u : DomainL2 Q, u ∈ limitFormDomain GE →
        (limitFormEnergy GF u).toReal = c * (limitFormEnergy GE u).toReal)
    (hGS : F.domain = E.domain → (∀ u ∈ E.domain, F.form u u = c * E.form u u) →
      ∀ u ∈ E.domain, GamF.measure u = ENNReal.ofReal c • GamE.measure u)
    (hG0S : F0.domain = E0.domain → (∀ u ∈ E0.domain, F0.form u u = c * E0.form u u) →
      ∀ u ∈ E0.domain, GamF0.measure u = ENNReal.ofReal c • GamE0.measure u)
    (A : (SpatialCoordinates d → ℝ) → Prop)
    (B : DomainL2 Q → (SpatialCoordinates d → ℝ) → Prop)
    (C : (SpatialCoordinates d → ℝ) → Prop) (S : Set (SpatialCoordinates d)) :
    sInf {e : ℝ | ∃ U : DomainL2 Q, U ∈ F0.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamF0.measure U) S).toReal} =
      c * sInf {e : ℝ | ∃ U : DomainL2 Q, U ∈ E0.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamE0.measure U) S).toReal} := by
  have hdomE : (E.domain : Set (DomainL2 Q)) = limitFormDomain GE := by
    ext u
    change u ∈ E.domain ↔ limitFormEnergy GE u < ⊤
    rw [← hE u, DirichletForm.ClosedForm.energy_lt_top_iff]
  have hdomF : (F.domain : Set (DomainL2 Q)) = limitFormDomain GF := by
    ext u
    change u ∈ F.domain ↔ limitFormEnergy GF u < ⊤
    rw [← hF u, DirichletForm.ClosedForm.energy_lt_top_iff]
  have hFE : F.domain = E.domain :=
    SetLike.coe_injective (hdomF.trans (hprop.1.symm.trans hdomE.symm))
  have hform : ∀ u ∈ E.domain, F.form u u = c * E.form u u := by
    intro u hu
    have huF : u ∈ F.domain := by rw [hFE]; exact hu
    have huG : u ∈ limitFormDomain GE := by rw [← hdomE]; exact hu
    have h1 : (limitFormEnergy GF u).toReal = F.form u u := by
      rw [← hF u, DirichletForm.ClosedForm.energy_of_mem F huF, EReal.toReal_coe]
    have h2 : (limitFormEnergy GE u).toReal = E.form u u := by
      rw [← hE u, DirichletForm.ClosedForm.energy_of_mem E hu, EReal.toReal_coe]
    rw [← h1, ← h2]
    exact hprop.2 u huG
  have hGam := hGS hFE hform
  have hF0E0 : F0.domain = E0.domain :=
    hwF.domain_eq.trans (hFE.trans hwE.domain_eq.symm)
  have hform0 : ∀ u ∈ E0.domain, F0.form u u = c * E0.form u u := by
    intro u hu
    have huE : u ∈ E.domain := by rw [← hwE.domain_eq]; exact hu
    have huF : u ∈ F.domain := by rw [hFE]; exact huE
    rw [hwF.energy_eq u huF, hwE.energy_eq u huE, hGam u huE, integral_smul_measure,
      ENNReal.toReal_ofReal hc.le, smul_eq_mul]
  have hGam0 := hG0S hF0E0 hform0
  have hset : {e : ℝ | ∃ U : DomainL2 Q, U ∈ F0.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamF0.measure U) S).toReal} =
      c • {e : ℝ | ∃ U : DomainL2 Q, U ∈ E0.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamE0.measure U) S).toReal} := by
    ext e
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨U, hU, Uc, hA, hB, hC, rfl⟩
      have hU0 : U ∈ E0.domain := by rw [← hF0E0]; exact hU
      refine ⟨((GamE0.measure U) S).toReal, ⟨U, hU0, Uc, hA, hB, hC, rfl⟩, ?_⟩
      rw [hGam0 U hU0]
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hc.le]
    · rintro ⟨x, ⟨U, hU, Uc, hA, hB, hC, rfl⟩, rfl⟩
      have hUF : U ∈ F0.domain := by rw [hF0E0]; exact hU
      refine ⟨U, hUF, Uc, hA, hB, hC, ?_⟩
      rw [hGam0 U hU]
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hc.le]
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]


/-- The normalizer `vol k` is the volume of `Q_{3^k}`. -/
theorem aux_thm_c1_envcal_volQ {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (qidx : ℕ → ℕ)
    (hq : ∀ k, z (qidx k) = 0 ∧ r (qidx k) = (3 : ℝ) ^ k) (k : ℕ) :
    (volume (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
        Set (SpatialCoordinates d))).toReal =
      (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal := by
  have h1 := centeredCube_volume_real (z (qidx k)) (hr (qidx k))
  have h2 := centeredCube_volume_real (0 : SpatialCoordinates d)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  rw [measureReal_def] at h1 h2
  rw [h1, h2, (hq k).2]


/-- The first unit loading `e_0`. -/
noncomputable def aux_thm_c1_envcal_e0 (d : ℕ) (hd0 : 0 < d) : Fin d → ℝ :=
  fun j => if j = ⟨0, hd0⟩ then 1 else 0

theorem aux_thm_c1_envcal_e0_sq (d : ℕ) (hd0 : 0 < d) :
    (1 : ℝ) ^ 2 = ∑ j : Fin d, aux_thm_c1_envcal_e0 d hd0 j ^ 2 := by
  simp [aux_thm_c1_envcal_e0, apply_ite (fun x : ℝ => x ^ 2), Finset.sum_ite_eq']


theorem aux_thm_c1_envcal_vol_pos {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    0 < (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  have h := centeredCube_volume_pos z hr
  rwa [measureReal_def] at h

/-- The uniform moment input gives integrability of every normalized response. -/
theorem aux_thm_c1_envcal_int_of_moment {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (f : ℕ → Ω → ℝ)
    (h : ∃ q : ℝ≥0∞, 1 < q ∧ q ≠ ∞ ∧ ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ N,
      MemLp (f N) q P ∧ eLpNorm (f N) q P ≤ B) (N : ℕ) :
    Integrable (f N) P := by
  obtain ⟨q, hq1, -, B, -, hB⟩ := h
  exact (hB N).1.integrable hq1.le


/-- Almost-sure scalar response scaling of the boundary minima on the padded roots. -/
theorem aux_thm_c1_envcal_scale_ae {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Qc : ℕ → Opens (SpatialCoordinates d))
    (E F E0 F0 : (i : ℕ) → Ω →
      DirichletForm.ClosedForm (volume.restrict (Qc i : Set (SpatialCoordinates d))))
    (GamE : ∀ i ω, DirichletForm.EnergyMeasure (E i ω))
    (GamF : ∀ i ω, DirichletForm.EnergyMeasure (F i ω))
    (GamE0 : ∀ i ω, DirichletForm.EnergyMeasure (E0 i ω))
    (GamF0 : ∀ i ω, DirichletForm.EnergyMeasure (F0 i ω))
    (rho : ℕ → Ω → SpatialCoordinates d → ℝ)
    (GE GF : (i : ℕ) → Ω → DomainL2 (Qc i) →L[ℝ] DomainL2 (Qc i))
    (hwE : ∀ᵐ ω ∂P, ∀ i,
      DirichletForm.IsWeightedForm (E i ω) (E0 i ω) (GamE i ω) (rho i ω))
    (hwF : ∀ᵐ ω ∂P, ∀ i,
      DirichletForm.IsWeightedForm (F i ω) (F0 i ω) (GamF i ω) (rho i ω))
    (hE : ∀ᵐ ω ∂P, ∀ i u, (E i ω).energy u = limitFormEnergy (GE i ω) u)
    (hF : ∀ᵐ ω ∂P, ∀ i u, (F i ω).energy u = limitFormEnergy (GF i ω) u)
    (hGS : ∀ᵐ ω ∂P, ∀ i (c : ℝ), 0 < c →
      (F i ω).domain = (E i ω).domain →
      (∀ u ∈ (E i ω).domain, (F i ω).form u u = c * (E i ω).form u u) →
      ∀ u ∈ (E i ω).domain,
        (GamF i ω).measure u = ENNReal.ofReal c • (GamE i ω).measure u)
    (hG0S : ∀ᵐ ω ∂P, ∀ i (c : ℝ), 0 < c →
      (F0 i ω).domain = (E0 i ω).domain →
      (∀ u ∈ (E0 i ω).domain, (F0 i ω).form u u = c * (E0 i ω).form u u) →
      ∀ u ∈ (E0 i ω).domain,
        (GamF0 i ω).measure u = ENNReal.ofReal c • (GamE0 i ω).measure u)
    (c : ℝ) (hc : 0 < c)
    (hpc : ∀ᵐ ω ∂P, ∀ i : ℕ,
      limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
      ∀ u : DomainL2 (Qc i), u ∈ limitFormDomain (GE i ω) →
        (limitFormEnergy (GF i ω) u).toReal = c * (limitFormEnergy (GE i ω) u).toReal)
    (root : ℕ) (A : (SpatialCoordinates d → ℝ) → Prop)
    (B : DomainL2 (Qc root) → (SpatialCoordinates d → ℝ) → Prop)
    (C : (SpatialCoordinates d → ℝ) → Prop) (S : Set (SpatialCoordinates d))
    (LE LF : Ω → ℝ)
    (hLE : ∀ᵐ ω ∂P, LE ω = sInf {e : ℝ | ∃ U : DomainL2 (Qc root),
      U ∈ (E0 root ω).domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamE0 root ω).measure U S).toReal})
    (hLF : ∀ᵐ ω ∂P, LF ω = sInf {e : ℝ | ∃ U : DomainL2 (Qc root),
      U ∈ (F0 root ω).domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamF0 root ω).measure U S).toReal}) :
    ∀ᵐ ω ∂P, LF ω = c * LE ω := by
  filter_upwards [hpc, hwE, hwF, hE, hF, hGS, hG0S, hLE, hLF] with ω hpω hwEω hwFω hEω hFω
    hGSω hG0Sω hLEω hLFω
  rw [hLEω, hLFω]
  exact aux_thm_c1_envcal_sInf_scale (E root ω) (F root ω) (E0 root ω) (F0 root ω) (GamE root ω)
    (GamF root ω) (GamE0 root ω) (GamF0 root ω) (rho root ω) (GE root ω) (GF root ω)
    (hwEω root) (hwFω root) (hEω root) (hFω root) c hc (hpω root) (hGSω root c hc)
    (hG0Sω root c hc) A B C S


/-- `cor_37`, transferred to a family of cutoff-dependent environments, each of chaos law:
the uniform-in-`n` calibration of the represented boundary responses `L k n` at
`(env n ω, NN n)`.  Environment form of `aux_thm_c1_envcal_cal`; the only change is that the law
transfer is applied at `field := env n` (measure preserving) and the cutoff is `NN n`. -/
theorem aux_thm_c1_envcal_cal_env (d : ℕ) (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (env : ℕ → Ω → BilateralField d),
        (∀ n, MeasurePreserving (env n) P (chaosSampleLaw model).toMeasure) →
      ∀ (Poincare : ℕ → ℝ≥0)
        (hPoincare : ∀ k (u : killedSobolevGraph
            (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
              (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))),
          ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d)
              ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))).1‖ ≤
            Poincare k * ‖subspaceGradient
              (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
                ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))) u‖)
        (NN : ℕ → ℕ) (L : ℕ → ℕ → Ω → ℝ) (vol : ℕ → ℝ) (p : Fin d → ℝ),
        (∀ k, vol k = (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal) →
        (∀ᵐ omega ∂P, ∀ k n,
          L k n omega =
            affineDirichletResponse
              (centeredCube_isBounded (0 : SpatialCoordinates d)
                (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))
              ⟨Poincare k, hPoincare k⟩
              (Lane4.cutoffPositiveCoefficient model
                (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (env n omega) (NN n) 0
                (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p) →
        ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ n,
          ∫ ω, |L k n ω / vol k - ∑ j : Fin d, p j ^ 2| ∂P ≤ eps := by
  obtain ⟨dC, hdC, hcor⟩ := cor_37 d hd hJ
  refine ⟨dC, hdC, ?_⟩
  intro _ _ model hmodel Ω _ P env hmp Poincare hPoincare NN L vol p hvolQ hL eps heps
  obtain ⟨k0, hk0⟩ := hcor model hmodel (fun k => ⟨Poincare k, hPoincare k⟩) p eps heps
  refine ⟨k0, fun k hk n => ?_⟩
  exact (aux_thm_c1_envcal_transfer model P (env n) (hmp n).measurable (hmp n).map_eq k (NN n)
    ⟨Poincare k, hPoincare k⟩ p (fun ω => L k n ω) (vol k) (hL.mono fun ω h => h k n)
    (hvolQ k)).trans_le (hk0 k hk (NN n))

/-- The scalar core of the proof (paper 3985--3992) for two represented families `LNE`, `LNF`
indexed by the represented sequence index: the calibration passes to both candidate limits by
Fatou (along the whole index sequence), and proportional limits force `c = 1`.  Environment
form of `aux_thm_c1_envcal_core`: the two responses are DIFFERENT families and the calibration
bound is the uniform-in-`n` one for each. -/
theorem aux_thm_c1_envcal_core_env {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (LNE LNF : ℕ → ℕ → Ω → ℝ) (LE LF : ℕ → Ω → ℝ) (vol : ℕ → ℝ) (hvol : ∀ k, 0 < vol k)
    (s : ℝ) (hs : (1 : ℝ) ^ 2 = s)
    (hintE : ∀ k n, Integrable (fun ω => LNE k n ω / vol k) P)
    (hintF : ∀ k n, Integrable (fun ω => LNF k n ω / vol k) P)
    (hEconv : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => LNE k n ω) atTop (𝓝 (LE k ω)))
    (hFconv : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => LNF k n ω) atTop (𝓝 (LF k ω)))
    (hcalE : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ n,
      ∫ ω, |LNE k n ω / vol k - s| ∂P ≤ eps)
    (hcalF : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ n,
      ∫ ω, |LNF k n ω / vol k - s| ∂P ≤ eps)
    (c : ℝ) (hc : 0 < c) (hscale : ∀ k, ∀ᵐ ω ∂P, LF k ω = c * LE k ω) : c = 1 := by
  have hElim := aux_thm_c1_envcal_limit_calibration P LNE LE vol s (fun n => n) hintE hEconv hcalE
  have hFlim := aux_thm_c1_envcal_limit_calibration P LNF LF vol s (fun n => n) hintF hFconv hcalF
  refine thm_c1_scalar c hc 1 one_pos (fun k => ∫ ω, LE k ω ∂P) (fun k => ∫ ω, LF k ω ∂P)
    vol hvol ?_ ?_ ?_
  · intro k
    show ∫ ω, LF k ω ∂P = c * ∫ ω, LE k ω ∂P
    rw [integral_congr_ae (hscale k), integral_const_mul]
  · rw [hs]
    exact aux_thm_c1_envcal_expect_tendsto P LE vol s hElim
  · rw [hs]
    exact aux_thm_c1_envcal_expect_tendsto P LF vol s hFlim

/-- Environment form of the fixed-field boundary-response identification `hLamN0` of `thm_c1`:
the `n`-th term of the represented sequence is the affine Dirichlet response of the coefficient at
`(env n ω, N n)`.  Same content as the draft's `aux_thm_c1_env_lam` (definitionally equal). -/
def aux_thm_c1_env_scalar_lam (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (env : ℕ → Ω → BilateralField d) (N : ℕ → ℕ) (Poincare : ℕ → ℝ≥0)
    (hPoincare : ∀ k (u : killedSobolevGraph
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (by norm_num) k))),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d)
          ((3 : ℝ) ^ k) (pow_pos (by norm_num) k))).1‖ ≤
        Poincare k * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
            ((3 : ℝ) ^ k) (pow_pos (by norm_num) k))) u‖)
    (Lam : ℕ → ℕ → (Fin d → ℝ) → Ω → ℝ) : Prop :=
  ∀ᵐ omega ∂P, ∀ k n p,
    Lam k n p omega =
      affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d)
          (pow_pos (by norm_num) k))
        ⟨Poincare k, hPoincare k⟩
        (Lane4.cutoffPositiveCoefficient model
          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (env n omega) (N n) 0
          (pow_pos (by norm_num) k)) p

/-- **First conclusion of the environment-form `thm_c1`, law-explicit form.**  Every
proportionality constant `c` between the two represented candidate operators is `1`: the finite-cutoff
calibration `cor_37` transfers to the cutoff-dependent environments `envE n`, `envF n` (each of chaos
law), passes to the represented limits `LamE0`, `LamF0` by Fatou along the represented sequence
under the uniform moment bank, and the scalar computation `thm_c1_scalar` together with the response
scaling of the boundary minima (`F0 = c E0`) forces `c = 1`.  The proportionality `F = c E` is the
antecedent of this normalization lemma; obtaining it is the other half of uniqueness.
Nothing is assumed about `c`, the expectations, or the calibration estimate; the uniform moment
bank (`hmomentE`, `hmomentF`) and the represented convergence (`hLamEconv`, `hLamFconv`) are explicit. -/
theorem thm_c1_env_calibration_core
    (d : ℕ) (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (envE envF : ℕ → Ω → BilateralField d)
        (hmpE : ∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure)
        (hmpF : ∀ n, MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ) (qidx rootidx : ℕ → ℕ),
        (∀ k, z (qidx k) = 0 ∧ r (qidx k) = (3 : ℝ) ^ k) →
      (let vol : ℕ → ℝ := fun k =>
          (volume (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
            Set (SpatialCoordinates d))).toReal;
      ∀ (rho : ℕ → Ω → SpatialCoordinates d → ℝ)
        (Eform Fform E0form F0form :
          (i : ℕ) → Ω → _root_.DirichletForm
            (volume.restrict (centeredCube (z i) (r i) (hr i) :
              Set (SpatialCoordinates d))))
        (GammaE : ∀ i (omega : Ω),
          DirichletForm.EnergyMeasure (Eform i omega).toClosedForm)
        (GammaF : ∀ i (omega : Ω),
          DirichletForm.EnergyMeasure (Fform i omega).toClosedForm)
        (GammaE0 : ∀ i (omega : Ω),
          DirichletForm.EnergyMeasure (E0form i omega).toClosedForm)
        (GammaF0 : ∀ i (omega : Ω),
          DirichletForm.EnergyMeasure (F0form i omega).toClosedForm)
        (hweightE : ∀ᵐ omega ∂P, ∀ i,
          DirichletForm.IsWeightedForm
            (Eform i omega).toClosedForm (E0form i omega).toClosedForm
            (GammaE i omega) (rho i omega))
        (hweightF : ∀ᵐ omega ∂P, ∀ i,
          DirichletForm.IsWeightedForm
            (Fform i omega).toClosedForm (F0form i omega).toClosedForm
            (GammaF i omega) (rho i omega))
        (hGammaScale : ∀ᵐ omega ∂P, ∀ i (c : ℝ), 0 < c →
          (Fform i omega).toClosedForm.domain = (Eform i omega).toClosedForm.domain →
          (∀ u ∈ (Eform i omega).toClosedForm.domain,
            (Fform i omega).toClosedForm.form u u =
              c * (Eform i omega).toClosedForm.form u u) →
          ∀ u ∈ (Eform i omega).toClosedForm.domain,
            (GammaF i omega).measure u = ENNReal.ofReal c • (GammaE i omega).measure u)
        (hGamma0Scale : ∀ᵐ omega ∂P, ∀ i (c : ℝ), 0 < c →
          (F0form i omega).toClosedForm.domain = (E0form i omega).toClosedForm.domain →
          (∀ u ∈ (E0form i omega).toClosedForm.domain,
            (F0form i omega).toClosedForm.form u u =
              c * (E0form i omega).toClosedForm.form u u) →
          ∀ u ∈ (E0form i omega).toClosedForm.domain,
            (GammaF0 i omega).measure u = ENNReal.ofReal c • (GammaE0 i omega).measure u)
        (hEform : ∀ᵐ omega ∂P, ∀ i u,
          (Eform i omega).toClosedForm.energy u = limitFormEnergy (GE i omega) u)
        (hFform : ∀ᵐ omega ∂P, ∀ i u,
          (Fform i omega).toClosedForm.energy u = limitFormEnergy (GF i omega) u)
        (LamNE LamNF : ℕ → ℕ → (Fin d → ℝ) → Ω → ℝ)
        (LamE0 LamF0 : ℕ → (Fin d → ℝ) → Ω → ℝ)
        (Poincare : ℕ → ℝ≥0)
        (hPoincare : ∀ k (u : killedSobolevGraph
            (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
              (pow_pos (by norm_num) k))),
          ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d)
              ((3 : ℝ) ^ k) (pow_pos (by norm_num) k))).1‖ ≤
            Poincare k * ‖subspaceGradient
              (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
                ((3 : ℝ) ^ k) (pow_pos (by norm_num) k))) u‖)
        (hLamNE : aux_thm_c1_env_scalar_lam d model Ω P envE NE Poincare hPoincare LamNE)
        (hLamNF : aux_thm_c1_env_scalar_lam d model Ω P envF NF Poincare hPoincare LamNF)
        (hLamEconv : ∀ k p, ∀ᵐ omega ∂P,
          Tendsto (fun n => LamNE k n p omega) atTop
            (𝓝 (LamE0 k p omega)))
        (hLamFconv : ∀ k p, ∀ᵐ omega ∂P,
          Tendsto (fun n => LamNF k n p omega) atTop
            (𝓝 (LamF0 k p omega)))
        (hmomentE : ∀ k p, ∃ q : ℝ≥0∞, 1 < q ∧ q ≠ ∞ ∧
          ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n,
            MemLp (fun omega =>
              LamNE k n p omega / vol k) q P ∧
            eLpNorm (fun omega =>
              LamNE k n p omega / vol k) q P ≤ B)
        (hmomentF : ∀ k p, ∃ q : ℝ≥0∞, 1 < q ∧ q ≠ ∞ ∧
          ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n,
            MemLp (fun omega =>
              LamNF k n p omega / vol k) q P ∧
            eLpNorm (fun omega =>
              LamNF k n p omega / vol k) q P ≤ B)
        (hLamEboundary : ∀ k p, ∀ᵐ omega ∂P,
          LamE0 k p omega =
            sInf {e : ℝ | ∃ U : DomainL2
              (centeredCube (z (rootidx k)) (r (rootidx k)) (hr (rootidx k))),
              U ∈ (E0form (rootidx k) omega).toClosedForm.domain ∧
              ∃ Uc : SpatialCoordinates d → ℝ,
                ContinuousOn Uc
                    (closure (centeredCube (z (rootidx k)) (r (rootidx k))
                      (hr (rootidx k)) : Set (SpatialCoordinates d))) ∧
                (U : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube (z (rootidx k)) (r (rootidx k))
                    (hr (rootidx k)) : Set (SpatialCoordinates d))] Uc ∧
                (∀ x ∈ frontier (centeredCube (z (qidx k)) (r (qidx k))
                    (hr (qidx k)) : Set (SpatialCoordinates d)),
                  Uc x = ∑ j : Fin d, p j * x j) ∧
                e = ((GammaE0 (rootidx k) omega).measure U
                  (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
                    Set (SpatialCoordinates d))).toReal})
        (hLamFboundary : ∀ k p, ∀ᵐ omega ∂P,
          LamF0 k p omega =
            sInf {e : ℝ | ∃ U : DomainL2
              (centeredCube (z (rootidx k)) (r (rootidx k)) (hr (rootidx k))),
              U ∈ (F0form (rootidx k) omega).toClosedForm.domain ∧
              ∃ Uc : SpatialCoordinates d → ℝ,
                ContinuousOn Uc
                    (closure (centeredCube (z (rootidx k)) (r (rootidx k))
                      (hr (rootidx k)) : Set (SpatialCoordinates d))) ∧
                (U : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube (z (rootidx k)) (r (rootidx k))
                    (hr (rootidx k)) : Set (SpatialCoordinates d))] Uc ∧
                (∀ x ∈ frontier (centeredCube (z (qidx k)) (r (qidx k))
                    (hr (qidx k)) : Set (SpatialCoordinates d)),
                  Uc x = ∑ j : Fin d, p j * x j) ∧
                e = ((GammaF0 (rootidx k) omega).measure U
                  (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
                    Set (SpatialCoordinates d))).toReal}),
        ∀ c : ℝ, 0 < c →
          (∀ᵐ omega ∂P, ∀ i : ℕ,
            limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
              (limitFormEnergy (GF i omega) u).toReal =
                c * (limitFormEnergy (GE i omega) u).toReal) →
          c = 1) := by
  have hd0 : 0 < d := by omega
  have hCc := aux_thm_c1_envcal_cal_env d hd hJ
  refine ⟨hCc.choose, hCc.choose_spec.1, ?_⟩
  intro _ _ model hmodel Ω _ P _ envE envF hmpE hmpF z r hr GE GF NE NF qidx rootidx hq
    vol rho Eform Fform E0form F0form GammaE GammaF GammaE0 GammaF0 hweightE hweightF
    hGammaScale hGamma0Scale hEform hFform LamNE LamNF LamE0 LamF0 Poincare hPoincare hLamNE
    hLamNF hLamEconv hLamFconv hmomentE hmomentF hLamEboundary hLamFboundary c hc hpc
  have hvolQ : ∀ k, vol k = (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal :=
    aux_thm_c1_envcal_volQ z r hr qidx hq
  have hvol_pos : ∀ k, 0 < vol k := fun k =>
    aux_thm_c1_envcal_vol_pos (z (qidx k)) (r (qidx k)) (hr (qidx k))
  have hcalE := hCc.choose_spec.2 model hmodel Ω P envE hmpE Poincare hPoincare NE
    (fun k n ω => LamNE k n (aux_thm_c1_envcal_e0 d hd0) ω) vol (aux_thm_c1_envcal_e0 d hd0)
    hvolQ (hLamNE.mono fun ω h k n => h k n (aux_thm_c1_envcal_e0 d hd0))
  have hcalF := hCc.choose_spec.2 model hmodel Ω P envF hmpF Poincare hPoincare NF
    (fun k n ω => LamNF k n (aux_thm_c1_envcal_e0 d hd0) ω) vol (aux_thm_c1_envcal_e0 d hd0)
    hvolQ (hLamNF.mono fun ω h k n => h k n (aux_thm_c1_envcal_e0 d hd0))
  have hintE : ∀ k n, Integrable
      (fun ω => LamNE k n (aux_thm_c1_envcal_e0 d hd0) ω / vol k) P :=
    fun k n => aux_thm_c1_envcal_int_of_moment P
      (fun n ω => LamNE k n (aux_thm_c1_envcal_e0 d hd0) ω / vol k)
      (hmomentE k (aux_thm_c1_envcal_e0 d hd0)) n
  have hintF : ∀ k n, Integrable
      (fun ω => LamNF k n (aux_thm_c1_envcal_e0 d hd0) ω / vol k) P :=
    fun k n => aux_thm_c1_envcal_int_of_moment P
      (fun n ω => LamNF k n (aux_thm_c1_envcal_e0 d hd0) ω / vol k)
      (hmomentF k (aux_thm_c1_envcal_e0 d hd0)) n
  exact aux_thm_c1_envcal_core_env P
    (fun k n ω => LamNE k n (aux_thm_c1_envcal_e0 d hd0) ω)
    (fun k n ω => LamNF k n (aux_thm_c1_envcal_e0 d hd0) ω)
    (fun k ω => LamE0 k (aux_thm_c1_envcal_e0 d hd0) ω)
    (fun k ω => LamF0 k (aux_thm_c1_envcal_e0 d hd0) ω)
    vol hvol_pos _ (aux_thm_c1_envcal_e0_sq d hd0) hintE hintF
    (fun k => hLamEconv k (aux_thm_c1_envcal_e0 d hd0))
    (fun k => hLamFconv k (aux_thm_c1_envcal_e0 d hd0)) hcalE hcalF c hc
    (fun k =>
      aux_thm_c1_envcal_scale_ae P (fun i => centeredCube (z i) (r i) (hr i))
        (fun i ω => (Eform i ω).toClosedForm) (fun i ω => (Fform i ω).toClosedForm)
        (fun i ω => (E0form i ω).toClosedForm) (fun i ω => (F0form i ω).toClosedForm)
        GammaE GammaF GammaE0 GammaF0 rho GE GF hweightE hweightF hEform hFform
        hGammaScale hGamma0Scale c hc hpc (rootidx k) _ _ _ _
        (fun ω => LamE0 k (aux_thm_c1_envcal_e0 d hd0) ω)
        (fun ω => LamF0 k (aux_thm_c1_envcal_e0 d hd0) ω)
        (hLamEboundary k (aux_thm_c1_envcal_e0 d hd0))
        (hLamFboundary k (aux_thm_c1_envcal_e0 d hd0)))

end Paper
