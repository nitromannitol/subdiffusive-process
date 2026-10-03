module

public import SubdiffusiveProcess.Paper.lem_replace
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise
namespace Paper
noncomputable section
def aux_prop_conc_logpot {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) -
      ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) + H om +
    ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i))

theorem aux_prop_conc_logpot_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) :
    Measurable (aux_prop_conc_logpot model H N) :=
  (measurable_const.add hH).add
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i)))

theorem aux_prop_conc_log_eq {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    continuousPositiveLog (Lane4.cutoffCoefficientCM model H om N z hr)
        (Lane4.cutoffCoefficientCM_pos model H om N z hr) -
      ContinuousMap.const _ (Real.log 1) =
    (aux_prop_conc_logpot model H N om).restrict
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  rw [Real.log_one, ContinuousMap.const_zero, sub_zero]
  ext x
  show Real.log (cutoffCoefficient model H om N (x : SpatialCoordinates d)) =
    aux_prop_conc_logpot model H N om (x : SpatialCoordinates d)
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N).ne')
    (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  simp only [aux_prop_conc_logpot, cutoffPotential, ContinuousMap.add_apply,
    ContinuousMap.const_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  ring

/-- Measurability of the cutoff affine response in the field. -/
theorem aux_prop_conc_resp_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (pvec : Fin d → ℝ) :
    Measurable (fun om : BilateralField d => affineDirichletResponse
      (centeredCube_isBounded z hr) hP
      (Lane4.cutoffPositiveCoefficient model H om N z hr) pvec) := by
  haveI : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hD := ((continuous_dirichletResponse_compact (killedResponseSpace hP)
      (closedCube z r hr) (affineSobolev (centeredCube_isBounded z hr) pvec 0)).comp
    (ContinuousMap.continuous_restrict
      (closedCube z r hr : Set (SpatialCoordinates d)))).measurable.comp
    (aux_prop_conc_logpot_measurable model H hH N)
  convert hD using 1
  funext om
  simp only [Function.comp_apply]
  unfold affineDirichletResponse Lane4.cutoffPositiveCoefficient
    normalizedContinuousPositiveCoefficient
  rw [aux_prop_conc_log_eq]

theorem aux_prop_conc_cube_dilation {d : ℕ} (r : ℝ) (hr : 0 < r) :
    r • (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
  change r • Metric.ball (0 : SpatialCoordinates d) (1 / 2) = Metric.ball 0 (r / 2)
  rw [smul_ball hr.ne']
  simp [Real.norm_eq_abs, abs_of_pos hr, div_eq_mul_inv]

theorem aux_prop_conc_cube_translation {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    translateSet z (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  change dist (x - z) 0 < r / 2 ↔ dist x z < r / 2
  rw [dist_eq_norm, sub_zero, dist_eq_norm]

/-- Native and Hilbert-space affine minima coincide on the actual cube. -/
theorem aux_prop_conc_dirichlet_inf_eq_affine_response
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : SpatialCoordinates d → ℝ) (hb : Continuous b) (hbpos : ∀ x, 0 < b x)
    (hab : a.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] b)
    (p : SpatialCoordinates d) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn b
        (centeredCube z r hr : Set (SpatialCoordinates d)) p =
      affineDirichletResponse (centeredCube_isBounded z hr) hP a p := by
  let hdom := isOpenBoundedConvexDomain_ball z (half_pos hr)
  let hne : (centeredCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, Metric.mem_ball_self (half_pos hr)⟩
  let U : Book.Ch02.Domain d := ⟨(centeredCube z r hr : Set (SpatialCoordinates d)), hdom, hne⟩
  let data := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos hb hbpos U
  have hn := Lane4.symmetricDirichletNu_eq_affineDirichletResponse
    hdom hne data (centeredCube_isBounded z hr) hP a hab (centeredCube_volume_pos z hr) p
  have hi := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.symmetricDirichletNu_eq
    data (fun x => (hbpos x).le) p
  rw [hi] at hn
  have hv : 2 * volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) (centeredCube_volume_pos z hr))
  change (2 * volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ * _ = _ at hn
  rw [div_eq_inv_mul] at hn
  exact mul_left_cancel₀ (inv_ne_zero hv) hn

/-- Exact translation/dilation covariance for the continuum affine minimum. -/
theorem aux_prop_conc_dirichlet_inf_chart
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (b : SpatialCoordinates d → ℝ) (hbpos : ∀ x, 0 < b x)
    (p : SpatialCoordinates d) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn (fun x => b (z + r • x))
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) p =
      (r ^ d)⁻¹ * SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn b
        (centeredCube z r hr : Set (SpatialCoordinates d)) p := by
  have hs := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn_comp_smul
    (B := fun y => b (y + z)) (p := p) hr
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet
    (fun x => (hbpos (x + z)).le)
  rw [aux_prop_conc_cube_dilation r hr,
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn_comp_add_right z
      (centeredCube (0 : SpatialCoordinates d) r hr).isOpen.measurableSet
      (fun x => (hbpos x).le), aux_prop_conc_cube_translation z r hr] at hs
  simpa only [add_comm] using hs

/-- Pull back an actual coefficient representative to its unit-cube chart. -/
theorem aux_prop_conc_ae_cube_chart
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {P : SpatialCoordinates d → Prop}
    (hP : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), P x) :
    ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      P (z + r • x) := by
  have ht : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)), P (x + z) := by
    apply (measurePreserving_addRight_restrict_translateSet z _).quasiMeasurePreserving.ae
    simpa only [aux_prop_conc_cube_translation z r hr] using hP
  have hs : ∀ᵐ x ∂volume.restrict
      (r • (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      P (x + z) := by
    simpa only [aux_prop_conc_cube_dilation r hr] using ht
  have hdil : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      P (r • x + z) := by
    apply ae_of_ae_map (p := fun x => P (x + z)) (measurable_const_smul r).aemeasurable
    rw [map_smul_volume_restrict hr]
    exact Measure.ae_smul_measure hs _
  simpa only [add_comm] using hdil

/-- The standing coefficient chart's matrix is the literal volume-normalized
affine Dirichlet response on the physical cube. -/
theorem aux_prop_conc_chart_matrix_response
    {d : ℕ} (I : in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : SpatialCoordinates d → ℝ) (hb : Continuous b) (hbpos : ∀ x, 0 < b x)
    (hab : a.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] b)
    (p : SpatialCoordinates d) :
    p ⬝ᵥ (Book.Ch02.sigmaCoarse (Book.Ch02.cubeDomain (originCube d 0))
      ((I.chart z r hr a z r).coeffOn (originCube d 0))).mulVec p =
      affineDirichletResponse (centeredCube_isBounded z hr) hP a p /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  let U := Book.Ch02.cubeDomain (originCube d 0)
  let bc : SpatialCoordinates d → ℝ := fun x => b (z + r • x)
  have hbc : Continuous bc := hb.comp (continuous_const.add (continuous_const_smul r))
  have hbcp (x : SpatialCoordinates d) : 0 < bc x := hbpos _
  let data := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos hbc hbcp U
  have hu : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
      openCubeSet (originCube d 0) := by
    simpa only [zpow_zero] using Lane4.centeredCube_zero_eq_openCubeSet_originCube
      (d := d) 0 (by norm_num)
  have hdata : Book.Ch02.CoeffOn.AEEq
      ((I.chart z r hr a z r).coeffOn (originCube d 0)) data.toCoeffOn := by
    change _ =ᵐ[volume.restrict (openCubeSet (originCube d 0))] _
    rw [← hu]
    have hchart := I.chart_eq z r hr a z r hr subset_rfl (originCube d 0) subset_rfl
    rw [← hu] at hchart
    filter_upwards [hchart, aux_prop_conc_ae_cube_chart z r hr hab] with x hc hx
    change _ = scalarMatrix (bc x)
    rw [hc]
    exact congrArg scalarMatrix hx
  rw [Book.Ch02.sigmaCoarse_eq_ofAEEq hdata]
  have htheory := Book.Ch02.responseSymmetricDirichletNeumannTheory U data.toCoeffOn data.isSymmetric
  have hsigma := htheory.derived_matrices.1
  have hquad := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.vecDot_aMatrix_eq_dirichletInfOn
    data (fun x => (hbcp x).le) p
  change p ⬝ᵥ (Book.Ch02.aCoarse U data.toCoeffOn).mulVec p = _ at hquad
  rw [hsigma] at hquad
  rw [hquad]
  change (volume (openCubeSet (originCube d 0))).toReal⁻¹ *
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn bc
      (openCubeSet (originCube d 0)) p = _
  rw [← hu, ← Measure.real_def, centeredCube_volume_real, one_pow, inv_one, one_mul]
  rw [aux_prop_conc_dirichlet_inf_chart z r hr b hbpos p,
    aux_prop_conc_dirichlet_inf_eq_affine_response z r hr hP a b hb hbpos hab p,
    centeredCube_volume_real, div_eq_inv_mul]

/-- A bound on the actual inverse multiscale ellipticity controls every
affine slope. It uses the dual coarse matrix and its genuine matrix inverse. -/
theorem aux_prop_conc_coarse_affine_coercivity
    {d : ℕ} [NeZero d] (A : Book.Ch02.TriadicCoeffFamily d)
    (K : ℝ)
    (hK : Book.Ch02.coarseSigmaStarInvMatrixNorm (originCube d 0) A ≤ K)
    (p : SpatialCoordinates d) :
    p ⬝ᵥ p ≤ K * (p ⬝ᵥ (Book.Ch02.sigmaCoarse
      (Book.Ch02.cubeDomain (originCube d 0)) (A.coeffOn (originCube d 0))).mulVec p) := by
  let U := Book.Ch02.cubeDomain (originCube d 0)
  let a := A.coeffOn (originCube d 0)
  have hInv := Book.Ch02.sigmaStarInvCoarse_mul_sigmaStarCoarse
    (Book.Ch02.isUnit_det_sigmaStarInvCoarse U a)
  have hleft (x : SpatialCoordinates d) :
      matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
        (matVecMul (Book.Ch02.sigmaStarCoarse U a) x) = x := by
    change (Book.Ch02.sigmaStarInvCoarse U a).mulVec
      ((Book.Ch02.sigmaStarCoarse U a).mulVec x) = x
    rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  have hcoer := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    (Book.Ch02.sigmaStarInvCoarse_posDef U a).posSemidef hleft p
  have hpos : 0 ≤ p ⬝ᵥ (Book.Ch02.sigmaStarCoarse U a).mulVec p := by
    simpa only [star_trivial] using
      (Book.Ch02.sigmaStarCoarse_posDef U a).posSemidef.dotProduct_mulVec_nonneg p
  have hle : p ⬝ᵥ (Book.Ch02.sigmaStarCoarse U a).mulVec p ≤
      p ⬝ᵥ (Book.Ch02.sigmaCoarse U a).mulVec p := by
    have h := Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U a p
    change (1 / 2 : ℝ) * (p ⬝ᵥ (Book.Ch02.sigmaStarCoarse U a).mulVec p) ≤
      (1 / 2 : ℝ) * (p ⬝ᵥ (Book.Ch02.sigmaCoarse U a).mulVec p) at h
    linarith
  have hK0 : 0 ≤ K :=
    (Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg (originCube d 0) A).trans hK
  exact hcoer.trans ((mul_le_mul_of_nonneg_right hK hpos).trans
    (mul_le_mul_of_nonneg_left hle hK0))

/-- Root inverse matrix control for the literal normalized cutoff response. -/
theorem prop_conc_cutoff_affine_coercivity
    {d : ℕ} [NeZero d] (I : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (p : SpatialCoordinates d) :
    p ⬝ᵥ p ≤ Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (originCube d 0) 0
      (I.chart z r hr (Lane4.cutoffPositiveCoefficient M H ω N z hr) z r) *
      (affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient M H ω N z hr) p /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let A := I.chart z r hr (Lane4.cutoffPositiveCoefficient M H ω N z hr) z r
  have hK := Book.Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale
    (originCube d 0) (k := 0) (by simp [originCube]) A
  have h := aux_prop_conc_coarse_affine_coercivity A _ hK p
  rw [aux_prop_conc_chart_matrix_response I z r hr hP _ (cutoffCoefficient M H ω N)
    (Lane4.cutoffCoefficient_continuous M H ω N) (Lane4.cutoffCoefficient_pos M H ω N)
    (aux_lem_replace_large_cube_cutoff_positive_coe M H ω N z hr) p] at h
  exact h



end
end Paper

