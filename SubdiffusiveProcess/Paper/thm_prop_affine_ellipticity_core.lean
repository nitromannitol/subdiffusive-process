module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.FiniteStopping.CutoffRestrictions
public import SubdiffusiveProcess.Analysis.CoarseEllipticityFromMultiscale
public import SubdiffusiveProcess.Probability.SubseqInProbability
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Geometry.Translation
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Mathlib.Tactic

@[expose] public section



set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise

namespace SubdiffusiveProcess.Paper
noncomputable section


/-! ##  -/




theorem aux_thm_prop_affine_ellipticity_core_cube_dilation {d : ℕ} (r : ℝ) (hr : 0 < r) :
    r • (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
  change r • Metric.ball (0 : SpatialCoordinates d) (1 / 2) = Metric.ball 0 (r / 2)
  rw [smul_ball hr.ne']
  simp [Real.norm_eq_abs, abs_of_pos hr, div_eq_mul_inv]

theorem aux_thm_prop_affine_ellipticity_core_cube_translation {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    translateSet z (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  change dist (x - z) 0 < r / 2 ↔ dist x z < r / 2
  rw [dist_eq_norm, sub_zero, dist_eq_norm]

/-- Native and Hilbert-space affine minima coincide on the actual cube. -/
theorem aux_thm_prop_affine_ellipticity_core_dirichlet_inf_eq_affine_response
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
  have hn := _root_.SubdiffusiveProcess.EllipticRegularity.symmetricDirichletNu_eq_affineDirichletResponse
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
theorem aux_thm_prop_affine_ellipticity_core_dirichlet_inf_chart
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
  rw [aux_thm_prop_affine_ellipticity_core_cube_dilation r hr,
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn_comp_add_right z
      (centeredCube (0 : SpatialCoordinates d) r hr).isOpen.measurableSet
      (fun x => (hbpos x).le), aux_thm_prop_affine_ellipticity_core_cube_translation z r hr] at hs
  simpa only [add_comm] using hs

/-- Pull back an actual coefficient representative to its unit-cube chart. -/
theorem aux_thm_prop_affine_ellipticity_core_ae_cube_chart
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {P : SpatialCoordinates d → Prop}
    (hP : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), P x) :
    ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      P (z + r • x) := by
  have ht : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)), P (x + z) := by
    apply (measurePreserving_addRight_restrict_translateSet z _).quasiMeasurePreserving.ae
    simpa only [aux_thm_prop_affine_ellipticity_core_cube_translation z r hr] using hP
  have hs : ∀ᵐ x ∂volume.restrict
      (r • (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      P (x + z) := by
    simpa only [aux_thm_prop_affine_ellipticity_core_cube_dilation r hr] using ht
  have hdil : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      P (r • x + z) := by
    apply ae_of_ae_map (p := fun x => P (x + z)) (measurable_const_smul r).aemeasurable
    rw [map_smul_volume_restrict hr]
    exact Measure.ae_smul_measure hs _
  simpa only [add_comm] using hdil

/-- The standing coefficient chart's matrix is the literal volume-normalized
affine Dirichlet response on the physical cube. -/
theorem aux_thm_prop_affine_ellipticity_core_chart_matrix_response
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
    simpa only [zpow_zero] using _root_.SubdiffusiveProcess.EllipticRegularity.centeredCube_zero_eq_openCubeSet_originCube
      (d := d) 0 (by norm_num)
  have hdata : Book.Ch02.CoeffOn.AEEq
      ((I.chart z r hr a z r).coeffOn (originCube d 0)) data.toCoeffOn := by
    change _ =ᵐ[volume.restrict (openCubeSet (originCube d 0))] _
    rw [← hu]
    have hchart := I.chart_eq z r hr a z r hr subset_rfl (originCube d 0) subset_rfl
    rw [← hu] at hchart
    filter_upwards [hchart, aux_thm_prop_affine_ellipticity_core_ae_cube_chart z r hr hab] with x hc hx
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
  rw [aux_thm_prop_affine_ellipticity_core_dirichlet_inf_chart z r hr b hbpos p,
    aux_thm_prop_affine_ellipticity_core_dirichlet_inf_eq_affine_response z r hr hP a b hb hbpos hab p,
    centeredCube_volume_real, div_eq_inv_mul]


/-! ### 2. Pure analysis -/


theorem aux_thm_prop_affine_ellipticity_core_dot_nonneg {d : ℕ} (p : Fin d → ℝ) :
    0 ≤ p ⬝ᵥ p := by
  unfold dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)

theorem aux_thm_prop_affine_ellipticity_core_trace_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace A = ∑ i : Fin d, (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ
      A.mulVec (Pi.single i (1 : ℝ)) := by
  simp only [Matrix.trace, Matrix.diag, single_dotProduct, Matrix.mulVec_single_one, one_mul]
  simp

/-- Layer B (pure analysis).  Finite-cutoff quadratic-form bounds `lam n |p|^2 <= R n p` and
`sum_i R n e_i <= d Lam n`, convergence of the responses `R n p -> p.A p`, and convergence of the
normalized ratios `lam n / s n -> loL >= cell`, `Lam n / s n -> hiL <= cell^-1` give the limiting
ellipticity `cell^2/d tr A |p|^2 <= p.A p`. -/
theorem aux_thm_prop_affine_ellipticity_core_limit
    {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ) (cell : ℝ) (hcell : 0 < cell)
    (R : ℕ → (Fin d → ℝ) → ℝ) (lam Lam s : ℕ → ℝ)
    (hlam : ∀ n, 0 < lam n) (hLam : ∀ n, 0 < Lam n)
    (h1 : ∀ n p, lam n * (p ⬝ᵥ p) ≤ R n p)
    (h2 : ∀ n, ∑ i : Fin d, R n (Pi.single i (1 : ℝ)) ≤ (d : ℝ) * Lam n)
    (hR : ∀ p, Tendsto (fun n => R n p) atTop (𝓝 (p ⬝ᵥ A.mulVec p)))
    {loL hiL : ℝ} (hlo : Tendsto (fun n => lam n / s n) atTop (𝓝 loL))
    (hhi : Tendsto (fun n => Lam n / s n) atTop (𝓝 hiL))
    (hloL : cell ≤ loL) (hhiL : hiL ≤ cell⁻¹) :
    ∀ p : Fin d → ℝ, cell ^ 2 / (d : ℝ) * Matrix.trace A * (p ⬝ᵥ p) ≤ p ⬝ᵥ A.mulVec p := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- the responses are nonnegative, hence so are the limits
  have hRnn : ∀ n p, 0 ≤ R n p := fun n p =>
    (mul_nonneg (hlam n).le (aux_thm_prop_affine_ellipticity_core_dot_nonneg p)).trans (h1 n p)
  have hAnn : ∀ p : Fin d → ℝ, 0 ≤ p ⬝ᵥ A.mulVec p := fun p =>
    ge_of_tendsto' (hR p) (fun n => hRnn n p)
  have htrnn : 0 ≤ Matrix.trace A := by
    rw [aux_thm_prop_affine_ellipticity_core_trace_eq]
    exact Finset.sum_nonneg fun i _ => hAnn _
  -- eventually the normalization is positive
  have hpos : ∀ᶠ n in atTop, 0 < lam n / s n :=
    hlo.eventually (lt_mem_nhds (lt_of_lt_of_le hcell hloL))
  have hspos : ∀ᶠ n in atTop, 0 < s n := by
    filter_upwards [hpos] with n hn
    rcases div_pos_iff.mp hn with h | h
    · exact h.2
    · exact absurd h.1 (not_lt.mpr (hlam n).le)
  -- traces of the finite responses
  have htr : Tendsto (fun n => ∑ i : Fin d, R n (Pi.single i (1 : ℝ))) atTop
      (𝓝 (Matrix.trace A)) := by
    rw [aux_thm_prop_affine_ellipticity_core_trace_eq]
    exact tendsto_finsetSum _ fun i _ => hR _
  intro p
  have hev : ∀ᶠ n in atTop,
      lam n / s n * (∑ i : Fin d, R n (Pi.single i (1 : ℝ))) * (p ⬝ᵥ p) ≤
        (d : ℝ) * (Lam n / s n) * R n p := by
    filter_upwards [hspos] with n hsn
    have hpp := aux_thm_prop_affine_ellipticity_core_dot_nonneg p
    have step : lam n * (∑ i : Fin d, R n (Pi.single i (1 : ℝ))) * (p ⬝ᵥ p) ≤
        (d : ℝ) * Lam n * R n p := by
      calc lam n * (∑ i : Fin d, R n (Pi.single i (1 : ℝ))) * (p ⬝ᵥ p)
          = (lam n * (p ⬝ᵥ p)) * (∑ i : Fin d, R n (Pi.single i (1 : ℝ))) := by ring
        _ ≤ (lam n * (p ⬝ᵥ p)) * ((d : ℝ) * Lam n) :=
            mul_le_mul_of_nonneg_left (h2 n) (mul_nonneg (hlam n).le hpp)
        _ = (d : ℝ) * Lam n * (lam n * (p ⬝ᵥ p)) := by ring
        _ ≤ (d : ℝ) * Lam n * R n p :=
            mul_le_mul_of_nonneg_left (h1 n p) (mul_nonneg hdR.le (hLam n).le)
    have := div_le_div_of_nonneg_right step hsn.le
    calc lam n / s n * (∑ i : Fin d, R n (Pi.single i (1 : ℝ))) * (p ⬝ᵥ p)
        = lam n * (∑ i : Fin d, R n (Pi.single i (1 : ℝ))) * (p ⬝ᵥ p) / s n := by ring
      _ ≤ (d : ℝ) * Lam n * R n p / s n := this
      _ = (d : ℝ) * (Lam n / s n) * R n p := by ring
  have hL : Tendsto (fun n => lam n / s n * (∑ i : Fin d, R n (Pi.single i (1 : ℝ))) * (p ⬝ᵥ p))
      atTop (𝓝 (loL * Matrix.trace A * (p ⬝ᵥ p))) :=
    (hlo.mul htr).mul_const _
  have hRt : Tendsto (fun n => (d : ℝ) * (Lam n / s n) * R n p) atTop
      (𝓝 ((d : ℝ) * hiL * (p ⬝ᵥ A.mulVec p))) :=
    ((hhi.const_mul (d : ℝ))).mul (hR p)
  have hlim : loL * Matrix.trace A * (p ⬝ᵥ p) ≤ (d : ℝ) * hiL * (p ⬝ᵥ A.mulVec p) :=
    le_of_tendsto_of_tendsto hL hRt hev
  have hpp := aux_thm_prop_affine_ellipticity_core_dot_nonneg p
  have hAp := hAnn p
  have hstep1 : cell * Matrix.trace A * (p ⬝ᵥ p) ≤ loL * Matrix.trace A * (p ⬝ᵥ p) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hloL htrnn) hpp
  have hstep2 : (d : ℝ) * hiL * (p ⬝ᵥ A.mulVec p) ≤ (d : ℝ) * cell⁻¹ * (p ⬝ᵥ A.mulVec p) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhiL hdR.le) hAp
  have hmain : cell * Matrix.trace A * (p ⬝ᵥ p) ≤ (d : ℝ) * cell⁻¹ * (p ⬝ᵥ A.mulVec p) :=
    hstep1.trans (hlim.trans hstep2)
  have hcd : 0 < cell / (d : ℝ) := div_pos hcell hdR
  have := mul_le_mul_of_nonneg_left hmain hcd.le
  calc cell ^ 2 / (d : ℝ) * Matrix.trace A * (p ⬝ᵥ p)
      = cell / (d : ℝ) * (cell * Matrix.trace A * (p ⬝ᵥ p)) := by ring
    _ ≤ cell / (d : ℝ) * ((d : ℝ) * cell⁻¹ * (p ⬝ᵥ A.mulVec p)) := this
    _ = p ⬝ᵥ A.mulVec p := by field_simp


/-! ### 3. Finite cutoff and the deterministic principal theorem -/


/-- The rescaled chart of an actual positive coefficient is a.e. a scalar matrix, hence symmetric. -/
theorem aux_thm_prop_affine_ellipticity_core_chart_symmetric
    {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) :
    Book.Ch02.CoeffOn.IsSymmetric ((I.chart z r hr a z r).coeffOn (originCube d 0)) := by
  have hchart := I.chart_eq z r hr a z r hr subset_rfl (originCube d 0) subset_rfl
  unfold Book.Ch02.CoeffOn.IsSymmetric
  filter_upwards [hchart] with x hx
  rw [hx]
  exact scalarMatrix_isSymm _

/-- Layer A (one finite cutoff).  For an actual positive coefficient with a continuous positive
representative, the multiscale lower/upper ellipticities `λ_{s,2}`, `Λ_{s,2}` of the rescaled chart
control the volume-normalized affine Dirichlet responses `R p`:
`λ |p|² ≤ R p` and `∑_i R e_i ≤ d Λ`. -/
theorem aux_thm_prop_affine_ellipticity_core_finite
    {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : SpatialCoordinates d → ℝ) (hb : Continuous b) (hbpos : ∀ x, 0 < b x)
    (hab : a.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] b)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    (∀ p : Fin d → ℝ, I.lam z r hr a z r s 2 * (p ⬝ᵥ p) ≤
      affineDirichletResponse (centeredCube_isBounded z hr) hP a p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ∧
    ∑ i : Fin d, affineDirichletResponse (centeredCube_isBounded z hr) hP a
        (Pi.single i (1 : ℝ)) /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      (d : ℝ) * I.Lam z r hr a z r s 2 := by
  have hlam := I.lam_eq z r hr a z r hr subset_rfl s hs 2 (by norm_num)
  have hLam := I.Lam_eq z r hr a z r hr subset_rfl s hs 2 (by norm_num)
  simp only [ENNReal.ofNat_ne_top, ↓reduceIte, ENNReal.toReal_ofNat] at hlam hLam
  have hsym := aux_thm_prop_affine_ellipticity_core_chart_symmetric I z r hr a
  have hresp := aux_thm_prop_affine_ellipticity_core_chart_matrix_response I z r hr hP a b hb hbpos hab
  have hlam' : I.lam z r hr a z r s 2 =
      Book.Ch02.lambdaSqFinite (originCube d 0) s 2 (I.chart z r hr a z r) := hlam
  have hLam' : I.Lam z r hr a z r s 2 =
      Book.Ch02.LambdaSqFinite (originCube d 0) s 2 (I.chart z r hr a z r) := hLam
  constructor
  · intro p
    have h := aux_sigmaCoarse_trace_lam_mul_normSq_le_quad (originCube d 0) (I.chart z r hr a z r)
      s 2 hs.1 (by norm_num) p
    rw [hlam']
    have := hresp p
    rw [← Measure.real_def] at *
    rw [← this]
    exact h
  · have h := aux_sigmaCoarse_trace_trace_le_dim_mul_Lambda (originCube d 0)
      (I.chart z r hr a z r) hsym s 2 hs.1 (by norm_num)
    rw [hLam']
    refine le_trans (le_of_eq ?_) h
    simp only [Matrix.trace, Matrix.diag]
    apply Finset.sum_congr rfl
    intro i _
    have := hresp (Pi.single i 1)
    rw [Measure.real_def] at this
    rw [← this]
    simp [single_dotProduct]




theorem thm_prop_affine_ellipticity_core
    {d : ℕ} (hd : 0 < d) (I : _root_.SubdiffusiveProcess.Paper.in_J d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ → ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ p : Fin d → ℝ, Tendsto (fun n =>
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      atTop (𝓝 (p ⬝ᵥ A.mulVec p)))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (s : ℕ → ℝ)
    (cell loL hiL : ℝ) (hcell : 0 < cell)
    (hlo : Tendsto (fun n => I.lam z r hr
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) z r sigma 2 / s n)
      atTop (𝓝 loL))
    (hhi : Tendsto (fun n => I.Lam z r hr
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) z r sigma 2 / s n)
      atTop (𝓝 hiL))
    (hloL : cell ≤ loL) (hhiL : hiL ≤ cell⁻¹) :
    ∀ p : Fin d → ℝ, cell ^ 2 / (d : ℝ) * Matrix.trace A * (p ⬝ᵥ p) ≤ p ⬝ᵥ A.mulVec p := by
  let : NeZero d := ⟨hd.ne'⟩
  have hfin := fun n => aux_thm_prop_affine_ellipticity_core_finite I z r hr hP
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr)
    (cutoffCoefficient model H om (N n))
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous model H om (N n))
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos model H om (N n))
    (FiniteStopping.cutoffCoefficient_ae model H om (N n) z hr) sigma hsigma
  exact aux_thm_prop_affine_ellipticity_core_limit hd A cell hcell
    (fun n p => affineDirichletResponse (centeredCube_isBounded z hr) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) p /
      (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
    (fun n => I.lam z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) z r sigma 2)
    (fun n => I.Lam z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) z r sigma 2)
    s (fun n => I.lam_pos z r hr _ z r sigma 2) (fun n => I.Lam_pos z r hr _ z r sigma 2)
    (fun n p => (hfin n).1 p) (fun n => (hfin n).2) hA hlo hhi hloL hhiL

/-! ### 4. Almost-sure transfer along a common subsequence -/

/-- Layer C (one catalogue cube, almost surely).  The lower and upper ellipticity arrays of the
actual good-cell catalogue, converging in measure along `psi`, together with the a.e. convergence of
the volume-normalized affine responses along `NE` (`prepared.converges`), give the limiting
ellipticity of the limiting matrix `A` wherever the good-cell bounds `cell ≤ loLim`, `hiLim ≤ cell⁻¹`
hold.  The identification of the coarse matrix with `A` is `aux_thm_prop_affine_ellipticity_core_chart_matrix_response`
applied to every finite cutoff. -/
theorem aux_thm_prop_affine_ellipticity_core_cell_ae
    {d : ℕ} (hd : 0 < d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (hmeas : Measurable field) (hmap : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (zj : SpatialCoordinates d) (rj : ℝ) (hrj : 0 < rj)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zj rj hrj),
      ‖(u : SobolevData (centeredCube zj rj hrj)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zj rj hrj)) u‖)
    (NE : ℕ → ℕ) (psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hconv : ∀ᵐ om ∂P,
      ∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded zj hrj) hP
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field om) (NE n) zj hrj) p /
          (volume (centeredCube zj rj hrj : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (A om).mulVec p)))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (cell : ℝ) (hcell : 0 < cell)
    (z1 : SpatialCoordinates d) (r1 : ℝ) (h1 : 0 < r1) (hz : z1 = zj) (hr : r1 = rj)
    (sN : ℕ → BilateralField d → ℝ) (loLim hiLim : BilateralField d → ℝ)
    (hlo : TendstoInMeasure (chaosSampleLaw model).toMeasure
      (fun n x => I.lam z1 r1 h1
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x (NE (psi n)) z1 h1) z1 r1 sigma 2 / sN n x)
      atTop loLim)
    (hhi : TendstoInMeasure (chaosSampleLaw model).toMeasure
      (fun n x => I.Lam z1 r1 h1
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x (NE (psi n)) z1 h1) z1 r1 sigma 2 / sN n x)
      atTop hiLim) :
    ∀ᵐ om ∂P, cell ≤ loLim (field om) → hiLim (field om) ≤ cell⁻¹ →
      ∀ p : Fin d → ℝ, cell ^ 2 / (d : ℝ) * Matrix.trace (A om) * (p ⬝ᵥ p) ≤
        p ⬝ᵥ (A om).mulVec p := by
  subst hz
  subst hr
  classical
  let : NeZero d := ⟨hd.ne'⟩
  set μ : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure with hμ
  let lo : ℕ → BilateralField d → ℝ := fun n x => I.lam z1 r1 h1
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x (NE (psi n)) z1 h1) z1 r1 sigma 2 / sN n x
  let hi : ℕ → BilateralField d → ℝ := fun n x => I.Lam z1 r1 h1
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x (NE (psi n)) z1 h1) z1 r1 sigma 2 / sN n x
  -- a common almost-everywhere subsequence for the two arrays
  let X : ℕ → ℕ → BilateralField d → ℝ := fun k n x =>
    if k = 0 then lo n x - loLim x else if k = 1 then hi n x - hiLim x else 0
  have hX : ∀ k : ℕ, ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N => μ {ω | eps ≤ |X k N ω|}) atTop (𝓝 0) := by
    intro k eps heps
    by_cases hk0 : k = 0
    · subst hk0
      have := tendstoInMeasure_iff_norm.1 hlo eps heps
      simpa only [X, ite_true, Real.norm_eq_abs] using this
    · by_cases hk1 : k = 1
      · subst hk1
        have := tendstoInMeasure_iff_norm.1 hhi eps heps
        simpa only [X, hk0, ite_false, ite_true, Real.norm_eq_abs] using this
      · have hempty : ∀ N, {ω : BilateralField d | eps ≤ |X k N ω|} = ∅ := by
          intro N
          ext ω
          simp only [X, hk0, hk1, ite_false, abs_zero, mem_ofPred_eq, Set.mem_empty_iff_false,
            iff_false, not_le]
          exact heps
        simp [hempty]
  obtain ⟨ψ2, hψ2, hae⟩ := exists_strictMono_ae_forall_tendsto_zero μ X hX id tendsto_id
  have hfmp : MeasurePreserving field P μ := ⟨hmeas, hmap⟩
  have haeP := hfmp.quasiMeasurePreserving.ae hae
  have hidx : Tendsto (fun i => psi (ψ2 i)) atTop atTop := (hpsi.comp hψ2).tendsto_atTop
  filter_upwards [haeP, hconv] with om hom hcv hloL hhiL
  intro p
  have hlo0 := hom 0
  have hhi0 := hom 1
  simp only [X, ite_true, id] at hlo0
  simp only [X, one_ne_zero, ite_false, ite_true, id] at hhi0
  exact thm_prop_affine_ellipticity_core hd I model H (field om) z1 r1 h1 hP
    (fun i => NE (psi (ψ2 i))) (A om) (fun p => (hcv p).comp hidx) sigma hsigma
    (fun i => sN (ψ2 i) (field om)) cell _ _ hcell
    (tendsto_sub_nhds_zero_iff.1 hlo0) (tendsto_sub_nhds_zero_iff.1 hhi0) hloL hhiL p

end
end SubdiffusiveProcess.Paper
