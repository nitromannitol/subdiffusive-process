

module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Sobolev.FoldedGMCField
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Sobolev.PartitionEnergy
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Geometry.UpstreamCube
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.GoodScaleMathcalE
public import SubdiffusiveProcess.Frozen.Vocab.PaperHomogenizationError
public import Homogenization.Book.Ch02.Symmetric
public import Homogenization.Book.Ch01.FieldSpaces
public import SubdiffusiveProcess.Assumptions.CoefficientPackaging

@[expose] public section

open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open MeasureTheory Set TopologicalSpace Filter
open scoped BigOperators Topology ContDiff Distributions ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.EllipticRegularity

/-- `A_N` of `eq:mfd-normalization`  is continuous. -/
theorem cutoffCoefficient_continuous {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) :
    Continuous (cutoffCoefficient M H om N) := by
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact Continuous.sub
    (Continuous.add (H om).continuous
      (continuous_finsetSum _ fun j _ => (om (-(Int.ofNat j))).continuous))
    continuous_const

/-- `A_N` is everywhere positive. -/
theorem cutoffCoefficient_pos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffCoefficient M H om N x :=
  mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- `A_N` has the cube-by-cube scalar coefficient certificates of the imported
coarse-graining estimates. -/
theorem nonempty_cutoffTriadicData {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) :
    Nonempty (ScalarTriadicCoeffData (fun x => cutoffCoefficient M H om N x)) := by
  refine ⟨{ onCube := fun Q => ?_ }⟩
  exact Classical.choice
    (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
      (cutoffCoefficient_continuous M H om N)
      (cutoffCoefficient_pos M H om N)
      (Homogenization.Book.Ch02.cubeDomain Q))

/-- Every literal coordinate fold of `A_N` has the same certificates.  This is the
coefficient `ã = A_N ∘ T` of Proposition `mfd:prop-folded-iteration`. -/
theorem nonempty_foldedCutoffTriadicData {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (I P : Finset (Fin d)) :
    Nonempty (ScalarTriadicCoeffData
      (fun x => cutoffCoefficient M H om N (coordinateFold z I P x))) := by
  refine ⟨{ onCube := fun Q => ?_ }⟩
  exact Classical.choice
    (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
      ((cutoffCoefficient_continuous M H om N).comp (coordinateFold_continuous z I P))
      (fun x => cutoffCoefficient_pos M H om N (coordinateFold z I P x))
      (Homogenization.Book.Ch02.cubeDomain Q))

/-- The upstream triadic coefficient family of `A_N`, together with the a.e. symmetry
hypothesis that `SubdiffusiveProcess.Frozen.Section2.general_coarse_graining` and
`coarse_grained_poincare` require. -/
theorem exists_cutoffTriadicCoeffFamily {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) :
    ∃ A : Homogenization.Book.Ch02.TriadicCoeffFamily d,
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.Book.Ch02.CoeffOn.IsSymmetric (A.coeffOn Q) := by
  obtain ⟨data⟩ := nonempty_cutoffTriadicData M H om N
  exact ⟨data.toTriadicCoeffFamily, fun Q => (data.onCube Q).isSymmetric⟩

/-- The same for the folded coefficient `A_N ∘ T`. -/
theorem exists_foldedCutoffTriadicCoeffFamily {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (I P : Finset (Fin d)) :
    ∃ A : Homogenization.Book.Ch02.TriadicCoeffFamily d,
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.Book.Ch02.CoeffOn.IsSymmetric (A.coeffOn Q) := by
  obtain ⟨data⟩ := nonempty_foldedCutoffTriadicData M H om N z I P
  exact ⟨data.toTriadicCoeffFamily, fun Q => (data.onCube Q).isSymmetric⟩

/-- Link 5: the upstream integrand of `Homogenization.Book.Ch03.ABK26.IsForcedEquation`
for a scalar coefficient is the project's coefficient-weighted gradient product. -/
theorem vecDot_matVecMul_scalarMatrix {d : ℕ} (t : ℝ) (v w : Homogenization.Vec d) :
    Homogenization.vecDot (Homogenization.matVecMul (Homogenization.scalarMatrix t) v) w =
      t * ∑ i : Fin d, v i * w i := by
  rw [Homogenization.matVecMul_scalarMatrix, Homogenization.vecDot]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_assoc]

/-- The same statement for the GMC scalar coefficient field. -/
theorem vecDot_matVecMul_scalarCoeffField {d : ℕ} (f : Homogenization.Vec d → ℝ)
    (x : Homogenization.Vec d) (v w : Homogenization.Vec d) :
    Homogenization.vecDot
        (Homogenization.matVecMul (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f x) v) w =
      f x * ∑ i : Fin d, v i * w i :=
  vecDot_matVecMul_scalarMatrix (f x) v w

/-- The project's coefficient form is the sum of the coordinate coefficient integrals. -/
theorem sobolevCoefficientForm_eq_sum_integral {d : ℕ}
    {Om : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Om) (u v : SobolevData Om) :
    sobolevCoefficientForm a u v =
      ∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
        a.val x * (u.2 i x * v.2 i x) :=
  weightedGradientForm_apply a.val _ _

/-! ### Link 3: the converse of `exists_nativeH10Function_of_killedSobolevGraph` -/

theorem tendsto_toLp_of_eLpNorm_sub_tendsto {al : Type*} [MeasurableSpace al]
    (mu : Measure al) {f : al → ℝ} {g : ℕ → al → ℝ}
    (hf : MemLp f 2 mu) (hg : ∀ n, MemLp (g n) 2 mu)
    (h : Tendsto (fun n => eLpNorm (fun x => g n x - f x) 2 mu) atTop (nhds 0)) :
    Tendsto (fun n => (hg n).toLp (g n)) atTop (nhds (hf.toLp f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖(hg n).toLp (g n) - hf.toLp f‖ =
      (eLpNorm (fun x => g n x - f x) 2 mu).toReal := by
    intro n
    rw [← MemLp.toLp_sub (hg n) hf]
    exact Lp.norm_toLp _ _
  simp only [hnorm]
  have h0 : Tendsto (fun n => (eLpNorm (fun x => g n x - f x) 2 mu).toReal) atTop
      (nhds (0 : ℝ≥0∞).toReal) := (ENNReal.tendsto_toReal (by simp)).comp h
  simpa using h0

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Every upstream `H¹₀` function on the domain is the image of a killed Sobolev datum.
This is the converse of `exists_nativeH10Function_of_killedSobolevGraph`, and it is the
direction needed to promote the project's weak equation to the upstream forced equation,
whose test class is all of `Homogenization.H10Function`. -/
theorem exists_killedSobolevGraph_of_nativeH10
    (v : Homogenization.H10Function (Ω : Set (SpatialCoordinates d))) :
    ∃ u : killedSobolevGraph Ω,
      ((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        (v : SpatialCoordinates d → ℝ) ∧
      ∀ i : Fin d, ((u : SobolevData Ω).2 i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        (fun x => v.toH1Function.grad x i) := by
  classical
  set mu : Measure (SpatialCoordinates d) :=
    volume.restrict (Ω : Set (SpatialCoordinates d)) with hmu
  -- the test functions supplied by the approximating sequence
  let φ : ℕ → 𝓓(Ω, ℝ) := fun n =>
    ⟨v.approx n, v.approx_smooth n, v.approx_hasCompactSupport n, v.approx_support_subset n⟩
  -- the limiting Sobolev datum
  let f : SobolevData Ω :=
    (v.toH1Function.memL2.toLp _, fun i => (v.toH1Function.gradMemL2 i).toLp _)
  have hval : Tendsto (fun n => (smoothSobolevData (φ n)).1) atTop (nhds f.1) := by
    refine tendsto_toLp_of_eLpNorm_sub_tendsto mu v.toH1Function.memL2
      (fun n => (φ n).contDiff.continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport) ?_
    exact v.tendsto_approx
  have hgrad : ∀ i : Fin d,
      Tendsto (fun n => (smoothSobolevData (φ n)).2 i) atTop (nhds (f.2 i)) := by
    intro i
    refine tendsto_toLp_of_eLpNorm_sub_tendsto mu (v.toH1Function.gradMemL2 i)
      (fun n => ((((φ n).contDiff.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
          ((φ n).hasCompactSupport.fderiv_apply ℝ (Pi.single i 1)))) ?_
    have h := v.tendsto_approx_grad i
    simpa only [Homogenization.basisVec] using! h
  have htend : Tendsto (fun n => smoothSobolevData (φ n)) atTop (nhds f) :=
    hval.prodMk_nhds (tendsto_pi_nhds.2 hgrad)
  have hmem : f ∈ killedSobolevGraph Ω := by
    have hcl : f ∈ closure
        ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) : Set (SobolevData Ω)) :=
      mem_closure_of_tendsto htend (Eventually.of_forall fun n => ⟨φ n, rfl⟩)
    simpa [killedSobolevGraph, Submodule.topologicalClosure_coe] using! hcl
  refine ⟨⟨f, hmem⟩, ?_, ?_⟩
  · exact MemLp.coeFn_toLp v.toH1Function.memL2
  · intro i
    exact MemLp.coeFn_toLp (v.toH1Function.gradMemL2 i)


/-! ### Link 1: the origin cube -/

/-- `Homogenization.cubeCenter_originCube` is not exported upstream; only
`cubeScaleFactor_originCube` is. -/
theorem cubeCenter_originCube {d : ℕ} (m : ℤ) :
    Homogenization.cubeCenter (Homogenization.originCube d m) = 0 := by
  funext i
  simp [Homogenization.cubeCenter, Homogenization.originCube,
    Homogenization.cubeScaleFactor]

/-- The project's cube of side `3^m` centred at the origin is the open realization of the
upstream origin cube.  This is the shape in which the pinned GMC exports are stated
(`Homogenization.openCubeSet (Homogenization.originCube d m)`). -/
theorem centeredCube_zero_eq_openCubeSet_originCube {d : ℕ} (m : ℤ)
    (hr : (0 : ℝ) < (3 : ℝ) ^ m) :
    (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) hr :
        Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet (Homogenization.originCube d m) := by
  have h := centeredCube_eq_openCubeSet (Homogenization.originCube d m) hr
  rw [cubeCenter_originCube] at h
  exact h


/-! ### Link 5: the coefficient form is the upstream forced-equation integrand -/



theorem sobolevCoefficientForm_eq_upstream_integral {d : ℕ}
    {Om : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Om)
    (f : SpatialCoordinates d → ℝ)
    (hf : (fun x => a.val x) =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] f)
    (u v : SobolevData Om) :
    sobolevCoefficientForm a u v =
      ∫ x in (Om : Set (SpatialCoordinates d)),
        Homogenization.vecDot
          (Homogenization.matVecMul (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f x)
            (fun i => u.2 i x)) (fun i => v.2 i x) := by
  have hint : ∀ i : Fin d,
      IntegrableOn (fun x => (a.val : SpatialCoordinates d → ℝ) x * (u.2 i x * v.2 i x))
        (Om : Set (SpatialCoordinates d)) volume :=
    fun i => integrable_weighted_coordinates a.val (sobolevGradient u) (sobolevGradient v) i
  rw [sobolevCoefficientForm_eq_sum_integral]
  rw [← integral_finsetSum Finset.univ (fun i _ => hint i)]
  refine integral_congr_ae ?_
  filter_upwards [hf] with x hx
  rw [vecDot_matVecMul_scalarCoeffField, ← hx, Finset.mul_sum]

/-! ### `IterationInput.good_error` for the original field -/

/-- Paper `e.mathcalE.bound.applied` at a deterministic centre `z`.
Direct consumption of the pinned `SubdiffusiveProcess.Frozen.Section6.good_scale_mathcal_e`, whose
second conjunct is this bound at the centre `0`, together with the upstream covariance
lemmas `Section6Covariance.mem_goodEvent_iff_translate_zero` and
`translatePotentialSample_zero`.  Nothing is re-proved. -/
theorem good_scale_error_at_center (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ),
        s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2) →
      ∀ (L m : ℕ), m ≤ L →
      ∀ (om : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (z : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) (eps : ℝ),
        eps ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1 →
        om ∈ SubdiffusiveProcess.CoarseGrainingVocab.goodEvent M none m z eps s →
        SubdiffusiveProcess.CoarseGrainingVocab.section6HomogenizationError M s L m om z ≤ C * eps := by
  obtain ⟨C, hC, h⟩ := SubdiffusiveProcess.Frozen.Section6.good_scale_mathcal_e d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m hmL om z eps heps hgood
  have hgood0 : translatePotentialSample z om ∈
      SubdiffusiveProcess.CoarseGrainingVocab.goodEvent M none m 0 eps s :=
    (Section6Covariance.mem_goodEvent_iff_translate_zero M none m eps s z om).1 hgood
  have hmain := (h M s hs L m hmL (translatePotentialSample z om)).2 eps heps hgood0
  simpa only [section6HomogenizationError,
    Section6Covariance.translatePotentialSample_zero] using hmain

/-! ### The folded coarse error: reduction to the probe level

`eq:mfd-11` is already proved for the project's `triadicDefectSup`
(`SubdiffusiveProcess.triadicDefectSup_fold_discounts`).  The two lemmas here
unfold the upstream `paperHomogenizationError` at `(p,q) = (∞,2)` and reduce the
folded bound to a single inequality between the discounted sums of
`paperMaxDescendantProbeAtScale`, which is the ℝ≥0∞ analogue of the proved fold
discount. -/

theorem paperHomogenizationError_infinity_two_eq {d : ℕ}
    (Q : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d) (n : ℤ) (s : ℝ)
    (A : Homogenization.Book.Ch02.TriadicCoeffFamily d) (alpha : ℝ) :
    paperHomogenizationError Q n s Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) A alpha =
      (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) A alpha) ^ (1 / (2 : ℝ)) := by
  show paperHomogenizationErrorFinite Q n s Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 A alpha = _
  unfold paperHomogenizationErrorFinite
  congr 1
  refine tsum_congr fun l => ?_
  congr 1
  show (paperScaleResponseAtScale Q (n - (l : ℤ)) Homogenization.Book.Ch02.MultiscaleExponent.infinity A alpha)
      ^ (2 : ℝ) = _
  unfold paperScaleResponseAtScale
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Reduction of the folded coarse-error bound to one inequality at the probe level. -/
theorem paperHomogenizationError_le_of_probe_discounted_le {d : ℕ}
    (Q : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d) (n : ℤ) (s : ℝ)
    (A A' : Homogenization.Book.Ch02.TriadicCoeffFamily d) (alpha c : ℝ) (hc : 0 ≤ c)
    (h : (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
            paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) A' alpha) ≤
        ENNReal.ofReal c *
          ∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
            paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) A alpha) :
    paperHomogenizationError Q n s Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) A' alpha ≤
      ENNReal.ofReal (Real.sqrt c) *
        paperHomogenizationError Q n s Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) A alpha := by
  rw [paperHomogenizationError_infinity_two_eq, paperHomogenizationError_infinity_two_eq]
  calc
    _ ≤ (ENNReal.ofReal c *
        ∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) A alpha) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    _ = (ENNReal.ofReal c) ^ (1 / (2 : ℝ)) *
        (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) A alpha) ^ (1 / (2 : ℝ)) :=
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = _ := by
      congr 1
      rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hc (by norm_num)]

/-! ### Route (a): the scalar-coefficient energy identities

These discharge the *objective* half of `DirichletNuBridgeStatement` and
`NeumannNuBridgeStatement`: for a scalar coefficient the upstream Chapter 2 energy
values are the project's coefficient-weighted gradient integrals.  What remains in
those two statements is only the admissible-class match (zero potential trace versus
`affine + H¹₀`, and all of `H¹` versus mean-zero) and the transfer of the attained
extremum.   -/

/-- `vecDot` is symmetric. -/
theorem vecDot_comm {d : ℕ} (v w : Homogenization.Vec d) :
    Homogenization.vecDot v w = Homogenization.vecDot w v := by
  unfold Homogenization.vecDot
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- For a scalar coefficient the upstream Dirichlet energy value is the project's
coefficient-weighted gradient integral, halved and volume-normalized.  This discharges
the objective half of `DirichletNuBridgeStatement`. -/
theorem symmetricDirichletEnergyValue_scalar {d : ℕ} {U : Homogenization.Book.Ch02.Domain d}
    {a : Homogenization.Vec d → ℝ} (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (u : Homogenization.H1Function (U : Set (Homogenization.Vec d))) :
    Homogenization.Book.Ch02.symmetricDirichletEnergyValue U data.toCoeffOn u =
      (∫ x in (U : Set (Homogenization.Vec d)),
        a x * ∑ i : Fin d, (u.grad x i) ^ 2) /
          (2 * MeasureTheory.volume.real (U : Set (Homogenization.Vec d))) := by
  unfold Homogenization.Book.Ch02.symmetricDirichletEnergyValue Homogenization.Book.Ch02.average
  have hint : ∀ x : Homogenization.Vec d,
      (1 / 2 : ℝ) * Homogenization.vecDot (u.grad x)
          (Homogenization.matVecMul ((data.toCoeffOn).toCoeffField x) (u.grad x)) =
        (1 / 2 : ℝ) * (a x * ∑ i : Fin d, (u.grad x i) ^ 2) := by
    intro x
    congr 1
    rw [vecDot_comm]
    rw [show (data.toCoeffOn).toCoeffField = SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField a from rfl]
    rw [vecDot_matVecMul_scalarCoeffField]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => (sq (u.grad x i)).symm)
  simp only [hint]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.measureReal_def]
  field_simp


/-- For a scalar coefficient the upstream Neumann energy value is the project's
load-minus-energy integrand, volume-normalized.  This discharges the objective half of
`NeumannNuBridgeStatement`. -/
theorem symmetricNeumannEnergyValue_scalar {d : ℕ} {U : Homogenization.Book.Ch02.Domain d}
    {a : Homogenization.Vec d → ℝ} (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (q : Homogenization.Vec d)
    (u : Homogenization.H1Function (U : Set (Homogenization.Vec d))) :
    Homogenization.Book.Ch02.symmetricNeumannEnergyValue U data.toCoeffOn q u =
      (∫ x in (U : Set (Homogenization.Vec d)),
        ((∑ i : Fin d, q i * u.grad x i) -
          (1 / 2 : ℝ) * (a x * ∑ i : Fin d, (u.grad x i) ^ 2))) /
        MeasureTheory.volume.real (U : Set (Homogenization.Vec d)) := by
  unfold Homogenization.Book.Ch02.symmetricNeumannEnergyValue Homogenization.Book.Ch02.average
  have hint : ∀ x : Homogenization.Vec d,
      Homogenization.vecDot q (u.grad x) -
          (1 / 2 : ℝ) * Homogenization.vecDot (u.grad x)
            (Homogenization.matVecMul ((data.toCoeffOn).toCoeffField x) (u.grad x)) =
        (∑ i : Fin d, q i * u.grad x i) -
          (1 / 2 : ℝ) * (a x * ∑ i : Fin d, (u.grad x i) ^ 2) := by
    intro x
    have hE : Homogenization.vecDot (u.grad x)
        (Homogenization.matVecMul ((data.toCoeffOn).toCoeffField x) (u.grad x)) =
          a x * ∑ i : Fin d, (u.grad x i) ^ 2 := by
      rw [vecDot_comm,
        show (data.toCoeffOn).toCoeffField
          = SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField a from rfl,
        vecDot_matVecMul_scalarCoeffField]
      exact congrArg _ (Finset.sum_congr rfl fun i _ => (sq (u.grad x i)).symm)
    rw [hE]
    rfl
  simp only [hint]
  rw [MeasureTheory.measureReal_def]
  exact (div_eq_inv_mul _ _).symm




variable {d : ℕ} {Om : Opens (SpatialCoordinates d)}

/-- Gradient-level form of `exists_killedSobolevGraph_of_nativeH10`: a vector field with
zero potential trace on the domain is the weak gradient of a killed Sobolev datum. -/
theorem exists_killedSobolevGraph_of_potentialZeroTrace
    {f : SpatialCoordinates d → Homogenization.Vec d}
    (hf : Homogenization.Book.Ch01.PotentialZeroTraceFieldOn
      (Om : Set (SpatialCoordinates d)) f) :
    ∃ w : killedSobolevGraph Om, ∀ i : Fin d,
      ((w : SobolevData Om).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] fun x => f x i := by
  obtain ⟨-, u, hu⟩ := hf
  obtain ⟨w, -, hgrad⟩ := exists_killedSobolevGraph_of_nativeH10 u
  refine ⟨w, fun i => ?_⟩
  refine (hgrad i).trans ?_
  filter_upwards [hu] with x hx
  exact (congrFun hx i).symm


/-- `HasWeakPartialDerivOn` only sees a.e. equivalence classes on the domain. -/
theorem hasWeakPartialDerivOn_congr_ae {U : Set (SpatialCoordinates d)}
    {i : Fin d} {u u' g g' : SpatialCoordinates d → ℝ}
    (hu : u =ᵐ[volume.restrict U] u') (hg : g =ᵐ[volume.restrict U] g')
    (h : Homogenization.HasWeakPartialDerivOn U i u g) :
    Homogenization.HasWeakPartialDerivOn U i u' g' := by
  intro φ hφ hφc hφs
  have h1 : ∫ x in U, u' x * (fderiv ℝ φ x) (Homogenization.basisVec i) =
      ∫ x in U, u x * (fderiv ℝ φ x) (Homogenization.basisVec i) := by
    refine integral_congr_ae ?_
    filter_upwards [hu] with x hx
    rw [hx]
  have h2 : ∫ x in U, g' x * φ x = ∫ x in U, g x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  rw [h1, h2]
  exact h φ hφ hφc hφs

/-- Converse of `exists_nativeH1Function_of_weakSobolevGraph`: every upstream `H¹`
function on the domain is the value/gradient pair of a weak Sobolev datum. -/
theorem exists_weakSobolevGraph_of_nativeH1
    (v : Homogenization.H1Function (Om : Set (SpatialCoordinates d))) :
    ∃ u : weakSobolevGraph Om,
      ((u : SobolevData Om).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] v.toFun ∧
      ∀ i : Fin d, ((u : SobolevData Om).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] fun x => v.grad x i := by
  classical
  refine ⟨⟨(v.memL2.toLp _, fun i => (v.gradMemL2 i).toLp _), ?_⟩,
    MemLp.coeFn_toLp v.memL2, fun i => MemLp.coeFn_toLp (v.gradMemL2 i)⟩
  rw [mem_weakSobolevGraph_iff_hasWeakGradientOn]
  intro i
  exact hasWeakPartialDerivOn_congr_ae (MemLp.coeFn_toLp v.memL2).symm
    (MemLp.coeFn_toLp (v.gradMemL2 i)).symm (v.hasWeakGradient i)


/-- Forward gradient-level form: the weak gradient of a killed Sobolev datum is a field
with zero potential trace on the domain.  Converse of
`exists_killedSobolevGraph_of_potentialZeroTrace`. -/
theorem potentialZeroTrace_of_killedSobolevGraph (w : killedSobolevGraph Om) :
    Homogenization.Book.Ch01.PotentialZeroTraceFieldOn (Om : Set (SpatialCoordinates d))
      (fun x i => ((w : SobolevData Om).2 i : SpatialCoordinates d → ℝ) x) := by
  obtain ⟨v, -, hgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph w
  refine ⟨?_, v, ?_⟩
  · refine MeasureTheory.MemLp.of_eval ?_
    intro i
    exact Lp.memLp ((w : SobolevData Om).2 i)
  · exact Filter.EventuallyEq.of_eq hgrad.symm


/-- Zero potential trace only sees a.e. classes on the domain. -/
theorem potentialZeroTrace_congr_ae
    {f g : SpatialCoordinates d → Homogenization.Vec d}
    (hfg : f =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] g)
    (hf : Homogenization.Book.Ch01.PotentialZeroTraceFieldOn
      (Om : Set (SpatialCoordinates d)) f) :
    Homogenization.Book.Ch01.PotentialZeroTraceFieldOn
      (Om : Set (SpatialCoordinates d)) g := by
  obtain ⟨hL2, u, hu⟩ := hf
  exact ⟨hL2.ae_eq hfg, u, hfg.symm.trans hu⟩


variable [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]

/-- Constant data have zero weak gradient, hence lie in the weak Sobolev graph. -/
theorem constantSobolevData_mem_weak (c : ℝ) :
    ((domainConstantL2 (Ω := Om) c, fun _ => (0 : DomainL2 Om)) : SobolevData Om)
      ∈ weakSobolevGraph Om := by
  rw [mem_weakSobolevGraph_iff_hasWeakGradientOn]
  intro i
  have hconst : Homogenization.HasWeakPartialDerivOn
      (Om : Set (SpatialCoordinates d)) i (fun _ => c) (fun _ => (0 : ℝ)) := by
    have h := (Homogenization.HasWeakGradientOn.of_contDiff
      (U := (Om : Set (SpatialCoordinates d))) (f := fun _ : SpatialCoordinates d => c)
      (contDiff_const)) i
    simpa using h
  refine hasWeakPartialDerivOn_congr_ae ?_ ?_ hconst
  · exact (domainConstantL2_coeFn (Ω := Om) c).symm
  · exact (Lp.coeFn_zero ℝ 2 (volume.restrict (Om : Set (SpatialCoordinates d)))).symm

/-- Every weak Sobolev datum has a mean-zero representative with the same gradient.
This is the class match that `NeumannNuBridgeStatement` needs: the upstream supremum runs
over all of `H¹(U)`, the project's over mean-zero data, and the objective sees only the
gradient. -/
theorem exists_meanZeroSobolevGraph_of_weak
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (u : weakSobolevGraph Om) :
    ∃ v : meanZeroSobolevGraph Om,
      ∀ i : Fin d, (v : SobolevData Om).2 i = (u : SobolevData Om).2 i := by
  classical
  set c : ℝ := (volume.real (Om : Set (SpatialCoordinates d)))⁻¹ *
    ∫ x in (Om : Set (SpatialCoordinates d)), (u : SobolevData Om).1 x with hc
  refine ⟨⟨(u : SobolevData Om) -
      (domainConstantL2 (Ω := Om) c, fun _ => (0 : DomainL2 Om)), ?_⟩, ?_⟩
  · rw [mem_meanZeroSobolevGraph_iff]
    refine ⟨Submodule.sub_mem _ u.property (constantSobolevData_mem_weak c), ?_⟩
    have hco : ((((u : SobolevData Om) -
        (domainConstantL2 (Ω := Om) c, fun _ => (0 : DomainL2 Om))).1 :
          DomainL2 Om) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))]
      fun x => (u : SobolevData Om).1 x - c := by
      filter_upwards [Lp.coeFn_sub ((u : SobolevData Om).1)
        (domainConstantL2 (Ω := Om) c), domainConstantL2_coeFn (Ω := Om) c] with x h1 h2
      change (((((u : SobolevData Om).1 - domainConstantL2 (Ω := Om) c) :
        DomainL2 Om) : SpatialCoordinates d → ℝ)) x = _
      rw [h1, Pi.sub_apply, h2]
    rw [integral_congr_ae hco]
    have hInt : Integrable (fun x => ((u : SobolevData Om).1 : SpatialCoordinates d → ℝ) x)
        (volume.restrict (Om : Set (SpatialCoordinates d))) := by
      have h := (Lp.memLp ((u : SobolevData Om).1)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      simpa using h
    rw [integral_sub hInt (integrable_const c)]
    rw [MeasureTheory.setIntegral_const, hc, smul_eq_mul]
    have hne : volume.real (Om : Set (SpatialCoordinates d)) ≠ 0 := ne_of_gt hvol
    field_simp
    ring
  · intro i
    show (u : SobolevData Om).2 i - (0 : DomainL2 Om) = _
    exact sub_zero _




/-- Dividing a set of reals by a positive constant carries least elements to least
elements. -/
theorem isLeast_div_image {S : Set ℝ} {L c : ℝ} (hc : 0 < c) (h : IsLeast S L) :
    IsLeast ((fun x => x / c) '' S) (L / c) := by
  refine ⟨⟨L, h.1, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact div_le_div_of_nonneg_right (h.2 hx) hc.le



theorem symmetricDirichletEnergyValue_transport
    {d : ℕ} {Om : TopologicalSpace.Opens (SpatialCoordinates d)}
    {U : Homogenization.Book.Ch02.Domain d}
    (hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)))
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (g : HilbertGradient Om)
    (u : Homogenization.H1Function (U : Set (Homogenization.Vec d)))
    (hu : ∀ i : Fin d, (fun x => u.grad x i)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))]
        fun x => (g i : SpatialCoordinates d → ℝ) x) :
    Homogenization.Book.Ch02.symmetricDirichletEnergyValue U data.toCoeffOn u =
      (∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
        (aP.val : SpatialCoordinates d → ℝ) x * ((g i : SpatialCoordinates d → ℝ) x) ^ 2) /
        (2 * volume.real (Om : Set (SpatialCoordinates d))) := by
  rw [symmetricDirichletEnergyValue_scalar data u]
  have hvolU : volume.real (U : Set (Homogenization.Vec d)) =
      volume.real (Om : Set (SpatialCoordinates d)) := by rw [hset]
  have hmeas : volume.restrict (U : Set (Homogenization.Vec d)) =
      volume.restrict (Om : Set (SpatialCoordinates d)) := by rw [hset]
  have hu' : ∀ᵐ x ∂volume.restrict (Om : Set (SpatialCoordinates d)),
      ∀ i : Fin d, u.grad x i = (g i : SpatialCoordinates d → ℝ) x :=
    (Filter.eventually_all).2 hu
  have hswap : (∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
        (aP.val : SpatialCoordinates d → ℝ) x *
          ((g i : SpatialCoordinates d → ℝ) x) ^ 2) =
      ∫ x in (Om : Set (SpatialCoordinates d)),
        a x * ∑ i : Fin d, (u.grad x i) ^ 2 := by
    rw [← integral_finsetSum Finset.univ (fun i _ =>
      (by simpa only [pow_two] using (integrable_weighted_coordinates aP.val g g i) :
        Integrable (fun x => (aP.val : SpatialCoordinates d → ℝ) x *
          ((g i : SpatialCoordinates d → ℝ) x) ^ 2)
          (volume.restrict (Om : Set (SpatialCoordinates d)))))]
    refine integral_congr_ae ?_
    filter_upwards [haP, hu'] with x h1 h2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, h2 i]
  rw [hvolU, hmeas, hswap]



theorem symmetricDirichletNu_eq_affineDirichletResponse
    {d : ℕ} {Om : TopologicalSpace.Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hdom : Homogenization.IsOpenBoundedConvexDomain (Om : Set (SpatialCoordinates d)))
    (hne : (Om : Set (SpatialCoordinates d)).Nonempty)
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData
      (⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ : Homogenization.Book.Ch02.Domain d) a)
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) :
    Homogenization.Book.Ch02.symmetricDirichletNu
        (⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ : Homogenization.Book.Ch02.Domain d)
        data.toCoeffOn p =
      affineDirichletResponse hOm hD aP p /
        (2 * volume.real (Om : Set (SpatialCoordinates d))) := by
  classical
  set U : Homogenization.Book.Ch02.Domain d :=
    ⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ with hUdef
  have hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)) := rfl
  have hc : (0 : ℝ) < 2 * volume.real (Om : Set (SpatialCoordinates d)) := by linarith
  have hL := affineDirichletResponse_isLeast hOm hD aP p
  have hgrad : ∀ (w : killedSobolevGraph Om) (i : Fin d),
      ((sobolevGradient ((affineSobolev hOm p 0 : SobolevData Om) +
          (w : SobolevData Om)) i : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))]
      fun x => p i + ((w : SobolevData Om).2 i : SpatialCoordinates d → ℝ) x := by
    intro w i
    filter_upwards [Lp.coeFn_add ((affineSobolev hOm p 0 : SobolevData Om).2 i)
      ((w : SobolevData Om).2 i), domainConstantL2_coeFn (Ω := Om) (p i)] with x h1 h2
    show (((affineSobolev hOm p 0 : SobolevData Om).2 i +
      (w : SobolevData Om).2 i : DomainL2 Om) : SpatialCoordinates d → ℝ) x = _
    rw [h1, Pi.add_apply,
      show ((affineSobolev hOm p 0 : SobolevData Om).2 i : DomainL2 Om) =
        domainConstantL2 (Ω := Om) (p i) from rfl, h2]
  have hval : ∀ w : killedSobolevGraph Om,
      (∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
        (aP.val : SpatialCoordinates d → ℝ) x *
          ((sobolevGradient ((affineSobolev hOm p 0 : SobolevData Om) +
            (w : SobolevData Om)) i : SpatialCoordinates d → ℝ) x) ^ 2) =
      ∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
        (aP.val : SpatialCoordinates d → ℝ) x *
          (p i + ((w : SobolevData Om).2 i : SpatialCoordinates d → ℝ) x) ^ 2 := by
    intro w
    refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
    filter_upwards [hgrad w i] with x hx
    rw [hx]
  have hmem : ∀ w : killedSobolevGraph Om,
      ((affineSobolev hOm p 0 : SobolevData Om) + (w : SobolevData Om))
        ∈ weakSobolevGraph Om := fun w =>
    Submodule.add_mem _ (affineSobolev hOm p 0).2
      (killedSobolevGraph_le_weakSobolevGraph w.2)
  have hIsLeast : IsLeast
      (Homogenization.Book.Ch02.symmetricDirichletValueSet U data.toCoeffOn p)
      (affineDirichletResponse hOm hD aP p /
        (2 * volume.real (Om : Set (SpatialCoordinates d)))) := by
    constructor
    · obtain ⟨w₀, hw₀⟩ := hL.1
      obtain ⟨v, -, hv⟩ := exists_nativeH1Function_of_weakSobolevGraph
        (⟨_, hmem w₀⟩ : weakSobolevGraph Om)
      refine ⟨v, ?_, ?_⟩
      · refine potentialZeroTrace_congr_ae (Om := Om) ?_
          (potentialZeroTrace_of_killedSobolevGraph w₀)
        have hveq : ∀ i : Fin d, (fun x => v.grad x i)
            =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))]
              fun x => p i + ((w₀ : SobolevData Om).2 i : SpatialCoordinates d → ℝ) x := by
          intro i
          have hvi : (fun x => v.grad x i) = fun x =>
            ((sobolevGradient ((affineSobolev hOm p 0 : SobolevData Om) +
              (w₀ : SobolevData Om)) i : SpatialCoordinates d → ℝ)) x := by
            funext x; rw [hv]; rfl
          rw [hvi]; exact hgrad w₀ i
        have hall : ∀ᵐ x ∂volume.restrict (Om : Set (SpatialCoordinates d)),
            ∀ i : Fin d, v.grad x i =
              p i + ((w₀ : SobolevData Om).2 i : SpatialCoordinates d → ℝ) x :=
          (Filter.eventually_all).2 hveq
        filter_upwards [hall] with x hx
        funext i
        rw [Pi.sub_apply, hx i]
        ring
      · rw [symmetricDirichletEnergyValue_transport hset data aP haP
          (sobolevGradient ((affineSobolev hOm p 0 : SobolevData Om) +
            (w₀ : SobolevData Om))) v
          (fun i => by
            have hvi : (fun x => v.grad x i) = fun x =>
              ((sobolevGradient ((affineSobolev hOm p 0 : SobolevData Om) +
                (w₀ : SobolevData Om)) i : SpatialCoordinates d → ℝ)) x := by
              funext x; rw [hv]; rfl
            rw [hvi])]
        rw [hval w₀]
        exact (congrArg
          (fun t => t / (2 * volume.real (Om : Set (SpatialCoordinates d)))) hw₀).symm
    · rintro E ⟨u, hadm, rfl⟩
      obtain ⟨w, hw⟩ := exists_killedSobolevGraph_of_potentialZeroTrace (Om := Om)
        (potentialZeroTrace_congr_ae (Om := Om) (Filter.EventuallyEq.refl _ _) hadm)
      have hu : ∀ i : Fin d, (fun x => u.grad x i)
          =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))]
            fun x => p i + ((w : SobolevData Om).2 i : SpatialCoordinates d → ℝ) x := by
        intro i
        filter_upwards [hw i] with x hx
        simp only [Pi.sub_apply] at hx
        linarith
      rw [symmetricDirichletEnergyValue_transport hset data aP haP
        (sobolevGradient ((affineSobolev hOm p 0 : SobolevData Om) + (w : SobolevData Om)))
        u (fun i => (hu i).trans (hgrad w i).symm)]
      rw [hval w]
      exact div_le_div_of_nonneg_right (hL.2 ⟨w, rfl⟩) hc.le
  exact hIsLeast.csInf_eq






theorem symmetricNeumannEnergyValue_transport
    {d : ℕ} {Om : TopologicalSpace.Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    {U : Homogenization.Book.Ch02.Domain d}
    (hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)))
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (q : Fin d → ℝ) (g : HilbertGradient Om)
    (u : Homogenization.H1Function (U : Set (Homogenization.Vec d)))
    (hu : ∀ i : Fin d, (fun x => u.grad x i)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))]
        fun x => (g i : SpatialCoordinates d → ℝ) x) :
    Homogenization.Book.Ch02.symmetricNeumannEnergyValue U data.toCoeffOn q u =
      (2 * (∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
          q i * ((g i : SpatialCoordinates d → ℝ) x)) -
        ∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
          (aP.val : SpatialCoordinates d → ℝ) x *
            (((g i : SpatialCoordinates d → ℝ) x) *
             ((g i : SpatialCoordinates d → ℝ) x))) /
        (2 * volume.real (Om : Set (SpatialCoordinates d))) := by
  rw [symmetricNeumannEnergyValue_scalar data q u]
  have hvolU : volume.real (U : Set (Homogenization.Vec d)) =
      volume.real (Om : Set (SpatialCoordinates d)) := by rw [hset]
  have hmeas : volume.restrict (U : Set (Homogenization.Vec d)) =
      volume.restrict (Om : Set (SpatialCoordinates d)) := by rw [hset]
  have hu' : ∀ᵐ x ∂volume.restrict (Om : Set (SpatialCoordinates d)),
      ∀ i : Fin d, u.grad x i = (g i : SpatialCoordinates d → ℝ) x :=
    (Filter.eventually_all).2 hu
  have hIq : ∀ i : Fin d, Integrable
      (fun x => q i * ((g i : SpatialCoordinates d → ℝ) x))
      (volume.restrict (Om : Set (SpatialCoordinates d))) := by
    intro i
    have h := (Lp.memLp (g i)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact (h.const_mul (q i))
  have hIa : ∀ i : Fin d, Integrable
      (fun x => (aP.val : SpatialCoordinates d → ℝ) x *
        (((g i : SpatialCoordinates d → ℝ) x) * ((g i : SpatialCoordinates d → ℝ) x)))
      (volume.restrict (Om : Set (SpatialCoordinates d))) :=
    fun i => integrable_weighted_coordinates aP.val g g i
  have hsplit : (∫ x in (Om : Set (SpatialCoordinates d)),
        ((∑ i : Fin d, q i * u.grad x i) -
          (1 / 2 : ℝ) * (a x * ∑ i : Fin d, (u.grad x i) ^ 2))) =
      (∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
          q i * ((g i : SpatialCoordinates d → ℝ) x)) -
        (1 / 2 : ℝ) * ∑ i : Fin d, ∫ x in (Om : Set (SpatialCoordinates d)),
          (aP.val : SpatialCoordinates d → ℝ) x *
            (((g i : SpatialCoordinates d → ℝ) x) *
             ((g i : SpatialCoordinates d → ℝ) x)) := by
    have hcongr : (fun x => ((∑ i : Fin d, q i * u.grad x i) -
        (1 / 2 : ℝ) * (a x * ∑ i : Fin d, (u.grad x i) ^ 2)))
        =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))]
      fun x => (∑ i : Fin d, q i * ((g i : SpatialCoordinates d → ℝ) x)) -
        (1 / 2 : ℝ) * ∑ i : Fin d, (aP.val : SpatialCoordinates d → ℝ) x *
          (((g i : SpatialCoordinates d → ℝ) x) *
           ((g i : SpatialCoordinates d → ℝ) x)) := by
      filter_upwards [haP, hu'] with x h1 h2
      rw [Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
      · refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
        rw [h1, h2 i, pow_two]
    rw [integral_congr_ae hcongr]
    rw [integral_sub (integrable_finsetSum _ (fun i _ => hIq i))
      (((integrable_finsetSum _ (fun i _ => hIa i))).const_mul (1 / 2 : ℝ))]
    rw [integral_finsetSum _ (fun i _ => hIq i), integral_const_mul,
      integral_finsetSum _ (fun i _ => hIa i)]
  rw [hvolU, hmeas, hsplit]
  field_simp

/-- Dividing a set of reals by a positive constant carries greatest elements to greatest
elements. -/
theorem isGreatest_div_image {S : Set ℝ} {L c : ℝ} (hc : 0 < c) (h : IsGreatest S L) :
    IsGreatest ((fun x => x / c) '' S) (L / c) := by
  refine ⟨⟨L, h.1, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact div_le_div_of_nonneg_right (h.2 hx) hc.le



theorem symmetricNeumannNu_eq_affineInverseNeumannResponse
    {d : ℕ} {Om : TopologicalSpace.Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hdom : Homogenization.IsOpenBoundedConvexDomain (Om : Set (SpatialCoordinates d)))
    (hne : (Om : Set (SpatialCoordinates d)).Nonempty)
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData
      (⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ : Homogenization.Book.Ch02.Domain d) a)
    (hN : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Om) w‖)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (q : Fin d → ℝ) :
    Homogenization.Book.Ch02.symmetricNeumannNu
        (⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ : Homogenization.Book.Ch02.Domain d)
        data.toCoeffOn q =
      affineInverseNeumannResponse hN aP q /
        (2 * volume.real (Om : Set (SpatialCoordinates d))) := by
  classical
  set U : Homogenization.Book.Ch02.Domain d :=
    ⟨(Om : Set (SpatialCoordinates d)), hdom, hne⟩ with hUdef
  have hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)) := rfl
  have hc : (0 : ℝ) < 2 * volume.real (Om : Set (SpatialCoordinates d)) := by linarith
  have hY := affineInverseNeumannResponse_isGreatest hN aP q
  have hIsGreatest : IsGreatest
      (Homogenization.Book.Ch02.symmetricNeumannValueSet U data.toCoeffOn q)
      (affineInverseNeumannResponse hN aP q /
        (2 * volume.real (Om : Set (SpatialCoordinates d)))) := by
    constructor
    · obtain ⟨v₀, hv₀⟩ := hY.1
      obtain ⟨u, -, hv⟩ := exists_nativeH1Function_of_weakSobolevGraph
        (⟨(v₀ : SobolevData Om), ((mem_meanZeroSobolevGraph_iff _).1 v₀.2).1⟩ :
          weakSobolevGraph Om)
      refine ⟨u, ?_⟩
      rw [symmetricNeumannEnergyValue_transport hset data aP haP q
        (sobolevGradient (v₀ : SobolevData Om)) u
        (fun i => by
          have hvi : (fun x => u.grad x i) = fun x =>
            ((sobolevGradient (v₀ : SobolevData Om) i : SpatialCoordinates d → ℝ)) x := by
            funext x; rw [hv]; rfl
          rw [hvi])]
      exact (congrArg
        (fun t => t / (2 * volume.real (Om : Set (SpatialCoordinates d)))) hv₀).symm
    · rintro E ⟨u, rfl⟩
      obtain ⟨w, -, hgw⟩ := exists_weakSobolevGraph_of_nativeH1 (Om := Om) u
      obtain ⟨v, hvw⟩ := exists_meanZeroSobolevGraph_of_weak hvol w
      rw [symmetricNeumannEnergyValue_transport hset data aP haP q
        (sobolevGradient (v : SobolevData Om)) u
        (fun i => by
          filter_upwards [hgw i] with x hx
          show u.grad x i = ((v : SobolevData Om).2 i : SpatialCoordinates d → ℝ) x
          rw [hvw i]
          exact hx.symm)]
      exact div_le_div_of_nonneg_right (hY.2 ⟨v, rfl⟩) hc.le
  exact hIsGreatest.csSup_eq

end SubdiffusiveProcess.EllipticRegularity
