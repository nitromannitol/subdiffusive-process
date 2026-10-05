module

public import SubdiffusiveProcess.Paper.prop_conc_local_affine_order
public import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
-- Limit-form identification and comparison, using the explicit local
-- supplier interfaces in the declarations below.
public import SubdiffusiveProcess.Paper.thm_prop_affine_parameters
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.comparison_half_density
public import SubdiffusiveProcess.Paper.lem_affine
public import SubdiffusiveProcess.Paper.lem_boundary
public import SubdiffusiveProcess.Paper.lem_endpoints
public import SubdiffusiveProcess.Paper.lem_mass
public import SubdiffusiveProcess.Paper.lem_replace
public import SubdiffusiveProcess.Paper.lem_saving
public import SubdiffusiveProcess.Paper.prop_density
public import SubdiffusiveProcess.Paper.thm_C0
public import SubdiffusiveProcess.Paper.zero_endpoint_gap
public import SubdiffusiveProcess.Paper.optimal_endpoints
public import SubdiffusiveProcess.Paper.thm_prop_pointwise
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.in_represented_bounds
public import SubdiffusiveProcess.Paper.in_represented_enum
public import SubdiffusiveProcess.Paper.in_represented_mosco
public import SubdiffusiveProcess.Paper.in_represented_catalogue
public import SubdiffusiveProcess.Paper.prop_regularity
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.cor_32

public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import SubdiffusiveProcess.ResponseMoments.RelativeConcentration
public import SubdiffusiveProcess.Paper.prop_conc
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.lem_skeleton
public import SubdiffusiveProcess.Paper.lem_band
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import SubdiffusiveProcess.Paper.lem_truncation
public import SubdiffusiveProcess.Paper.obl_BH_compact_preimage_nullity
public import SubdiffusiveProcess.Paper.obl_BH_energy_measure_convergence
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq
public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import SubdiffusiveProcess.Paper.prop_gluing_smooth_mesh
public import SubdiffusiveProcess.Paper.lem_skeleton_smooth_approx
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.uniform_response_input
public import SubdiffusiveProcess.Paper.conv_represented_estimates_change_input
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import Mathlib.Probability.ProductMeasure
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import SubdiffusiveProcess.EllipticRegularity.Scaling
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import SubdiffusiveProcess.Sobolev.DomainPoincare

public import SubdiffusiveProcess.Paper.Support.ThmPropBasePart02

@[expose] public section

/-!
Proof support for SubdiffusiveProcess.Paper.thm_prop_base, part 3.
Supports: thm_prop_base
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The logarithm of the cutoff coefficient as one global continuous function. -/
def aux_thm_prop_affine_logpot {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) -
      ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) + H om +
    ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i))

theorem aux_thm_prop_affine_logpot_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) :
    Measurable (aux_thm_prop_affine_logpot model H N) :=
  (measurable_const.add hH).add
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i)))

theorem aux_thm_prop_affine_log_eq {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    continuousPositiveLog (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM model H om N z hr)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos model H om N z hr) -
      ContinuousMap.const _ (Real.log 1) =
    (aux_thm_prop_affine_logpot model H N om).restrict
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  rw [Real.log_one, ContinuousMap.const_zero, sub_zero]
  ext x
  show Real.log (cutoffCoefficient model H om N (x : SpatialCoordinates d)) =
    aux_thm_prop_affine_logpot model H N om (x : SpatialCoordinates d)
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N).ne')
    (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  simp only [aux_thm_prop_affine_logpot, cutoffPotential, ContinuousMap.add_apply,
    ContinuousMap.const_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  ring

/-- Measurability of the cutoff affine response in the field. -/
theorem aux_thm_prop_affine_response_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (pvec : Fin d → ℝ) :
    Measurable (fun om : BilateralField d => affineDirichletResponse
      (centeredCube_isBounded z hr) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z hr) pvec) := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hD := ((continuous_dirichletResponse_compact (killedResponseSpace hP)
      (closedCube z r hr) (affineSobolev (centeredCube_isBounded z hr) pvec 0)).comp
    (ContinuousMap.continuous_restrict
      (closedCube z r hr : Set (SpatialCoordinates d)))).measurable.comp
    (aux_thm_prop_affine_logpot_measurable model H hH N)
  convert hD using 1
  funext om
  simp only [Function.comp_apply]
  unfold affineDirichletResponse _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
    normalizedContinuousPositiveCoefficient
  rw [aux_thm_prop_affine_log_eq]

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_matrix_quadratic_eq {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
    p ⬝ᵥ A.mulVec p = ∑ i : Fin d, ∑ j : Fin d, A i j * p i * p j := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual measurable quadratic responses determine a.e.-measurable entries of
their symmetric limiting matrix, without completeness of the probability space. -/
theorem aux_thm_prop_matrix_limit_aemeasurable
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℕ → Ω → (Fin d → ℝ) → ℝ)
    (hR : ∀ n p, Measurable (fun om => R n om p))
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsym : ∀ om, (A om).transpose = A om)
    (hlim : ∀ᵐ om ∂P, ∀ p : Fin d → ℝ,
      Tendsto (fun n => R n om p) atTop (𝓝 (p ⬝ᵥ (A om).mulVec p))) :
    ∀ i j, AEMeasurable (fun om => A om i j) P := by
  intro i j
  let ei : Fin d → ℝ := Pi.single i 1
  let ej : Fin d → ℝ := Pi.single j 1
  apply aemeasurable_of_tendsto_metrizable_ae' (f := fun n om =>
    (R n om (ei + ej) - R n om ei - R n om ej) / 2)
    (fun n => (((hR n (ei + ej)).sub (hR n ei)).sub (hR n ej)).div_const 2 |>.aemeasurable)
  filter_upwards [hlim] with om hom
  have h := (((hom (ei + ej)).sub (hom ei)).sub (hom ej)).div_const 2
  have heq : (((ei + ej) ⬝ᵥ (A om).mulVec (ei + ej) -
      ei ⬝ᵥ (A om).mulVec ei - ej ⬝ᵥ (A om).mulVec ej) / 2) = A om i j := by
    simp only [aux_thm_prop_matrix_quadratic_eq]
    exact aux_thm_prop_matrix_polarization (A om)
      (fun k l => (congrFun (congrFun (hsym om) k) l).symm) i j
  rwa [heq] at h

/-- A countable family of a.e.-measurable symmetric matrices admits measurable
versions which remain symmetric at every sample. Symmetrization is performed
only after taking genuine measurable versions of every entry. -/
theorem aux_thm_prop_symmetric_measurable_versions
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsym : ∀ k om, (A k om).transpose = A k om)
    (hmeas : ∀ k i j, AEMeasurable (fun om => A k om i j) P) :
    ∃ B : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ,
      (∀ k i j, Measurable (fun om => B k om i j)) ∧
      (∀ k om, (B k om).transpose = B k om) ∧
      (∀ᵐ om ∂P, ∀ k, B k om = A k om) := by
  let C : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ := fun k om i j =>
    (hmeas k i j).mk (fun om => A k om i j) om
  let B : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ := fun k om i j =>
    (C k om i j + C k om j i) / 2
  refine ⟨B, ?_, ?_, ?_⟩
  · intro k i j
    exact ((hmeas k i j).measurable_mk.add (hmeas k j i).measurable_mk).div_const 2
  · intro k om
    ext i j
    change (C k om j i + C k om i j) / 2 = (C k om i j + C k om j i) / 2
    rw [add_comm]
  · have hC : ∀ᵐ om ∂P, ∀ k i j, A k om i j = C k om i j :=
      ae_all_iff.mpr fun k => ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
        (hmeas k i j).ae_eq_mk
    filter_upwards [hC] with om hom k
    ext i j
    change (C k om i j + C k om j i) / 2 = A k om i j
    rw [← hom k i j, ← hom k j i]
    have hs : A k om j i = A k om i j := congrFun (congrFun (hsym k om) i) j
    rw [hs]
    ring

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Both actual normalized affine matrix banks have entrywise measurable,
everywhere symmetric versions on one common probability-one event. -/
theorem aux_thm_prop_catalogue_measurable_affine_matrices
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hH : Measurable H)
    (field : Ω → BilateralField d) (hfield : Measurable field)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖) :
    ∃ AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ,
      (∀ j om, (AE j om).transpose = AE j om) ∧
      (∀ j om, (AF j om).transpose = AF j om) ∧
      (∀ j i k, Measurable (fun om => AE j om i k)) ∧
      (∀ j i k, Measurable (fun om => AF j om i k)) ∧
      ∀ᵐ om ∂P, ∀ j,
        aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
        aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om) := by
  obtain ⟨AE, AF, hEsym, hFsym, hconv⟩ := aux_thm_prop_catalogue_affine_matrices
    d hd model H Ω P field z r hr Sspace NE NF alpha eta hCat hP
  have hME : ∀ j i k, AEMeasurable (fun om => AE j om i k) P := by
    intro j
    exact aux_thm_prop_matrix_limit_aemeasurable P
      (fun n om p => affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field om) (NE n) (z j) (hr j)) p /
        (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
      (fun n p => ((aux_thm_prop_affine_response_measurable model H hH (NE n)
        (z j) (hr j) (hP j) p).comp hfield).div_const _)
      (AE j) (hEsym j) (hconv.mono fun om hom => (hom j).1)
  have hMF : ∀ j i k, AEMeasurable (fun om => AF j om i k) P := by
    intro j
    exact aux_thm_prop_matrix_limit_aemeasurable P
      (fun n om p => affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field om) (NF n) (z j) (hr j)) p /
        (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
      (fun n p => ((aux_thm_prop_affine_response_measurable model H hH (NF n)
        (z j) (hr j) (hP j) p).comp hfield).div_const _)
      (AF j) (hFsym j) (hconv.mono fun om hom => (hom j).2)
  obtain ⟨BE, hBEmeas, hBEsym, hBEeq⟩ := aux_thm_prop_symmetric_measurable_versions P AE hEsym hME
  obtain ⟨BF, hBFmeas, hBFsym, hBFeq⟩ := aux_thm_prop_symmetric_measurable_versions P AF hFsym hMF
  refine ⟨BE, BF, hBEsym, hBFsym, hBEmeas, hBFmeas, ?_⟩
  filter_upwards [hconv, hBEeq, hBFeq] with om hc he hf j
  rw [he j, hf j]
  exact hc j

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

-- Shared proof: SubdiffusiveProcess.Paper.prop_conc_local_affine_order supplies aux_thm_prop_boundary_glb_order.

-- Shared proof: SubdiffusiveProcess.Paper.prop_conc_local_affine_order supplies aux_thm_prop_affine_matrix_order.

/-- Quadratic matrix comparison bounds the trace ratio used to define the
deterministic coefficient. -/
theorem aux_thm_prop_trace_ratio_bounds
    {d : ℕ} (AE AF : Matrix (Fin d) (Fin d) ℝ) (m M : ℝ)
    (htrace : 0 < Matrix.trace AE)
    (horder : ∀ p : Fin d → ℝ,
      m * (p ⬝ᵥ AE.mulVec p) ≤ p ⬝ᵥ AF.mulVec p ∧
      p ⬝ᵥ AF.mulVec p ≤ M * (p ⬝ᵥ AE.mulVec p)) :
    Matrix.trace AF / Matrix.trace AE ∈ Icc m M := by
  have hdiag (i : Fin d) : m * AE i i ≤ AF i i ∧ AF i i ≤ M * AE i i := by
    simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul] using! horder (Pi.single i 1)
  have hlo : m * Matrix.trace AE ≤ Matrix.trace AF := by
    simpa [Matrix.trace, Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hdiag i).1)
  have hhi : Matrix.trace AF ≤ M * Matrix.trace AE := by
    simpa [Matrix.trace, Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hdiag i).2)
  exact ⟨(le_div_iff₀ htrace).mpr hlo, (div_le_iff₀ htrace).mpr hhi⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
noncomputable section
variable {d : ℕ}

/-- The affine map `y ↦ R y + w`. -/
def aux_thm_prop_affineMap (R : Homogenization.Mat d) (w : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun y => matVecMul R y + w, by
    refine Continuous.add ?_ continuous_const
    exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_apply j)⟩

theorem aux_thm_prop_affineMap_apply (R : Homogenization.Mat d) (w y : SpatialCoordinates d) :
    aux_thm_prop_affineMap R w y = matVecMul R y + w := rfl

/-- Precomposition of a continuous field by the affine map. -/
def aux_thm_prop_precomp (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (g : C(SpatialCoordinates d, ℝ)) : C(SpatialCoordinates d, ℝ) :=
  g.comp (aux_thm_prop_affineMap R w)

theorem aux_thm_prop_precomp_continuous (R : Homogenization.Mat d) (w : SpatialCoordinates d) :
    Continuous (aux_thm_prop_precomp R w) :=
  ContinuousMap.continuous_precomp (aux_thm_prop_affineMap R w)

theorem aux_thm_prop_matVecMul_smul (R : Homogenization.Mat d) (c : ℝ) (y : SpatialCoordinates d) :
    matVecMul R (c • y) = c • matVecMul R y := by
  funext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

section laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_thm_prop_precomp_measurable (R : Homogenization.Mat d) (w : SpatialCoordinates d) :
    Measurable (aux_thm_prop_precomp R w) :=
  (aux_thm_prop_precomp_continuous R w).measurable

/-- The root field law is invariant under every affine signed coordinate permutation. -/
theorem aux_thm_prop_root_invariant (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R) (w : SpatialCoordinates d) :
    ((chaosRootFieldLaw M : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
        Measure C(SpatialCoordinates d, ℝ)).map (aux_thm_prop_precomp R w) =
      (chaosRootFieldLaw M : Measure C(SpatialCoordinates d, ℝ)) := by
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  have hroot : ((chaosRootFieldLaw M : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
      Measure C(SpatialCoordinates d, ℝ)) =
      ((_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P :
        ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialField d)) :
          Measure (_root_.SubdiffusiveProcess.Model.PotentialField d)).map forget := by
    simp only [chaosRootFieldLaw, ProbabilityMeasure.toMeasure_map]
    rfl
  have hrot := congrArg ProbabilityMeasure.toMeasure
    (M.G3.signed_coordinate_permutations R hR)
  rw [ProbabilityMeasure.toMeasure_map] at hrot
  have hstat := M.G1.stationary w
  have hcomm : aux_thm_prop_precomp R w ∘ forget =
      forget ∘ (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR ∘
        _root_.SubdiffusiveProcess.Model.PotentialField.translate w) := by
    funext g
    ext y
    rfl
  have hforget : Measurable forget := forget.continuous.measurable
  rw [hroot, Measure.map_map (aux_thm_prop_precomp_measurable R w) hforget, hcomm,
    ← Measure.map_map hforget
      ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR).comp
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate w)),
    ← Measure.map_map (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR)
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate w), hstat, hrot]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Layer scaling intertwines the affine map with the rescaled translation part. -/
theorem aux_thm_prop_precomp_layerScaling
    [_portSection0 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection1 : BorelSpace C(SpatialCoordinates d, ℝ)] (R : Homogenization.Mat d) (w : SpatialCoordinates d) (j : ℤ) :
    aux_thm_prop_precomp R w ∘ layerScaling d j =
      layerScaling d j ∘ aux_thm_prop_precomp R (((3 : ℝ) ^ (-j)) • w) := by
  funext g
  ext y
  simp only [Function.comp_apply, aux_thm_prop_precomp, ContinuousMap.comp_apply,
    aux_thm_prop_affineMap_apply, layerScaling, ContinuousMap.compRightContinuousMap_apply,
    ContinuousMap.coe_mk]
  congr 1
  rw [smul_add, aux_thm_prop_matVecMul_smul]

theorem aux_thm_prop_layer_invariant (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R) (w : SpatialCoordinates d) (j : ℤ) :
    ((scaledLayerLaw d (chaosRootFieldLaw M) j : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
        Measure C(SpatialCoordinates d, ℝ)).map (aux_thm_prop_precomp R w) =
      (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ)) := by
  have hS : Measurable (layerScaling d j) := (layerScaling d j).continuous.measurable
  simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (aux_thm_prop_precomp_measurable R w) hS,
    aux_thm_prop_precomp_layerScaling,
    ← Measure.map_map hS (aux_thm_prop_precomp_measurable R _),
    aux_thm_prop_root_invariant M R hR]

/-- The chaos sample law is invariant under composing every layer with the affine map. -/
theorem aux_thm_prop_chaos_invariant (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R) (w : SpatialCoordinates d) :
    ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)).map
        (fun x : BilateralField d => fun j => aux_thm_prop_precomp R w (x j)) =
      (chaosSampleLaw M : Measure (BilateralField d)) := by
  change (Measure.infinitePi (fun j : ℤ =>
      ((scaledLayerLaw d (chaosRootFieldLaw M) j : ProbabilityMeasure _) :
        Measure C(SpatialCoordinates d, ℝ)))).map
      (fun x : BilateralField d => fun j => aux_thm_prop_precomp R w (x j)) =
    Measure.infinitePi (fun j : ℤ =>
      ((scaledLayerLaw d (chaosRootFieldLaw M) j : ProbabilityMeasure _) :
        Measure C(SpatialCoordinates d, ℝ)))
  rw [Measure.infinitePi_map_pi _ (fun _ => aux_thm_prop_precomp_measurable R w)]
  congr 1
  funext j
  exact aux_thm_prop_layer_invariant M R hR w j

end laws


def aux_thm_prop_T (R : Homogenization.Mat d) (w : SpatialCoordinates d) (x : BilateralField d) :
    BilateralField d :=
  fun j => aux_thm_prop_precomp R w (x j)

/-- The anchored-gauge transform of the infrared field. -/
def aux_thm_prop_gauge (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (h : C(SpatialCoordinates d, ℝ)) : C(SpatialCoordinates d, ℝ) :=
  aux_thm_prop_precomp R w h - ContinuousMap.const _ (h (aux_thm_prop_affineMap R w 0))

theorem aux_thm_prop_gauge_continuous (R : Homogenization.Mat d) (w : SpatialCoordinates d) :
    Continuous (aux_thm_prop_gauge R w) := by
  refine (aux_thm_prop_precomp_continuous R w).sub ?_
  exact ContinuousMap.const'.continuous.comp (continuous_eval_const _)

theorem aux_thm_prop_infraredPartialSum_T (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (x : BilateralField d) (L : ℕ) :
    infraredPartialSum (aux_thm_prop_T R w x) L =
      aux_thm_prop_gauge R w (infraredPartialSum x L) := by
  ext y
  simp only [infraredPartialSum, aux_thm_prop_gauge, aux_thm_prop_T, aux_thm_prop_precomp,
    ContinuousMap.sub_apply, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.coe_sub, Pi.sub_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- The infrared field transforms with the anchored gauge wherever both partial-sum
limits exist. -/
theorem aux_thm_prop_H_T (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x : BilateralField d)
    (hx : Tendsto (infraredPartialSum x) atTop (𝓝 (H x)))
    (hTx : Tendsto (infraredPartialSum (aux_thm_prop_T R w x)) atTop
      (𝓝 (H (aux_thm_prop_T R w x)))) :
    H (aux_thm_prop_T R w x) = aux_thm_prop_gauge R w (H x) := by
  have h2 : Tendsto (infraredPartialSum (aux_thm_prop_T R w x)) atTop
      (𝓝 (aux_thm_prop_gauge R w (H x))) := by
    have := ((aux_thm_prop_gauge_continuous R w).tendsto (H x)).comp hx
    refine this.congr fun L => ?_
    simp only [Function.comp_apply, aux_thm_prop_infraredPartialSum_T]
  exact tendsto_nhds_unique hTx h2

/-- The cutoff coefficient transforms by the gauge constant. -/
theorem aux_thm_prop_cutoffCoefficient_T (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x : BilateralField d)
    (hH : H (aux_thm_prop_T R w x) = aux_thm_prop_gauge R w (H x)) (N : ℕ)
    (y : SpatialCoordinates d) :
    cutoffCoefficient model H (aux_thm_prop_T R w x) N y =
      Real.exp (-(H x (aux_thm_prop_affineMap R w 0))) *
        cutoffCoefficient model H x N (aux_thm_prop_affineMap R w y) := by
  simp only [cutoffCoefficient, cutoffPotential, hH, aux_thm_prop_gauge, aux_thm_prop_T,
    aux_thm_prop_precomp, ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring


end
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Translation covariance of the actual affine minimum follows by composing
two proved reflection bijections. A common positive gauge scales its value. -/
theorem aux_thm_prop_affine_response_translation
    {d : ℕ} (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' r hr),
      ‖(u : SobolevData (centeredCube z' r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube z' r hr))
    (c : ℝ) (hc : 0 < c)
    (hab : ∀ᵐ x ∂volume.restrict (centeredCube z' r hr : Set (SpatialCoordinates d)),
      b.val x = c * a.val (x + z - z')) (p : Fin d → ℝ) :
    affineDirichletResponse (centeredCube_isBounded z' hr) hP' b p =
      c * affineDirichletResponse (centeredCube_isBounded z hr) hP a p := by
  let mid : SpatialCoordinates d := fun i => (z i + z' i) / 2
  have hmid : coordinateReflection mid Finset.univ z' = z := by
    ext i
    simp only [coordinateReflection, Finset.mem_univ, ite_true, mid]
    ring
  have hself : coordinateReflection z' Finset.univ z' = z' := by
    ext i
    simp only [coordinateReflection, Finset.mem_univ, ite_true]
    ring
  have hpre : coordinateReflection mid Finset.univ ⁻¹'
      (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z' r hr : Set (SpatialCoordinates d)) := by
    simpa only [hmid] using coordinateReflection_preimage_cube mid Finset.univ z' hr
  have hpre' : coordinateReflection z' Finset.univ ⁻¹'
      (centeredCube z' r hr : Set (SpatialCoordinates d)) =
      (centeredCube z' r hr : Set (SpatialCoordinates d)) := by
    simpa only [hself] using coordinateReflection_preimage_cube z' Finset.univ z' hr
  let a1 := reflectionCoefficient mid Finset.univ hpre a
  let a2 := reflectionCoefficient z' Finset.univ hpre' a1
  have hcomp (x : SpatialCoordinates d) :
      coordinateReflection mid Finset.univ (coordinateReflection z' Finset.univ x) =
        x + z - z' := by
    ext i
    simp only [coordinateReflection, Finset.mem_univ, ite_true, Pi.add_apply, Pi.sub_apply, mid]
    ring
  have hval : ∀ᵐ x ∂volume.restrict (centeredCube z' r hr : Set (SpatialCoordinates d)),
      a2.val x = a.val (x + z - z') := by
    have hm := coordinateReflection_domain_measurePreserving z' Finset.univ hpre'
    filter_upwards [reflectionCoefficient_coeFn z' Finset.univ hpre' a1,
      hm.quasiMeasurePreserving.ae (reflectionCoefficient_coeFn mid Finset.univ hpre a)]
      with x h2 h1
    change a1.val (coordinateReflection z' Finset.univ x) =
      a.val (coordinateReflection mid Finset.univ (coordinateReflection z' Finset.univ x)) at h1
    change a2.val x = a1.val (coordinateReflection z' Finset.univ x) at h2
    rw [h2, h1, hcomp]
  have hb : b = smulPositiveCoefficient hc a2 := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hab, hval, smulPositiveCoefficient_coeFn hc a2] with x hx h2 hs
    change b.val x = (smulPositiveCoefficient hc a2).val x
    rw [hx, hs, h2]
  have h1 := affineDirichletResponse_reflection mid Finset.univ hpre
    (centeredCube_isBounded z hr) (centeredCube_isBounded z' hr) hP hP' a p
  have h2 := affineDirichletResponse_reflection z' Finset.univ hpre'
    (centeredCube_isBounded z' hr) (centeredCube_isBounded z' hr) hP' hP' a1
    (coordinateReflectionDerivative Finset.univ p)
  rw [coordinateReflectionDerivative_involutive] at h2
  rw [hb, affineDirichletResponse_smulCoeff, h2, h1]

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology

namespace SubdiffusiveProcess.Paper

/-- A genuine scalar response limit factors through its measurable field. The
canonical factor is the measurable limit, also on incomplete probability spaces. -/
theorem aux_thm_prop_limit_factor
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (μ : Measure Ξ) (field : Ω → Ξ)
    (hfield : Measurable field) (hlaw : P.map field = μ)
    (f : ℕ → Ξ → ℝ) (hf : ∀ n, Measurable (f n)) (L : Ω → ℝ)
    (hlim : ∀ᵐ om ∂P, Tendsto (fun n => f n (field om)) atTop (𝓝 (L om))) :
    ∃ g : Ξ → ℝ, Measurable g ∧
      (∀ᵐ om ∂P, g (field om) = L om) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  let g : Ξ → ℝ := fun x => limUnder atTop (fun n => f n x)
  have hg : Measurable g :=
    (StronglyMeasurable.limUnder (fun n => (hf n).stronglyMeasurable)).measurable
  have heq : ∀ᵐ om ∂P, g (field om) = L om := hlim.mono fun _ h => h.limUnder_eq
  refine ⟨g, hg, heq, ?_⟩
  rw [← hlaw, ae_map_iff hfield.aemeasurable (measurableSet_tendsto_fun hf hg)]
  filter_upwards [hlim, heq] with om h he
  rwa [he]

/-- A common nonzero gauge in two actual response sequences cancels in their
limiting trace ratio. A measure-preserving field symmetry therefore identifies
the expected ratios, without choosing any off-event matrix representative. -/
theorem aux_thm_prop_limit_ratio_integral
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (μ : Measure Ξ) (field : Ω → Ξ)
    (hfield : Measurable field) (hlaw : P.map field = μ)
    (T : Ξ → Ξ) (hT : MeasurePreserving T μ μ)
    (aE aF bE bF : ℕ → Ξ → ℝ)
    (haE : ∀ n, Measurable (aE n)) (haF : ∀ n, Measurable (aF n))
    (hbE : ∀ n, Measurable (bE n)) (hbF : ∀ n, Measurable (bF n))
    (AE AF BE BF : Ω → ℝ)
    (hAE : ∀ᵐ om ∂P, Tendsto (fun n => aE n (field om)) atTop (𝓝 (AE om)))
    (hAF : ∀ᵐ om ∂P, Tendsto (fun n => aF n (field om)) atTop (𝓝 (AF om)))
    (hBE : ∀ᵐ om ∂P, Tendsto (fun n => bE n (field om)) atTop (𝓝 (BE om)))
    (hBF : ∀ᵐ om ∂P, Tendsto (fun n => bF n (field om)) atTop (𝓝 (BF om)))
    (c : Ξ → ℝ)
    (hcov : ∀ᵐ x ∂μ, c x ≠ 0 ∧ ∀ n,
      bE n (T x) = c x * aE n x ∧ bF n (T x) = c x * aF n x) :
    (∫ om, BF om / BE om ∂P) = ∫ om, AF om / AE om ∂P := by
  obtain ⟨a, hma, hea, hla⟩ := aux_thm_prop_limit_factor P μ field hfield hlaw aE haE AE hAE
  obtain ⟨f, hmf, hef, hlf⟩ := aux_thm_prop_limit_factor P μ field hfield hlaw aF haF AF hAF
  obtain ⟨b, hmb, heb, hlb⟩ := aux_thm_prop_limit_factor P μ field hfield hlaw bE hbE BE hBE
  obtain ⟨g, hmg, heg, hlg⟩ := aux_thm_prop_limit_factor P μ field hfield hlaw bF hbF BF hBF
  have hratio : ∀ᵐ x ∂μ, g (T x) / b (T x) = f x / a x := by
    filter_upwards [hla, hlf, hT.quasiMeasurePreserving.ae hlb,
      hT.quasiMeasurePreserving.ae hlg, hcov] with x hla hlf hlb hlg hc
    have hbe : b (T x) = c x * a x := tendsto_nhds_unique hlb
      ((hla.const_mul (c x)).congr fun n => (hc.2 n).1.symm)
    have hbf : g (T x) = c x * f x := tendsto_nhds_unique hlg
      ((hlf.const_mul (c x)).congr fun n => (hc.2 n).2.symm)
    rw [hbe, hbf, mul_div_mul_left _ _ hc.1]
  have hleft : (∫ om, BF om / BE om ∂P) = ∫ x, g x / b x ∂μ := by
    rw [← hlaw]
    rw [show (∫ x, g x / b x ∂Measure.map field P) =
      ∫ om, g (field om) / b (field om) ∂P from
      (by simpa only [Pi.div_apply] using! integral_map hfield.aemeasurable (hmg.div hmb).aestronglyMeasurable)]
    apply integral_congr_ae
    filter_upwards [heb, heg] with om hb hg
    rw [hb, hg]
  have hright : (∫ om, AF om / AE om ∂P) = ∫ x, f x / a x ∂μ := by
    rw [← hlaw]
    rw [show (∫ x, f x / a x ∂Measure.map field P) =
      ∫ om, f (field om) / a (field om) ∂P from
      (by simpa only [Pi.div_apply] using! integral_map hfield.aemeasurable (hmf.div hma).aestronglyMeasurable)]
    apply integral_congr_ae
    filter_upwards [hea, hef] with om ha hf
    rw [ha, hf]
  rw [hleft, hright]
  calc
    (∫ x, g x / b x ∂μ) = ∫ x, g (T x) / b (T x) ∂μ := by
      conv_lhs => rw [← hT.map_eq]
      exact integral_map hT.measurable.aemeasurable (hmg.div hmb).aestronglyMeasurable
    _ = ∫ x, f x / a x ∂μ := integral_congr_ae hratio

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_cube_translation_preserving
    {d : ℕ} (z z' : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    MeasurePreserving (fun x : SpatialCoordinates d => x + z - z')
      (volume.restrict (centeredCube z' r hr : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let mid : SpatialCoordinates d := fun i => (z i + z' i) / 2
  have hmid : coordinateReflection mid Finset.univ z' = z := by
    ext i
    simp only [coordinateReflection, Finset.mem_univ, ite_true, mid]
    ring
  have hself : coordinateReflection z' Finset.univ z' = z' := by
    ext i
    simp only [coordinateReflection, Finset.mem_univ, ite_true]
    ring
  have hpre : coordinateReflection mid Finset.univ ⁻¹'
      (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z' r hr : Set (SpatialCoordinates d)) := by
    simpa only [hmid] using coordinateReflection_preimage_cube mid Finset.univ z' hr
  have hpre' : coordinateReflection z' Finset.univ ⁻¹'
      (centeredCube z' r hr : Set (SpatialCoordinates d)) =
      (centeredCube z' r hr : Set (SpatialCoordinates d)) := by
    simpa only [hself] using coordinateReflection_preimage_cube z' Finset.univ z' hr
  have hcomp : coordinateReflection mid Finset.univ ∘ coordinateReflection z' Finset.univ =
      fun x : SpatialCoordinates d => x + z - z' := by
    funext x i
    simp only [Function.comp_apply, coordinateReflection, Finset.mem_univ, ite_true,
      Pi.add_apply, Pi.sub_apply, mid]
    ring
  rw [← hcomp]
  exact (coordinateReflection_domain_measurePreserving mid Finset.univ hpre).comp
    (coordinateReflection_domain_measurePreserving z' Finset.univ hpre')

theorem aux_thm_prop_cutoff_coeFn {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N z hr).val y =
        cutoffCoefficient model H x N y := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  filter_upwards [normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z r hr)
    (closedCube z r hr) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM model H x N z hr)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos model H x N z hr) 1 one_pos,
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hmem
  simpa only [div_one] using! hy hmem

theorem aux_thm_prop_field_translation_preserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (w : SpatialCoordinates d) :
    MeasurePreserving (aux_thm_prop_T (1 : Homogenization.Mat d) w)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
  have hI : IsSignedPermutationMatrix (1 : Homogenization.Mat d) := by
    refine ⟨Equiv.refl _, fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    intro i j
    simp only [Equiv.refl_apply, Matrix.one_apply]
    rfl
  exact ⟨Measurable.of_eval (fun j =>
    (aux_thm_prop_precomp_measurable 1 w).comp (measurable_pi_apply j)),
    aux_thm_prop_chaos_invariant model 1 hI w⟩

/-- The literal cutoff affine response on a translated cube has the common
infrared gauge factor, on one full event for every cutoff and affine slope. -/
theorem aux_thm_prop_cutoff_affine_translation {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (z z' : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' r hr),
      ‖(u : SobolevData (centeredCube z' r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' r hr)) u‖) :
    ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, ∀ N p,
      affineDirichletResponse (centeredCube_isBounded z' hr) hP'
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H
          (aux_thm_prop_T (1 : Homogenization.Mat d) (z - z') x) N z' hr) p =
      Real.exp (-(H x (z - z'))) *
        affineDirichletResponse (centeredCube_isBounded z hr) hP
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N z hr) p := by
  have hT := aux_thm_prop_field_translation_preserving model (z - z')
  filter_upwards [hH.2, hT.quasiMeasurePreserving.ae hH.2] with x hx hTx N p
  have hHx := aux_thm_prop_H_T (1 : Homogenization.Mat d) (z - z') H x hx hTx
  apply aux_thm_prop_affine_response_translation z z' r hr hP hP'
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N z hr)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H
      (aux_thm_prop_T (1 : Homogenization.Mat d) (z - z') x) N z' hr)
    _ (Real.exp_pos _) _ p
  have hmp := aux_thm_prop_cube_translation_preserving z z' hr
  filter_upwards [aux_thm_prop_cutoff_coeFn model H
      (aux_thm_prop_T (1 : Homogenization.Mat d) (z - z') x) N z' hr,
    hmp.quasiMeasurePreserving.ae (aux_thm_prop_cutoff_coeFn model H x N z hr)]
    with y hb ha
  rw [hb, ha, aux_thm_prop_cutoffCoefficient_T model 1 (z - z') H x hHx]
  have hId (v : SpatialCoordinates d) : matVecMul (1 : Homogenization.Mat d) v = v := Matrix.one_mulVec v
  simp only [aux_thm_prop_affineMap_apply, hId, zero_add, ← add_sub_assoc]

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper
noncomputable section

def aux_thm_prop_cutoff_trace {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ) (om : BilateralField d) : ℝ :=
  ∑ i : Fin d, affineDirichletResponse (centeredCube_isBounded z hr) hP
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z hr) (Pi.single i 1) /
    (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal

theorem aux_thm_prop_cutoff_trace_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖) (N : ℕ) :
    Measurable (aux_thm_prop_cutoff_trace model H z hr hP N) := by
  exact Finset.measurable_sum _ fun i _ =>
    (aux_thm_prop_affine_response_measurable model H hH N z hr hP (Pi.single i 1)).div_const _

theorem aux_thm_prop_cutoff_trace_limit {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ → ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hlim : aux_thm_prop_affine_converges model H om z r hr N hP A) :
    Tendsto (fun n => aux_thm_prop_cutoff_trace model H z hr hP (N n) om)
      atTop (𝓝 (Matrix.trace A)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ => hlim (Pi.single i 1))
  simpa only [aux_thm_prop_cutoff_trace, Matrix.trace, Matrix.diag,
    Matrix.mulVec_single_one, single_dotProduct, one_mul] using! h

theorem aux_thm_prop_cutoff_trace_translation {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (z z' : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' r hr),
      ‖(u : SobolevData (centeredCube z' r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' r hr)) u‖) :
    ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, ∀ N,
      aux_thm_prop_cutoff_trace model H z' hr hP' N
        (aux_thm_prop_T (1 : Homogenization.Mat d) (z - z') x) =
      Real.exp (-(H x (z - z'))) * aux_thm_prop_cutoff_trace model H z hr hP N x := by
  filter_upwards [aux_thm_prop_cutoff_affine_translation model H hH z z' hr hP hP']
    with x hx N
  simp only [aux_thm_prop_cutoff_trace, hx, centeredCube_volume, Finset.mul_sum,
    mul_div_assoc]

/-- Genuine affine response limits on any two cubes of the same radius have
the same expected trace ratio. The common infrared gauge cancels before taking
expectations; no spatial invariance of a chosen matrix representative is assumed. -/
theorem aux_thm_prop_expected_trace_ratio_translation {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d) (hfield : Measurable field)
    (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (z z' : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' r hr),
      ‖(u : SobolevData (centeredCube z' r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' r hr)) u‖)
    (NE NF : ℕ → ℕ) (AE AF BE BF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) z r hr NE hP (AE om))
    (hAF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) z r hr NF hP (AF om))
    (hBE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) z' r hr NE hP' (BE om))
    (hBF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) z' r hr NF hP' (BF om)) :
    (∫ om, Matrix.trace (BF om) / Matrix.trace (BE om) ∂P) =
      ∫ om, Matrix.trace (AF om) / Matrix.trace (AE om) ∂P := by
  apply aux_thm_prop_limit_ratio_integral P (chaosSampleLaw model).toMeasure field hfield hlaw
    (aux_thm_prop_T 1 (z - z')) (aux_thm_prop_field_translation_preserving model (z - z'))
    (fun n => aux_thm_prop_cutoff_trace model H z hr hP (NE n))
    (fun n => aux_thm_prop_cutoff_trace model H z hr hP (NF n))
    (fun n => aux_thm_prop_cutoff_trace model H z' hr hP' (NE n))
    (fun n => aux_thm_prop_cutoff_trace model H z' hr hP' (NF n))
    (fun n => aux_thm_prop_cutoff_trace_measurable model H hH.1 z hr hP (NE n))
    (fun n => aux_thm_prop_cutoff_trace_measurable model H hH.1 z hr hP (NF n))
    (fun n => aux_thm_prop_cutoff_trace_measurable model H hH.1 z' hr hP' (NE n))
    (fun n => aux_thm_prop_cutoff_trace_measurable model H hH.1 z' hr hP' (NF n))
    (fun om => Matrix.trace (AE om)) (fun om => Matrix.trace (AF om))
    (fun om => Matrix.trace (BE om)) (fun om => Matrix.trace (BF om))
    (hAE.mono fun om h => aux_thm_prop_cutoff_trace_limit model H (field om) z hr hP NE (AE om) h)
    (hAF.mono fun om h => aux_thm_prop_cutoff_trace_limit model H (field om) z hr hP NF (AF om) h)
    (hBE.mono fun om h => aux_thm_prop_cutoff_trace_limit model H (field om) z' hr hP' NE (BE om) h)
    (hBF.mono fun om h => aux_thm_prop_cutoff_trace_limit model H (field om) z' hr hP' NF (BF om) h)
    (fun x => Real.exp (-(H x (z - z'))))
  filter_upwards [aux_thm_prop_cutoff_trace_translation model H hH z z' hr hP hP'] with x hx
  exact ⟨(Real.exp_pos _).ne', fun n => ⟨hx (NE n), hx (NF n)⟩⟩

end
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_expected_trace_ratio_equal_radii {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d) (hfield : Measurable field)
    (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (z z' : SpatialCoordinates d) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (heq : r' = r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' r' hr'),
      ‖(u : SobolevData (centeredCube z' r' hr')).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' r' hr')) u‖)
    (NE NF : ℕ → ℕ) (AE AF BE BF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) z r hr NE hP (AE om))
    (hAF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) z r hr NF hP (AF om))
    (hBE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) z' r' hr' NE hP' (BE om))
    (hBF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) z' r' hr' NF hP' (BF om)) :
    (∫ om, Matrix.trace (BF om) / Matrix.trace (BE om) ∂P) =
      ∫ om, Matrix.trace (AF om) / Matrix.trace (AE om) ∂P := by
  subst r'
  exact aux_thm_prop_expected_trace_ratio_translation model H hH P field hfield hlaw
    z z' hr hP hP' NE NF AE AF BE BF hAE hAF hBE hBF

/-- The actual measurable matrix banks have one deterministic expected trace
ratio per cube radius. This derives the common spatial coefficient directly from
field stationarity and the response limits of the represented catalogue. -/
theorem aux_thm_prop_spatial_matrix_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hH : InfraredCharacterization model H)
    (field : Ω → BilateralField d) (hfield : Measurable field)
    (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖) :
    ∃ (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ),
      (∀ j om, (AE j om).transpose = AE j om) ∧
      (∀ j om, (AF j om).transpose = AF j om) ∧
      (∀ j i k, Measurable (fun om => AE j om i k)) ∧
      (∀ j i k, Measurable (fun om => AF j om i k)) ∧
      (∀ j, (∫ om, Matrix.trace (AF j om) / Matrix.trace (AE j om) ∂P) = ck (r j)) ∧
      ∀ᵐ om ∂P, ∀ j,
        aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
        aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om) := by
  classical
  obtain ⟨AE, AF, hEsym, hFsym, hEmeas, hFmeas, hconv⟩ :=
    aux_thm_prop_catalogue_measurable_affine_matrices d hd model H Ω P hH.1 field hfield
      z r hr Sspace NE NF alpha eta hCat hP
  have hequal (i j : ℕ) (hij : r j = r i) :
      (∫ om, Matrix.trace (AF j om) / Matrix.trace (AE j om) ∂P) =
      ∫ om, Matrix.trace (AF i om) / Matrix.trace (AE i om) ∂P := by
    have hE := hconv.mono fun om h => (h i).1
    have hF := hconv.mono fun om h => (h i).2
    exact aux_thm_prop_expected_trace_ratio_equal_radii model H hH P field hfield hlaw
      (z i) (z j) (hr i) (hr j) hij (hP i) (hP j) NE NF (AE i) (AF i) (AE j) (AF j)
      hE hF (hconv.mono fun om h => (h j).1) (hconv.mono fun om h => (h j).2)
  let ck : ℝ → ℝ := fun rr => if h : ∃ j, r j = rr then
    ∫ om, Matrix.trace (AF h.choose om) / Matrix.trace (AE h.choose om) ∂P else 0
  refine ⟨AE, AF, ck, hEsym, hFsym, hEmeas, hFmeas, ?_, hconv⟩
  intro j
  have hex : ∃ i, r i = r j := ⟨j, rfl⟩
  dsimp only [ck]
  rw [dite_eq_left hex]
  exact hequal hex.choose j hex.choose_spec.symm

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_cube_dilation {d : ℕ} (r : ℝ) (hr : 0 < r) :
    r • (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
  change r • Metric.ball (0 : SpatialCoordinates d) (1 / 2) = Metric.ball 0 (r / 2)
  rw [smul_ball hr.ne']
  simp [Real.norm_eq_abs, abs_of_pos hr, div_eq_mul_inv]

theorem aux_thm_prop_cube_translation {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    translateSet z (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  change dist (x - z) 0 < r / 2 ↔ dist x z < r / 2
  rw [dist_eq_norm, sub_zero, dist_eq_norm]

/-- Native and Hilbert-space affine minima coincide on the actual cube. -/
theorem aux_thm_prop_dirichlet_inf_eq_affine_response
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
theorem aux_thm_prop_dirichlet_inf_chart
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
  rw [aux_thm_prop_cube_dilation r hr,
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn_comp_add_right z
      (centeredCube (0 : SpatialCoordinates d) r hr).isOpen.measurableSet
      (fun x => (hbpos x).le), aux_thm_prop_cube_translation z r hr] at hs
  simpa only [add_comm] using hs

/-- Pull back an actual coefficient representative to its unit-cube chart. -/
theorem aux_thm_prop_ae_cube_chart
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {P : SpatialCoordinates d → Prop}
    (hP : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), P x) :
    ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      P (z + r • x) := by
  have ht : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)), P (x + z) := by
    apply (measurePreserving_addRight_restrict_translateSet z _).quasiMeasurePreserving.ae
    simpa only [aux_thm_prop_cube_translation z r hr] using hP
  have hs : ∀ᵐ x ∂volume.restrict
      (r • (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      P (x + z) := by
    simpa only [aux_thm_prop_cube_dilation r hr] using ht
  have hdil : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      P (r • x + z) := by
    apply ae_of_ae_map (p := fun x => P (x + z)) (measurable_const_smul r).aemeasurable
    rw [map_smul_volume_restrict hr]
    exact Measure.ae_smul_measure hs _
  simpa only [add_comm] using hdil

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise

namespace SubdiffusiveProcess.Paper

/-- The standing coefficient chart's matrix is the literal volume-normalized
affine Dirichlet response on the physical cube. -/
theorem aux_thm_prop_chart_matrix_response
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
    filter_upwards [hchart, aux_thm_prop_ae_cube_chart z r hr hab] with x hc hx
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
  rw [aux_thm_prop_dirichlet_inf_chart z r hr b hbpos p,
    aux_thm_prop_dirichlet_inf_eq_affine_response z r hr hP a b hb hbpos hab p,
    centeredCube_volume_real, div_eq_inv_mul]

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- A bound on the actual inverse multiscale ellipticity controls every
affine slope. It uses the dual coarse matrix and its genuine matrix inverse. -/
theorem aux_thm_prop_coarse_affine_coercivity
    {d : ℕ} [NeZero d] (A : Book.Ch02.TriadicCoeffFamily d)
    (s K : ℝ) (hs : 0 < s)
    (hK : (Book.Ch02.lambdaSq (originCube d 0) s (.finite 2) A)⁻¹ ≤ K)
    (p : SpatialCoordinates d) :
    p ⬝ᵥ p ≤ K * (p ⬝ᵥ (Book.Ch02.sigmaCoarse
      (Book.Ch02.cubeDomain (originCube d 0)) (A.coeffOn (originCube d 0))).mulVec p) := by
  let U := Book.Ch02.cubeDomain (originCube d 0)
  let a := A.coeffOn (originCube d 0)
  have hNorm := (Book.Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv
    (originCube d 0) A hs (by norm_num : (1 : ℝ) ≤ 2)).trans hK
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
    (Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg (originCube d 0) A).trans hNorm
  exact hcoer.trans ((mul_le_mul_of_nonneg_right hNorm hpos).trans
    (mul_le_mul_of_nonneg_left hle hK0))

theorem aux_thm_prop_affine_response_coercivity
    {d : ℕ} [NeZero d] (I : in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : SpatialCoordinates d → ℝ) (hb : Continuous b) (hbpos : ∀ x, 0 < b x)
    (hab : a.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] b)
    (s K : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hK : (I.lam z r hr a z r s 2)⁻¹ ≤ K) (p : SpatialCoordinates d) :
    p ⬝ᵥ p ≤ K * (affineDirichletResponse (centeredCube_isBounded z hr) hP a p /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hlam := I.lam_eq z r hr a z r hr subset_rfl s hs 2 (by norm_num)
  simp only [ENNReal.ofNat_ne_top, ↓reduceIte, ENNReal.toReal_ofNat] at hlam
  rw [hlam] at hK
  have h := aux_thm_prop_coarse_affine_coercivity (I.chart z r hr a z r) s K hs.1 hK p
  rw [aux_thm_prop_chart_matrix_response I z r hr hP a b hb hbpos hab p] at h
  exact h

/-- Uniform finite-response coercivity survives the represented limit. -/
theorem aux_thm_prop_limit_trace_positive
    {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℝ)
    (K : ℝ) (hK : 0 < K) (R : ℕ → (Fin d → ℝ) → ℝ)
    (hR : ∀ n p, p ⬝ᵥ p ≤ K * R n p)
    (hlim : ∀ p, Tendsto (fun n => R n p) atTop (𝓝 (p ⬝ᵥ A.mulVec p))) :
    (∀ p, p ⬝ᵥ p ≤ K * (p ⬝ᵥ A.mulVec p)) ∧ 0 < Matrix.trace A := by
  have hc (p : Fin d → ℝ) : p ⬝ᵥ p ≤ K * (p ⬝ᵥ A.mulVec p) :=
    ge_of_tendsto' ((hlim p).const_mul K) (fun n => hR n p)
  refine ⟨hc, ?_⟩
  have hdiag (i : Fin d) : 0 < A i i := by
    have h := hc (Pi.single i 1)
    simp only [Matrix.mulVec_single_one, single_dotProduct, Pi.single_eq_same, one_mul] at h
    exact (mul_pos_iff_of_pos_left hK).mp (zero_lt_one.trans_le h)
  exact Finset.sum_pos (fun i _ => hdiag i) Finset.univ_nonempty

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The actual represented inverse-ellipticity bank makes every limiting
normalized affine matrix coercive, hence gives a strictly positive trace. -/
theorem aux_thm_prop_represented_trace_positive
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (om : Ω) (hom : om ∈ G) (j : J)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hlim : ∀ p : Fin d → ℝ,
      Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)) p /
        (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ A.mulVec p))) :
    (∃ K : ℝ, 0 < K ∧ ∀ p : Fin d → ℝ, p ⬝ᵥ p ≤ K * (p ⬝ᵥ A.mulVec p)) ∧
      0 < Matrix.trace A := by
  let : NeZero d := ⟨by omega⟩
  rcases hRep with ⟨hA, hAlpha, hBeta, hC, hOrders, hN, hIR, hMeas, hLaw, hSeq,
    hcontain, hrat, htri, hcomplete, hgrat, hcover, hS, hDense, hSrc, hSrcDense,
    hTrace, hSt, hParent, hTDense, hPlateau, hMeasc, hMom, hNonneg, hSol, hCoeff,
    hCoerc, hExt, hGrid, hSrcEst, hCellEst⟩
  obtain ⟨B, hB⟩ := hSeq.2.2.2.2 (lambdaKey j) om hom
  let K : ℝ := max B 0 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hs : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [hBeta.1, hBeta.2, hAlpha.1]
  have hbound (n : ℕ) :
      (E.lam (z j) (r j) (hr j)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2)⁻¹ ≤ K := by
    have heq := (hCoeff j n om hom).2
    rw [Real.rpow_neg_one] at heq
    rw [← heq]
    exact (le_abs_self _).trans ((hB n).trans (by dsimp [K]; linarith [le_max_left B 0]))
  have h := aux_thm_prop_limit_trace_positive A K hK
    (fun n p => affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)) p /
      (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
    (fun n p => aux_thm_prop_affine_response_coercivity E (z j) (r j) (hr j) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
      (cutoffCoefficient M H (env n om) (cutoff n))
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (env n om) (cutoff n))
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (env n om) (cutoff n))
      (aux_lem_replace_large_cube_cutoff_positive_coe M H (env n om) (cutoff n) (z j) (hr j))
      ((beta - 1 / 2) / 4) K hs (hbound n) p) hlim
  exact ⟨⟨K, hK, h.1⟩, h.2⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Both actual matrix banks have strictly positive traces on one common full event. -/
theorem aux_thm_prop_catalogue_trace_positive
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hconv : ∀ᵐ om ∂P, ∀ j,
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om)) :
    ∀ᵐ om ∂P, ∀ j, 0 < Matrix.trace (AE j om) ∧ 0 < Matrix.trace (AF j om) := by
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF,
    root, _hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
    cellHolderKey, origin, gridRoot, gridKey, hRepE, hRepF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  have he : ∀ᵐ om ∂P, om ∈ eventE :=
    ae_iff.mpr hRepE.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hf : ∀ᵐ om ∂P, om ∈ eventF :=
    ae_iff.mpr hRepF.2.2.2.2.2.2.2.2.2.1.2.2.1
  filter_upwards [he, hf, hconv] with om he hf hc j
  constructor
  · exact (aux_thm_prop_represented_trace_positive d hd model H Ω P
      NE (fun _ om => field om) ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NE n) (field om)) responseE
      (fun i n om => catalogConstant i (NE n) (field om)) eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepE
      om he j (hP j) (AE j om) (hc j).1).2
  · exact (aux_thm_prop_represented_trace_positive d hd model H Ω P
      NF (fun _ om => field om) ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NF n) (field om)) responseF
      (fun i n om => catalogConstant i (NF n) (field om)) eventF
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepF
      om hf j (hP j) (AF j om) (hc j).2).2

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Genuine matrix order and a positive denominator bound the actual expected
trace ratio; measurability is supplied entry by entry by the matrix bank. -/
theorem aux_thm_prop_expected_trace_ratio_bounds
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ i j, Measurable (fun om => AE om i j))
    (hAF : ∀ i j, Measurable (fun om => AF om i j))
    (m M : ℝ)
    (htrace : ∀ᵐ om ∂P, 0 < Matrix.trace (AE om))
    (horder : ∀ᵐ om ∂P, ∀ p : Fin d → ℝ,
      m * (p ⬝ᵥ (AE om).mulVec p) ≤ p ⬝ᵥ (AF om).mulVec p ∧
      p ⬝ᵥ (AF om).mulVec p ≤ M * (p ⬝ᵥ (AE om).mulVec p)) :
    Integrable (fun om => Matrix.trace (AF om) / Matrix.trace (AE om)) P ∧
      (∫ om, Matrix.trace (AF om) / Matrix.trace (AE om) ∂P) ∈ Icc m M := by
  have he : Measurable (fun om => Matrix.trace (AE om)) :=
    Finset.measurable_sum _ (fun i _ => hAE i i)
  have hf : Measurable (fun om => Matrix.trace (AF om)) :=
    Finset.measurable_sum _ (fun i _ => hAF i i)
  have hb : ∀ᵐ om ∂P, Matrix.trace (AF om) / Matrix.trace (AE om) ∈ Icc m M := by
    filter_upwards [htrace, horder] with om htr hord
    exact aux_thm_prop_trace_ratio_bounds (AE om) (AF om) m M htr hord
  have hi : Integrable (fun om => Matrix.trace (AF om) / Matrix.trace (AE om)) P := by
    apply (integrable_const (max |m| |M|)).mono' (hf.div he).aestronglyMeasurable
    filter_upwards [hb] with om hom
    simp only [Real.norm_eq_abs, Pi.div_apply]
    exact abs_le.mpr ⟨by linarith [hom.1, neg_abs_le m, le_max_left |m| |M|],
      hom.2.trans ((le_abs_self M).trans (le_max_right |m| |M|))⟩
  refine ⟨hi, ?_, ?_⟩
  · simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono_ae (integrable_const m) hi (hb.mono fun _ h => h.1)
  · simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono_ae hi (integrable_const M) (hb.mono fun _ h => h.2)

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper
section Standing

variable {d : ℕ} {hd : 2 ≤ d}
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

include BD BDQ EM hcontract


theorem aux_thm_prop_represented_affine_glb_on_padded_cube
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders I Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (om : Ω) (hom : om ∈ G) (jQ : J)
    (rq : ℝ) (hrq : 0 < rq) (h3rq : 0 < 3 * rq) (hrQ : r jQ = 3 * rq)
    (jC : J) (hzC : z jC = z jQ) (hrC : r jC = rq)
    (Rp : ℝ) (hRp : 0 < Rp) (hRp_eq : Rp = 3 * rq)
    (SP : ResponseSpace (centeredCube (z jQ) Rp hRp))
    (hSP : SP.space = killedSobolevGraph (centeredCube (z jQ) Rp hRp))
    (Controls : aux_thm_prop_analytic_controls d hd (z jQ) Rp hRp SP
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z jQ) hRp))
    (GN : ℕ → DomainL2 (centeredCube (z jQ) Rp hRp) →L[ℝ]
      DomainL2 (centeredCube (z jQ) Rp hRp))
    (Glim : DomainL2 (centeredCube (z jQ) Rp hRp) →L[ℝ]
      DomainL2 (centeredCube (z jQ) Rp hRp))
    (hGN : ∀ n f, GN n f =
      (responseSolution SP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z jQ) hRp)
        ((sobolevVolumeLoad f).comp SP.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 Glim))
    (F : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube (z jQ) Rp hRp : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (hF : ∀ v, F.energy v = limitFormEnergy Glim v)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube (z jQ) Rp hRp : Set (SpatialCoordinates d)) C)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z jQ) rq hrq),
      ‖(u : SobolevData (centeredCube (z jQ) rq hrq)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z jQ) rq hrq)) u‖)
    (Amat : Matrix (Fin d) (Fin d) ℝ)
    (hAffine : ∀ p : Fin d → ℝ,
      Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded (z jQ) hrq) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z jQ) hrq) p /
        (volume (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ Amat.mulVec p))) :
    ∀ (p : Fin d → ℝ) (c : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) Rp hRp)
        F.toClosedForm Gamma (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c))
        ((volume (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ Amat.mulVec p)) ∧
      (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) Rp hRp)
        F.toClosedForm Gamma (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c)).Nonempty := by
  subst Rp
  exact aux_thm_prop_represented_affine_glb BD BDQ EM hcontract M H Ω P cutoff env
    J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders I
    Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey
    sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
    Grid origin gridRoot gridKey hRep om hom jQ rq hrq h3rq hrQ jC hzC hrC
    SP hSP Controls GN Glim hGN hConv F Gamma hF hcore hP Amat hAffine

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_catalogue_affine_minima
    (d : ℕ) (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hconv : ∀ᵐ om ∂P, ∀ j,
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om)) :
    ∀ᵐ om ∂P, ∀ jQ jC, z jC = z jQ → r jQ = 3 * r jC →
      (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
          (Sspace jQ) (GE jQ om) NE, ∀ (p : Fin d → ℝ) (c : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c))
          ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
            (p ⬝ᵥ (AE jC om).mulVec p)) ∧
        (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c)).Nonempty) ∧
      (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
          (Sspace jQ) (GF jQ om) NF, ∀ (p : Fin d → ℝ) (c : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c))
          ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
            (p ⬝ᵥ (AF jC om).mulVec p)) ∧
        (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c)).Nonempty) := by
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF,
    root, _hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
    cellHolderKey, origin, gridRoot, gridKey, hRepE, hRepF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  have he : ∀ᵐ om ∂P, om ∈ eventE :=
    ae_iff.mpr hRepE.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hf : ∀ᵐ om ∂P, om ∈ eventF :=
    ae_iff.mpr hRepF.2.2.2.2.2.2.2.2.2.1.2.2.1
  filter_upwards [he, hf, hconv] with om home homf hc jQ jC hzC hrQ
  have hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z jQ) (r jC) (hr jC)),
      ‖(u : SobolevData (centeredCube (z jQ) (r jC) (hr jC))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z jQ) (r jC) (hr jC))) u‖ := by
    exact killedPoincare_domain_eq (by simp only [centeredCube, hzC]) (hP jC)
  constructor
  · intro A p c
    obtain ⟨controls⟩ := aux_thm_prop_controls_of_bounds hd model H (field om)
      (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GE jQ om) NE A.bounds
    have hAff' : aux_thm_prop_affine_converges model H (field om) (z jQ) (r jC) (hr jC)
        NE hP' (AE jC om) := by
      simpa only [hzC] using (hc jC).1
    have hmin := aux_thm_prop_represented_affine_glb_on_padded_cube BD BDQ EM hcontract
      model H Ω P NE (fun _ om => field om) ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NE n) (field om)) responseE
      (fun i n om => catalogConstant i (NE n) (field om)) eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepE
      om home jQ (r jC) (hr jC) (mul_pos (by norm_num) (hr jC)) hrQ jC hzC rfl
      (r jQ) (hr jQ) hrQ (Sspace jQ) (hRepE.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 jQ)
      controls A.response (GE jQ om) A.response_eq A.response_tendsto A.form A.gamma
      A.energy_eq A.core hP' (AE jC om) hAff' p c
    simpa only [hzC] using hmin
  · intro A p c
    obtain ⟨controls⟩ := aux_thm_prop_controls_of_bounds hd model H (field om)
      (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GF jQ om) NF A.bounds
    have hAff' : aux_thm_prop_affine_converges model H (field om) (z jQ) (r jC) (hr jC)
        NF hP' (AF jC om) := by
      simpa only [hzC] using (hc jC).2
    have hmin := aux_thm_prop_represented_affine_glb_on_padded_cube BD BDQ EM hcontract
      model H Ω P NF (fun _ om => field om) ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NF n) (field om)) responseF
      (fun i n om => catalogConstant i (NF n) (field om)) eventF
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepF
      om homf jQ (r jC) (hr jC) (mul_pos (by norm_num) (hr jC)) hrQ jC hzC rfl
      (r jQ) (hr jQ) hrQ (Sspace jQ) (hRepF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 jQ)
      controls A.response (GF jQ om) A.response_eq A.response_tendsto A.form A.gamma
      A.energy_eq A.core hP' (AF jC om) hAff' p c
    simpa only [hzC] using hmin

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_catalogue_matrix_order
    (d : ℕ) (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hconv : ∀ᵐ om ∂P, ∀ j,
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om))
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hside : ∀ᵐ om ∂P, ∀ j,
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GE j om) NE) ∧
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GF j om) NF))
    (horder : ∀ᵐ om ∂P, ∀ j,
      limitFormDomain (GE j om) = limitFormDomain (GF j om) ∧
      ∀ u ∈ limitFormDomain (GE j om),
        m * (limitFormEnergy (GE j om) u).toReal ≤ (limitFormEnergy (GF j om) u).toReal ∧
        (limitFormEnergy (GF j om) u).toReal ≤ M * (limitFormEnergy (GE j om) u).toReal) :
    ∀ᵐ om ∂P, ∀ jQ jC, z jC = z jQ → r jQ = 3 * r jC → ∀ p : Fin d → ℝ,
      m * (p ⬝ᵥ (AE jC om).mulVec p) ≤ p ⬝ᵥ (AF jC om).mulVec p ∧
      p ⬝ᵥ (AF jC om).mulVec p ≤ M * (p ⬝ᵥ (AE jC om).mulVec p) := by
  have hmin := aux_thm_prop_catalogue_affine_minima d hd BD BDQ EM hcontract model H Ω P
    field z r hr Sspace GE GF NE NF alpha eta hCat hP AE AF hconv
  filter_upwards [hmin, hside, horder] with om hmin hs ho jQ jC hzC hrQ
  obtain ⟨E⟩ := (hs jQ).1
  obtain ⟨F⟩ := (hs jQ).2
  have hedom := aux_thm_prop_domain_eq_of_energy E.form.toClosedForm (GE jQ om) E.energy_eq
  have hfdom := aux_thm_prop_domain_eq_of_energy F.form.toClosedForm (GF jQ om) F.energy_eq
  have hdom : E.form.domain = F.form.domain := by
    apply SetLike.coe_injective
    exact hedom.trans ((ho jQ).1.trans hfdom.symm)
  have he := aux_thm_prop_form_eq_toReal_energy E.form.toClosedForm (GE jQ om) E.energy_eq
  have hf := aux_thm_prop_form_eq_toReal_energy F.form.toClosedForm (GF jQ om) F.energy_eq
  have hforms : ∀ u ∈ E.form.domain,
      m * E.form.form u u ≤ F.form.form u u ∧ F.form.form u u ≤ M * E.form.form u u := by
    intro u hu
    rw [he u hu, hf u (hdom ▸ hu)]
    exact (ho jQ).2 u (hedom ▸ hu)
  have hvol : 0 < (volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal :=
    centeredCube_volume_pos (z jC) (hr jC)
  exact aux_thm_prop_affine_matrix_order (centeredCube (z jQ) (r jQ) (hr jQ))
    E.form F.form hdom E.core F.core E.gamma F.gamma m M hm hM hforms
    (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
    (centeredCube (z jC) (r jC) (hr jC)).isOpen.measurableSet hvol (AE jC om) (AF jC om)
    (fun p => by simpa only [add_zero] using ((hmin jQ jC hzC hrQ).1 E p 0).1)
    (fun p => by simpa only [add_zero] using ((hmin jQ jC hzC hrQ).2 F p 0).1)

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_ordered_spatial_matrix_bank
    (d : ℕ) (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (hH : InfraredCharacterization model H)
    (hfield : Measurable field)
    (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hside : ∀ᵐ om ∂P, ∀ j,
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GE j om) NE) ∧
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GF j om) NF))
    (horder : ∀ᵐ om ∂P, ∀ j,
      limitFormDomain (GE j om) = limitFormDomain (GF j om) ∧
      ∀ u ∈ limitFormDomain (GE j om),
        m * (limitFormEnergy (GE j om) u).toReal ≤ (limitFormEnergy (GF j om) u).toReal ∧
        (limitFormEnergy (GF j om) u).toReal ≤ M * (limitFormEnergy (GE j om) u).toReal) :
    ∃ (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖),
    ∃ (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ),
      (∀ j om, (AE j om).transpose = AE j om) ∧
      (∀ j om, (AF j om).transpose = AF j om) ∧
      (∀ j i k, Measurable (fun om => AE j om i k)) ∧
      (∀ j i k, Measurable (fun om => AF j om i k)) ∧
      (∀ j, (∫ om, Matrix.trace (AF j om) / Matrix.trace (AE j om) ∂P) = ck (r j)) ∧
      (∀ j, (∃ jQ, z j = z jQ ∧ r jQ = 3 * r j) →
        Integrable (fun om => Matrix.trace (AF j om) / Matrix.trace (AE j om)) P ∧
          ck (r j) ∈ Icc m M) ∧
      ∀ᵐ om ∂P,
        (∀ j,
          aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
          aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om) ∧
          0 < Matrix.trace (AE j om) ∧ 0 < Matrix.trace (AF j om)) ∧
        (∀ jQ j, z j = z jQ → r jQ = 3 * r j → ∀ p : Fin d → ℝ,
          m * (p ⬝ᵥ (AE j om).mulVec p) ≤ p ⬝ᵥ (AF j om).mulVec p ∧
          p ⬝ᵥ (AF j om).mulVec p ≤ M * (p ⬝ᵥ (AE j om).mulVec p)) := by
  have : NeZero d := ⟨by omega⟩
  have hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖ := by
    intro j
    exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (z j) (r j) (hr j))
      (isOpenBoundedConvexDomain_centeredCube (z j) (hr j))).1
  obtain ⟨AE, AF, ck, hEsym, hFsym, hEmeas, hFmeas, hck, hconv⟩ :=
    aux_thm_prop_spatial_matrix_bank d hd model H Ω P hH field hfield hlaw
      z r hr Sspace NE NF alpha eta hCat hP
  have htr := aux_thm_prop_catalogue_trace_positive d hd model H Ω P field
    z r hr Sspace NE NF alpha eta hCat hP AE AF hconv
  have hord := aux_thm_prop_catalogue_matrix_order d hd BD BDQ EM hcontract model H Ω P
    field z r hr Sspace GE GF NE NF alpha eta hCat hP AE AF hconv m M hm hM hside horder
  refine ⟨hP, AE, AF, ck, hEsym, hFsym, hEmeas, hFmeas, hck, ?_, ?_⟩
  · intro j hj
    obtain ⟨jQ, hzQ, hrQ⟩ := hj
    have hb := aux_thm_prop_expected_trace_ratio_bounds P (AE j) (AF j) (hEmeas j) (hFmeas j)
      m M (htr.mono fun om h => (h j).1) (hord.mono fun om h => h jQ j hzQ hrQ)
    exact ⟨hb.1, hck j ▸ hb.2⟩
  · filter_upwards [hconv, htr, hord] with om hc ht ho
    exact ⟨fun j => ⟨(hc j).1, (hc j).2, (ht j).1, (ht j).2⟩, ho⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology

namespace SubdiffusiveProcess.Paper

/-- Every rational centre inside the bounded root has both its observation
cube and its padded cube in the catalogue at all sufficiently fine scales. -/
theorem aux_thm_prop_fine_padded_indices
    {d : ℕ} {J : Type} (j0 : J) (z : J → SpatialCoordinates d) (r : J → ℝ)
    (hr : ∀ j, 0 < r j)
    (hcomplete : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      (∀ i, ∃ q : ℚ, zc i = (q : ℝ)) → (∃ k : ℤ, rc = (3 : ℝ) ^ k) →
      (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) →
      ∃ j, z j = zc ∧ r j = rc)
    (zc : SpatialCoordinates d) (hrat : ∀ i, ∃ q : ℚ, zc i = (q : ℝ))
    (hinside : zc ∈ (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d))) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ jC jP : J,
      z jC = zc ∧ r jC = (3 : ℝ) ^ (-(k : ℝ)) ∧
      z jP = zc ∧ r jP = 3 * (3 : ℝ) ^ (-(k : ℝ)) := by
  have hdist : dist zc (z j0) < r j0 / 2 := hinside
  have htol : 0 < r j0 / 2 - dist zc (z j0) := sub_pos.mpr hdist
  have ht : Tendsto (fun k : ℕ => (3 : ℝ) ^ (-(k : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_atBot_of_base_gt_one 3 (by norm_num)).comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have ht' : Tendsto (fun k : ℕ => 3 * (3 : ℝ) ^ (-(k : ℝ)) / 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (ht.const_mul 3).div_const 2
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp (ht'.eventually (gt_mem_nhds htol))
  refine ⟨k0, ?_⟩
  intro k hk
  have hs : 0 < (3 : ℝ) ^ (-(k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hsP : 0 < 3 * (3 : ℝ) ^ (-(k : ℝ)) := mul_pos (by norm_num) hs
  have hsubP : (centeredCube zc (3 * (3 : ℝ) ^ (-(k : ℝ))) hsP : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) := by
    exact Metric.ball_subset_ball' (by linarith [hk0 k hk])
  have hsubC : (centeredCube zc ((3 : ℝ) ^ (-(k : ℝ))) hs : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) :=
    (Metric.ball_subset_ball (by linarith : (3 : ℝ) ^ (-(k : ℝ)) / 2 ≤
      3 * (3 : ℝ) ^ (-(k : ℝ)) / 2)).trans hsubP
  have htriC : (3 : ℝ) ^ (-(k : ℝ)) = (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, _root_.zpow_neg, zpow_natCast]
  have htriP : 3 * (3 : ℝ) ^ (-(k : ℝ)) = (3 : ℝ) ^ (1 - (k : ℤ)) := by
    rw [htriC, sub_eq_add_neg, zpow_add₀ (by norm_num)]
    norm_num
  obtain ⟨jC, hjC⟩ := hcomplete zc _ hs hrat ⟨-(k : ℤ), htriC⟩ hsubC
  obtain ⟨jP, hjP⟩ := hcomplete zc _ hsP hrat ⟨1 - (k : ℤ), htriP⟩ hsubP
  exact ⟨jC, jP, hjC.1, hjC.2, hjP.1, hjP.2⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology

namespace SubdiffusiveProcess.Paper

/-- A bounded catalogue supplies the actual deterministic trace-ratio bounds
at every sufficiently fine scale. The finite initial range needs no padded cell. -/
theorem aux_thm_prop_fine_trace_bounds
    {d : ℕ} {J : Type} (j0 : J) (z : J → SpatialCoordinates d) (r : J → ℝ)
    (hr : ∀ j, 0 < r j)
    (hrat : ∀ i, ∃ q : ℚ, z j0 i = (q : ℝ))
    (hcomplete : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      (∀ i, ∃ q : ℚ, zc i = (q : ℝ)) → (∃ k : ℤ, rc = (3 : ℝ) ^ k) →
      (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) →
      ∃ j, z j = zc ∧ r j = rc)
    (ck : ℝ → ℝ) (m M : ℝ)
    (hck : ∀ j, (∃ jQ, z j = z jQ ∧ r jQ = 3 * r j) → ck (r j) ∈ Icc m M) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ck ((3 : ℝ) ^ (-(k : ℝ))) ∈ Icc m M := by
  obtain ⟨k0, hk0⟩ := aux_thm_prop_fine_padded_indices j0 z r hr hcomplete (z j0) hrat
    (Metric.mem_ball_self (by linarith [hr j0]))
  refine ⟨k0, ?_⟩
  intro k hk
  obtain ⟨jC, jP, hzC, hrC, hzP, hrP⟩ := hk0 k hk
  have hbound := hck jC ⟨jP, hzC.trans hzP.symm, by rw [hrP, hrC]⟩
  simpa only [hrC] using hbound

/-- Clamp only the uncontrolled initial values of the actual deterministic
sequence; all sufficiently fine values and both density alternatives are kept. -/
theorem aux_thm_prop_fine_coefficient_sequence
    (ck : ℝ → ℝ) (m M : ℝ) (hmM : m ≤ M)
    (k0 : ℕ) (hck : ∀ k : ℕ, k0 ≤ k → ck ((3 : ℝ) ^ (-(k : ℝ))) ∈ Icc m M)
    (H1 : ℕ) :
    ∃ cseq : ℕ → ℝ,
      (∀ k, cseq k ∈ Icc m M) ∧
      (∀ k, k0 ≤ k → cseq k = ck ((3 : ℝ) ^ (-(k : ℝ)))) ∧
      ((1 / 2 : ℝ) ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity (fun n => cseq (H1 * n) ≤ (m + M) / 2) ∨
        (1 / 2 : ℝ) ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity (fun n => ¬ cseq (H1 * n) ≤ (m + M) / 2)) := by
  let cseq : ℕ → ℝ := fun k => max m (min M (ck ((3 : ℝ) ^ (-(k : ℝ)))))
  refine ⟨cseq, ?_, ?_, aux_thm_prop_half_density _⟩
  · intro k
    exact ⟨le_max_left _ _, max_le hmM (min_le_left _ _)⟩
  · intro k hk
    exact (congrArg (max m) (min_eq_right (hck k hk).2)).trans
      (max_eq_right (hck k hk).1)

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
section Standing

variable {d : ℕ} {hd : 2 ≤ d}
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

include BD BDQ EM hcontract

/-- Two actual represented sides have the same continuous boundary-energy
classes on an interior cell when the ambient cube is restricted. -/
theorem aux_thm_prop_side_boundary_restriction
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ → ℕ)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR))
    (Sq : ResponseSpace (centeredCube zq r hr))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr))
    (GQ : DomainL2 (centeredCube zQ R hR) →L[ℝ] DomainL2 (centeredCube zQ R hR))
    (Gq : DomainL2 (centeredCube zq r hr) →L[ℝ] DomainL2 (centeredCube zq r hr))
    (A : aux_thm_prop_limit_side d hd model H om zQ R hR SQ GQ N)
    (B : aux_thm_prop_limit_side d hd model H om zq r hr Sq Gq N)
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc)
    (hcell : closure (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ⊆
      (centeredCube zq r hr : Set (SpatialCoordinates d))) :
    ∀ b : SpatialCoordinates d → ℝ,
      aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) A.form.toClosedForm A.gamma
        (centeredCube zc rc hrc : Set (SpatialCoordinates d)) b =
      aux_thm_prop_boundary_energy_set (centeredCube zq r hr) B.form.toClosedForm B.gamma
        (centeredCube zc rc hrc : Set (SpatialCoordinates d)) b := by
  obtain ⟨AQ⟩ := aux_thm_prop_controls_of_bounds hd model H om zQ R hR SQ GQ N A.bounds
  obtain ⟨Aq⟩ := aux_thm_prop_controls_of_bounds hd model H om zq r hr Sq Gq N B.bounds
  have hcoeff (n : ℕ) :
      ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) zQ hR).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube zq r hr : Set (SpatialCoordinates d))]
      ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) zq hr).val : SpatialCoordinates d → ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hqQ
      (aux_lem_replace_large_cube_cutoff_positive_coe model H om (N n) zQ hR),
      aux_lem_replace_large_cube_cutoff_positive_coe model H om (N n) zq hr] with x hQ hq
    exact hQ.trans hq.symm
  exact aux_thm_prop_controlled_boundary_restriction BD BDQ EM hcontract
    zQ zq R r hR hr hqQ SQ Sq hSQ hSq
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) zQ hR)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) zq hr) hcoeff
    A.form B.form AQ Aq A.response B.response GQ Gq A.response_eq B.response_eq
    A.response_tendsto B.response_tendsto A.energy_eq B.energy_eq B.core A.core
    A.gamma B.gamma zc rc hrc hcell

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_catalogue_ambient_affine_minima
    (d : ℕ) (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hconv : ∀ᵐ om ∂P, ∀ j,
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om))
    (hside : ∀ᵐ om ∂P, ∀ j,
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GE j om) NE) ∧
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GF j om) NF)) :
    ∀ᵐ om ∂P, ∀ jQ jP jC, z jC = z jP → r jP = 3 * r jC →
      (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
          (Sspace jQ) (GE jQ om) NE, ∀ (p : Fin d → ℝ) (c : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c))
          ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
            (p ⬝ᵥ (AE jC om).mulVec p)) ∧
        (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c)).Nonempty) ∧
      (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
          (Sspace jQ) (GF jQ om) NF, ∀ (p : Fin d → ℝ) (c : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c))
          ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
            (p ⬝ᵥ (AF jC om).mulVec p)) ∧
        (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c)).Nonempty) := by
  have hmin := aux_thm_prop_catalogue_affine_minima d hd BD BDQ EM hcontract model H Ω P
    field z r hr Sspace GE GF NE NF alpha eta hCat hP AE AF hconv
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF,
    root, _hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
    cellHolderKey, origin, gridRoot, gridKey, hRepE, hRepF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  have hSpaces := hRepE.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [hmin, hside] with om hmin hs jQ jP jC hzC hrP hsub
  have hcell : closure (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) := by
    intro x hx
    have hdist : dist x (z jC) ≤ r jC / 2 := Metric.closure_ball_subset_closedBall hx
    change dist x (z jP) < r jP / 2
    rw [← hzC, hrP]
    linarith [hr jC]
  constructor
  · intro A p c
    obtain ⟨B⟩ := (hs jP).1
    have htransfer := aux_thm_prop_side_boundary_restriction BD BDQ EM hcontract
      model H (field om) NE (z jQ) (z jP) (r jQ) (r jP) (hr jQ) (hr jP) hsub
      (Sspace jQ) (Sspace jP) (hSpaces jQ) (hSpaces jP) (GE jQ om) (GE jP om)
      A B (z jC) (r jC) (hr jC) hcell (fun x => (∑ i, p i * x i) + c)
    rw [htransfer]
    exact (hmin jP jC hzC hrP).1 B p c
  · intro A p c
    obtain ⟨B⟩ := (hs jP).2
    have htransfer := aux_thm_prop_side_boundary_restriction BD BDQ EM hcontract
      model H (field om) NF (z jQ) (z jP) (r jQ) (r jP) (hr jQ) (hr jP) hsub
      (Sspace jQ) (Sspace jP) (hSpaces jQ) (hSpaces jP) (GF jQ om) (GF jP om)
      A B (z jC) (r jC) (hr jC) hcell (fun x => (∑ i, p i * x i) + c)
    rw [htransfer]
    exact (hmin jP jC hzC hrP).2 B p c

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The mass-grid radius is a literal triadic radius, including level zero. -/
theorem aux_thm_prop_mass_side_zpow (H1 n : ℕ) :
    aux_thm_prop_mass_side H1 n = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)) := by
  unfold aux_thm_prop_mass_side
  rw [← Real.rpow_natCast (3 : ℝ) H1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hexp : (H1 : ℝ) * -(n : ℝ) = -((H1 * n : ℕ) : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast,
    _root_.zpow_neg, zpow_natCast]

/-- Rational shifts and triadic radii give rational cell centres. -/
theorem aux_thm_prop_mass_center_rational {d : ℕ} (H1 Mm n : ℕ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) :
    ∀ i, ∃ q : ℚ, aux_thm_prop_mass_center H1 Mm sigma n k i = (q : ℝ) := by
  intro i
  refine ⟨((sigma i).val : ℚ) / (Mm : ℚ) +
    (3 : ℚ) ^ (-((H1 * n : ℕ) : ℤ)) * (k i : ℚ) +
      (3 : ℚ) ^ (-((H1 * n : ℕ) : ℤ)) / 2, ?_⟩
  simp only [aux_thm_prop_mass_center, aux_thm_prop_mass_lo,
    aux_thm_prop_mass_shift, aux_thm_prop_mass_side_zpow,
    Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_zpow,
    Rat.cast_natCast, Rat.cast_intCast, Rat.cast_ofNat]

/-- A padded mass cell contains enough room for its threefold enlargement.
The enlarged cube lies in the actual half-open parent, not an invented root. -/
theorem aux_thm_prop_mass_padded_threefold {d : ℕ} (H1 Mm n : ℕ)
    (Cwidth gamma : ℝ) (sigma : Fin d → Fin Mm) (k : Fin d → ℤ)
    (hwidth : 1 ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma)
    (hpad : aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k) :
    closure (centeredCube (aux_thm_prop_mass_center H1 Mm sigma n k)
      (3 * aux_thm_prop_mass_side H1 n)
      (mul_pos (by norm_num) (aux_thm_prop_grid_side_pos H1 n)) : Set (SpatialCoordinates d)) ⊆
      aux_thm_prop_mass_parent H1 Mm sigma n k := by
  let s := aux_thm_prop_mass_side H1 n
  have hs : 0 < s := aux_thm_prop_grid_side_pos H1 n
  have hws : s ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma * s := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hwidth hs.le
  intro x hx i hi
  have hx' : x ∈ Metric.closedBall (aux_thm_prop_mass_center H1 Mm sigma n k) (3 * s / 2) :=
    (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall) hx
  have hxi : |x i - aux_thm_prop_mass_center H1 Mm sigma n k i| ≤ 3 * s / 2 := by
    have hdist : dist x (aux_thm_prop_mass_center H1 Mm sigma n k) ≤ 3 * s / 2 := hx'
    have hi' := dist_le_pi_dist x (aux_thm_prop_mass_center H1 Mm sigma n k) i
    rw [Real.dist_eq] at hi'
    exact hi'.trans hdist
  have hlo := (abs_le.mp hxi).1
  have hhi := (abs_le.mp hxi).2
  have hpi := hpad i
  change _ ≤ x i ∧ x i < _
  dsimp only [aux_thm_prop_mass_center] at hlo hhi
  constructor <;> dsimp only [s] at * <;> linarith

/-- Catalogue completeness supplies the two actual indices needed for every
padded cell selected by the mass theorem. The parent may be any interior cell
of any of the finitely shifted grids. -/
theorem aux_thm_prop_mass_catalogue_indices
    {d : ℕ} {J : Type} (j0 : J) (z : J → SpatialCoordinates d) (r : J → ℝ)
    (hr : ∀ j, 0 < r j)
    (hcontain : ∀ j, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)))
    (hcomplete : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      (∀ i, ∃ q : ℚ, zc i = (q : ℝ)) → (∃ k : ℤ, rc = (3 : ℝ) ^ k) →
      (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) →
      ∃ j, z j = zc ∧ r j = rc)
    (jQ : J) (H1 Mm n : ℕ) (Cwidth gamma : ℝ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ)
    (hwidth : 1 ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma)
    (hpad : aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k)
    (hparent : closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) :
    ∃ jC jP : J,
      z jC = aux_thm_prop_mass_center H1 Mm sigma n k ∧
      r jC = aux_thm_prop_mass_side H1 n ∧
      z jP = aux_thm_prop_mass_center H1 Mm sigma n k ∧
      r jP = 3 * aux_thm_prop_mass_side H1 n ∧
      closure (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) := by
  let zc := aux_thm_prop_mass_center H1 Mm sigma n k
  let s := aux_thm_prop_mass_side H1 n
  have hs : 0 < s := aux_thm_prop_grid_side_pos H1 n
  have hsP : 0 < 3 * s := mul_pos (by norm_num) hs
  have hpadQ : closure (centeredCube zc (3 * s) hsP : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) :=
    (aux_thm_prop_mass_padded_threefold H1 Mm n Cwidth gamma sigma k hwidth hpad).trans
      (subset_closure.trans hparent)
  have hpRoot := (subset_closure.trans hpadQ).trans (hcontain jQ)
  have hcRoot : (centeredCube zc s hs : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) :=
    (Metric.ball_subset_ball (by linarith : s / 2 ≤ 3 * s / 2)).trans hpRoot
  have hrat := aux_thm_prop_mass_center_rational H1 Mm n sigma k
  have htri := aux_thm_prop_mass_side_zpow H1 n
  have htriP : 3 * s = (3 : ℝ) ^ (1 - ((H1 * n : ℕ) : ℤ)) := by
    dsimp only [s]
    rw [htri, sub_eq_add_neg, zpow_add₀ (by norm_num)]
    norm_num
  obtain ⟨jC, hjC⟩ := hcomplete zc s hs hrat ⟨_, htri⟩ hcRoot
  obtain ⟨jP, hjP⟩ := hcomplete zc (3 * s) hsP hrat ⟨_, htriP⟩ hpRoot
  refine ⟨jC, jP, hjC.1, hjC.2, hjP.1, hjP.2, ?_⟩
  simpa only [hjP.1, hjP.2] using hpadQ

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Analytic data constructed from the actual joint candidates before selecting
any good cell. Every matrix limit, boundary minimum and energy measure is tied
to the original response operators. -/
structure aux_thm_prop_selection_data
    (d : ℕ) (hd : 2 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (m M : ℝ) where
  hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
    ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖
  AE : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ
  AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ
  ck : ℝ → ℝ
  symmetricE : ∀ j om, (AE j om).transpose = AE j om
  symmetricF : ∀ j om, (AF j om).transpose = AF j om
  measurableE : ∀ j i k, Measurable (fun om => AE j om i k)
  measurableF : ∀ j i k, Measurable (fun om => AF j om i k)
  expected : ∀ j, (∫ om, Matrix.trace (AF j om) / Matrix.trace (AE j om) ∂P) = ck (r j)
  fine_bounds : ∃ k0 : ℕ, ∀ k, k0 ≤ k → ck ((3 : ℝ) ^ (-(k : ℝ))) ∈ Icc m M
  mass_indices : ∀ (jQ H1 Mm n : ℕ) (Cwidth gamma : ℝ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ),
    1 ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma →
    aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k →
    closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
    ∃ jC jP : ℕ,
      z jC = aux_thm_prop_mass_center H1 Mm sigma n k ∧
      r jC = aux_thm_prop_mass_side H1 n ∧
      z jP = aux_thm_prop_mass_center H1 Mm sigma n k ∧
      r jP = 3 * aux_thm_prop_mass_side H1 n ∧
      closure (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
  converges : ∀ᵐ om ∂P, ∀ j,
    aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
    aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om)
  trace_positive : ∀ᵐ om ∂P, ∀ j, 0 < Matrix.trace (AE j om) ∧ 0 < Matrix.trace (AF j om)
  order : ∀ᵐ om ∂P, ∀ jP jC, z jC = z jP → r jP = 3 * r jC → ∀ p : Fin d → ℝ,
    m * (p ⬝ᵥ (AE jC om).mulVec p) ≤ p ⬝ᵥ (AF jC om).mulVec p ∧
    p ⬝ᵥ (AF jC om).mulVec p ≤ M * (p ⬝ᵥ (AE jC om).mulVec p)
  minima : ∀ᵐ om ∂P, ∀ jQ jP jC, z jC = z jP → r jP = 3 * r jC →
    (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
    (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
        (Sspace jQ) (GE jQ om) NE, ∀ (p : Fin d → ℝ) (c : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
        A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c))
        ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ (AE jC om).mulVec p)) ∧
      (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
        A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c)).Nonempty) ∧
    (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
        (Sspace jQ) (GF jQ om) NF, ∀ (p : Fin d → ℝ) (c : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
        A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c))
        ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ (AF jC om).mulVec p)) ∧
      (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
        A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c)).Nonempty)
  planes : ∀ᵐ om ∂P, ∀ j,
    (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GE j om) NE, ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
      A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0) ∧
    (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GF j om) NF, ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
      A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0)

theorem aux_thm_prop_prepare_selection
    (d : ℕ) (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (hH : InfraredCharacterization model H)
    (hfield : Measurable field)
    (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hside : ∀ᵐ om ∂P, ∀ j,
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GE j om) NE) ∧
      Nonempty (aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
        (Sspace j) (GF j om) NF))
    (horder : ∀ᵐ om ∂P, ∀ j,
      limitFormDomain (GE j om) = limitFormDomain (GF j om) ∧
      ∀ u ∈ limitFormDomain (GE j om),
        m * (limitFormEnergy (GE j om) u).toReal ≤ (limitFormEnergy (GF j om) u).toReal ∧
        (limitFormEnergy (GF j om) u).toReal ≤ M * (limitFormEnergy (GE j om) u).toReal) :
    Nonempty (aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF m M) := by
  obtain ⟨hP, AE, AF, ck, hEsym, hFsym, hEmeas, hFmeas, hck, hbounds, hevent⟩ :=
    aux_thm_prop_ordered_spatial_matrix_bank d hd BD BDQ EM hcontract model H Ω P
      field z r hr Sspace GE GF NE NF alpha eta hCat hH hfield hlaw m M hm hM hside horder
  have hconv : ∀ᵐ om ∂P, ∀ j,
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om) :=
    hevent.mono fun om h j => ⟨(h.1 j).1, (h.1 j).2.1⟩
  have htr : ∀ᵐ om ∂P, ∀ j, 0 < Matrix.trace (AE j om) ∧ 0 < Matrix.trace (AF j om) :=
    hevent.mono fun om h j => (h.1 j).2.2
  have hmin := aux_thm_prop_catalogue_ambient_affine_minima d hd BD BDQ EM hcontract
    model H Ω P field z r hr Sspace GE GF NE NF alpha eta hCat hP AE AF hconv hside
  have hplanes := aux_thm_prop_catalogue_planes_joint d hd BD BDQ EM hcontract model H Ω P
    field z r hr Sspace GE GF NE NF alpha eta hCat
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF,
    root, _hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
    cellHolderKey, origin, gridRoot, gridKey, hRepE, hRepF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  have hrat := hRepE.2.2.2.2.2.2.2.2.2.2.2.1
  have hcontain := hRepE.2.2.2.2.2.2.2.2.2.2.1
  have hcomplete := hRepE.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfine := aux_thm_prop_fine_trace_bounds root z r hr (hrat root) hcomplete
    ck m M (fun j hj => (hbounds j hj).2)
  exact ⟨{
    hP := hP, AE := AE, AF := AF, ck := ck
    symmetricE := hEsym, symmetricF := hFsym
    measurableE := hEmeas, measurableF := hFmeas
    expected := hck, fine_bounds := hfine, converges := hconv, trace_positive := htr
    mass_indices := aux_thm_prop_mass_catalogue_indices root z r hr hcontain hcomplete
    order := hevent.mono (fun om h => h.2), minima := hmin, planes := hplanes }⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.Paper

/-- The interpolation premise of the updated concentration supplier is already
contained in the represented bounds. A genuine joint response limit instantiates
those bounds, so no new principal hypothesis is necessary. -/
theorem aux_thm_prop_interpolation_of_joint_bounds
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ i, 0 < r i}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i))}
    {NE NF : ℕ → ℕ}
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (hPW : aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF) :
    CubeFractionalInterpolationInput d hd := by
  have : IsProbabilityMeasure P := hJoint.1
  have hb := aux_thm_prop_bounds_pointwise_ae hd hJoint hJoint.2.1 hJoint.2.2.1 hPW
  obtain ⟨om, hom⟩ := hb.exists
  obtain ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, rest⟩ := (hom 0).1
  exact hInterp

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The standing unit-cube trace right inverse supplies a genuine continuous
H1 boundary datum on every physical cube. The interior datum need not equal
the prescribed boundary function away from the frontier. -/
theorem aux_thm_prop_holder_boundary_datum
    {d : ℕ} (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : SpatialCoordinates d → ℝ)
    (hG : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) :
    ∃ b : weakSobolevGraph (centeredCube z r hr), ∃ U : SpatialCoordinates d → ℝ,
      Continuous U ∧
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = G x := by
  have hG1 := aux_lem_extension_isHolderOn_dilation z r hr beta G hG
  obtain ⟨b1, U1, hU1, hb1, htrace1, _hfin, _hbound⟩ :=
    Sob.traceRightInverse beta hbeta 0 1 one_pos rfl _ hG1
  obtain ⟨b, hb⟩ := aux_lem_extension_weak_pushforward z hr one_pos b1
  let U : SpatialCoordinates d → ℝ := fun y => U1 (r⁻¹ • (y - z))
  refine ⟨b, U, hU1.comp (by fun_prop), ?_, ?_⟩
  · apply (aux_lem_extension_ae_dilation_iff z hr one_pos _).mpr
    filter_upwards [hb, hb1] with x hbx hbx1
    rw [← hbx, hbx1]
    exact (congrArg U1 (aux_lem_extension_cubeDilation_inv' z hr x)).symm
  · intro x hx
    have hx1 : r⁻¹ • (x - z) ∈ frontier
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
      apply (aux_lem_extension_frontier_dilation z hr one_pos _).mp
      simpa only [aux_lem_extension_cubeDilation_inv z hr x] using hx
    change U1 (r⁻¹ • (x - z)) = G x
    rw [htrace1 _ hx1, aux_lem_extension_cubeDilation_inv z hr x]

/-- Native H1 data with its literal continuous representative. -/
theorem aux_thm_prop_holder_boundary_native
    {d : ℕ} (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : SpatialCoordinates d → ℝ)
    (hG : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) :
    ∃ b : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      Continuous b.toFun ∧
      ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), b.toFun x = G x := by
  obtain ⟨b, U, hU, hbU, htrace⟩ := aux_thm_prop_holder_boundary_datum hd Sob beta hbeta z r hr G hG
  obtain ⟨b0, hb0, _hg0⟩ := exists_nativeH1Function_of_weakSobolevGraph b
  have hae : b0.toFun =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U := by
    rw [hb0]
    exact hbU
  refine ⟨{
    toFun := U
    grad := b0.grad
    memL2 := (memLp_congr_ae hae).mp b0.memL2
    gradMemL2 := b0.gradMemL2
    hasWeakGradient := ?_ }, hU, htrace⟩
  intro i phi hphi hcomp hsub
  rw [show (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      U x * (fderiv ℝ phi x) (basisVec i) ∂volume) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        b0.toFun x * (fderiv ℝ phi x) (basisVec i) ∂volume from by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]]
  exact b0.hasWeakGradient i phi hphi hcomp hsub

/-- The boundary datum has the genuine deterministic extension estimate for
every coefficient; the constant depends only on the chosen trace exponent and
the existing standing inputs. -/
theorem aux_thm_prop_holder_extension_response
    (d : ℕ) (hd : 2 ≤ d) (I : in_J d) (X : in_extension d hd I)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (G : SpatialCoordinates d → ℝ),
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ∃ b : weakSobolevGraph (centeredCube z r hr), ∃ U : SpatialCoordinates d → ℝ,
        Continuous U ∧
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = G x) ∧
        ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
          (a : PositiveCoefficient (centeredCube z r hr)),
          dirichletResponse (killedResponseSpace hP) a b ≤
            C * I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
              (r ^ beta * holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  obtain ⟨C, hC, hExt⟩ := aux_lem_extension_boundary_half d hd I X Sob beta hbeta
  refine ⟨C, hC, ?_⟩
  intro z r hr hr1 G hG
  obtain ⟨b, U, hU, hbU, htrace⟩ := aux_thm_prop_holder_boundary_datum hd Sob beta hbeta z r hr G hG
  refine ⟨b, U, hU, hbU, htrace, ?_⟩
  intro hP a
  have hHU : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U :=
    aux_lem_skeleton_isHolderOn_congr (fun x hx => (htrace x hx).symm) hG
  have hset : holderRatioSet beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U =
      holderRatioSet beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G := by
    ext v
    constructor
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      exact ⟨x, hx, y, hy, hxy, by rw [htrace x hx, htrace y hy]⟩
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      exact ⟨x, hx, y, hy, hxy, by rw [htrace x hx, htrace y hy]⟩
  have hsemi := congrArg sSup hset
  exact (hExt z r hr hr1 hP a U b hU.continuousOn hHU hbU).trans_eq
    (by unfold holderSeminorm; rw [hsemi])

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- Quantitative exponent lowering for the literal Euclidean Hölder seminorm.
The set need not contain two different points. -/
theorem aux_thm_prop_holder_seminorm_exponent_le
    {d : ℕ} (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ)
    (D beta alpha : ℝ) (hD : 0 ≤ D) (hba : beta ≤ alpha)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ D)
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S f) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S f ≤
      D ^ (alpha - beta) * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f := by
  apply Real.sSup_le
  · rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    let e : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)
    have he : 0 < e := aux_prop_gluing_euclid_pos x y hxy
    have ha := le_csSup hf
      (show |f x - f y| / e ^ alpha ∈ _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha S f from
        ⟨x, hx, y, hy, hxy, rfl⟩)
    have habs : |f x - f y| ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f * e ^ alpha :=
      (div_le_iff₀ (Real.rpow_pos_of_pos he _)).mp ha
    have hsplit : e ^ alpha = e ^ (alpha - beta) * e ^ beta := by
      rw [← Real.rpow_add he]
      congr 1
      ring
    apply (div_le_iff₀ (Real.rpow_pos_of_pos he _)).mpr
    calc
      |f x - f y| ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f * e ^ alpha := habs
      _ = (e ^ (alpha - beta) * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f) * e ^ beta := by
        rw [hsplit]
        ring
      _ ≤ (D ^ (alpha - beta) * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f) * e ^ beta :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow he.le (hdiam x hx y hy) (sub_nonneg.mpr hba))
            (aux_prop_gluing_holderSeminorm_nonneg alpha S f))
          (Real.rpow_nonneg he.le _)
  · exact mul_nonneg (Real.rpow_nonneg hD _) (aux_prop_gluing_holderSeminorm_nonneg alpha S f)

theorem aux_thm_prop_holder_norm_exponent_le
    {d : ℕ} (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ)
    (D beta alpha : ℝ) (hD : 0 ≤ D) (hba : beta ≤ alpha)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ D)
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S f) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S f ≤ (1 + D ^ (alpha - beta)) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S f := by
  have hsemi := aux_thm_prop_holder_seminorm_exponent_le S f D beta alpha hD hba hdiam hf
  have h0 := aux_prop_gluing_supAbs_nonneg S f
  have h1 := aux_prop_gluing_holderSeminorm_nonneg alpha S f
  have hpow : 0 ≤ D ^ (alpha - beta) := Real.rpow_nonneg hD _
  dsimp [_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm]
  calc
    _ ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} +
        D ^ (alpha - beta) * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f := add_le_add le_rfl hsemi
    _ ≤ (sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f) +
        D ^ (alpha - beta) *
          (sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f) := by
      exact add_le_add (le_add_of_nonneg_right h1)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h0) hpow)
    _ = _ := by ring

/-- Convergence at a larger exponent implies convergence at every smaller
exponent on the same bounded set, with the original norm convention. -/
theorem aux_thm_prop_holder_norm_exponent_tendsto
    {d : ℕ} (S : Set (SpatialCoordinates d)) (f : ℕ → SpatialCoordinates d → ℝ)
    (D beta alpha : ℝ) (hD : 0 ≤ D) (hba : beta ≤ alpha)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ D)
    (hf : ∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S (f n))
    (hconv : Tendsto (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S (f n)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n => (1 + D ^ (alpha - beta)) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S (f n))
      atTop (𝓝 0) from by simpa only [mul_zero] using hconv.const_mul (1 + D ^ (alpha - beta)))
  · exact Eventually.of_forall (fun n => aux_prop_gluing_cAlphaNorm_nonneg beta S (f n))
  · exact Eventually.of_forall
      (fun n => aux_thm_prop_holder_norm_exponent_le S (f n) D beta alpha hD hba hdiam (hf n))

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- Complete a smooth source catalogue at a Hölder boundary datum. The source
catalogue is used only with its existing smooth topology. -/
theorem aux_thm_prop_holder_catalogue_approximation
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Catalog : Set (SpatialCoordinates d → ℝ))
    (hCatalog : ∀ f ∈ Catalog, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hDense : ∀ B : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ B → HasCompactSupport B →
      tsupport B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ Bs : ℕ → SpatialCoordinates d → ℝ, (∀ n, Bs n ∈ Catalog) ∧
        ∀ m : ℕ, TendstoUniformly
          (fun n x => iteratedFDeriv ℝ m (fun y => Bs n y - B y) x) (fun _ => 0) atTop)
    (alpha : ℝ) (halpha : 1 / 2 < alpha)
    (B : SpatialCoordinates d → ℝ)
    (hBcont : ContinuousOn B (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hBholder : ∀ theta : ℝ, 1 / 2 < theta → theta < min alpha 1 →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn theta (closure (centeredCube z r hr : Set (SpatialCoordinates d))) B)
    (hBvanish : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = 0)
    (hBzero : ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), B x = 0)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < min alpha 1) :
    ∃ Bs : ℕ → SpatialCoordinates d → ℝ,
      (∀ n, Bs n ∈ Catalog) ∧ TendstoUniformly Bs B atTop ∧
      (∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
        (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (fun x => Bs n x - B x)) ∧
      (∀ n, BddAbove {v : ℝ | ∃ x ∈ closure
        (centeredCube z r hr : Set (SpatialCoordinates d)), v = |Bs n x - B x|}) ∧
      Tendsto (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (fun x => Bs n x - B x)) atTop (𝓝 0) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let K : Set (SpatialCoordinates d) := closure (centeredCube z r hr : Set (SpatialCoordinates d))
  have hb0 : 0 < beta := by linarith only [hbeta]
  have hb1 : beta < 1 := hba.trans_le (min_le_right _ _)
  have hdiam : ∀ x ∈ K, ∀ y ∈ K,
      Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ Real.sqrt (d : ℝ) * r :=
    fun x hx y hy => aux_prop_gluing_euclid_le_of_mem_closure z r hr x y hx hy
  have hdist : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ r := by
    intro x hx y hy
    have hx' := Metric.closure_ball_subset_closedBall hx
    have hy' := Metric.closure_ball_subset_closedBall hy
    have h := dist_triangle x z y
    rw [Metric.mem_closedBall] at hx' hy'
    rw [dist_comm z y] at h
    linarith only [hx', hy', h]
  have hsmooth : ∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta K f := fun f hf hs =>
    aux_lem_skeleton_isHolderOn_of_contDiff_bounded hb0 hb1.le hf hs hr.le hdist
  have hbH := hBholder beta hbeta hba
  have hbounded : ∀ f : SpatialCoordinates d → ℝ, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta K f →
      BddAbove {v : ℝ | ∃ x ∈ K, v = |f x|} := fun f hf =>
    aux_prop_gluing_bddAbove_abs_of_isHolderOn K f (Real.sqrt (d : ℝ) * r) beta
      (mul_nonneg (Real.sqrt_nonneg _) hr.le) hdiam hb0.le hf
  obtain ⟨g, hg, hgsupp, hgQ, hgconv⟩ :=
    lem_skeleton_smooth_approx (Q := centeredCube z r hr) hd ⟨z, r, hr, rfl⟩
      alpha halpha B hBcont hBholder hBvanish beta hbeta hba
  have hchoose (n : ℕ) : ∃ f ∈ Catalog,
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K (fun x => f x - g n x) ≤ 1 / ((n : ℝ) + 1) := by
    obtain ⟨a, ha, hder⟩ := hDense (g n) (hg n) (hgsupp n) (hgQ n)
    have hconv := (aux_thm_prop_smooth_source_approximation a (g n)
      (fun j => (hCatalog _ (ha j)).1) (hg n)
      (fun j => (hCatalog _ (ha j)).2.1) (hgsupp n) hder beta hb0 hb1 K).2.2.2
    obtain ⟨j, hj⟩ := (hconv.eventually (gt_mem_nhds
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity))).exists
    exact ⟨a j, ha j, hj.le⟩
  choose Bs hBs herror using hchoose
  have hBsH (n : ℕ) : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta K (Bs n) :=
    hsmooth _ (hCatalog _ (hBs n)).1 (hCatalog _ (hBs n)).2.1
  have hgH (n : ℕ) : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta K (g n) := hsmooth _ (hg n) (hgsupp n)
  have hdiffH (n : ℕ) : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta K (fun x => Bs n x - B x) :=
    aux_prop_gluing_isHolderOn_sub beta K _ _ (hBsH n) hbH
  have happrox (n : ℕ) : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K (fun x => Bs n x - B x) ≤
      1 / ((n : ℝ) + 1) + _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K (fun x => g n x - B x) := by
    have hf := aux_prop_gluing_isHolderOn_sub beta K _ _ (hBsH n) (hgH n)
    have hh := aux_prop_gluing_isHolderOn_sub beta K _ _ hbH (hgH n)
    have h := aux_prop_gluing_cAlphaNorm_sub_le beta K
      (fun x => Bs n x - g n x) (fun x => B x - g n x)
      (aux_prop_gluing_closure_nontrivial (by omega) z r hr)
      (hbounded _ hf) (hbounded _ hh) hf hh
    have heq : (fun x => (Bs n x - g n x) - (B x - g n x)) = (fun x => Bs n x - B x) := by
      funext x
      ring
    rw [heq] at h
    have hneg : (fun x => B x - g n x) = (fun x => -(g n x - B x)) := by
      funext x
      ring
    rw [hneg, aux_prop_gluing_cAlphaNorm_neg] at h
    exact h.trans (add_le_add (herror n) le_rfl)
  have hnorm : Tendsto (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K (fun x => Bs n x - B x))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) +
          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K (fun x => g n x - B x)) atTop (𝓝 0) from by
        simpa only [zero_add] using tendsto_one_div_add_atTop_nhds_zero_nat.add hgconv)
    · exact Eventually.of_forall (fun n => aux_prop_gluing_cAlphaNorm_nonneg beta K _)
    · exact Eventually.of_forall happrox
  have huniform : TendstoUniformlyOn Bs B atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    filter_upwards [hnorm.eventually (gt_mem_nhds heps)] with n hn x hx
    have hval : |Bs n x - B x| ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K (fun y => Bs n y - B y) :=
      (le_csSup (hbounded _ (hdiffH n)) ⟨x, hx, rfl⟩).trans
        (le_add_of_nonneg_right (aux_prop_gluing_holderSeminorm_nonneg beta K _))
    simpa only [Real.dist_eq, abs_sub_comm] using hval.trans_lt hn
  refine ⟨Bs, hBs, ?_, hdiffH, fun n => hbounded _ (hdiffH n), hnorm⟩
  apply aux_prop_gluing_tendstoUniformly_global K Bs B huniform
  · intro n x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact hx (subset_closure ((hCatalog _ (hBs n)).2.2 hs))
  · intro x hx
    exact hBzero x (fun h => hx (subset_closure h))

/-- One catalogue sequence converges at both the catalogue exponent and an
independent local exponent. Neither exponent changes the represented estimates. -/
theorem aux_thm_prop_holder_catalogue_two_exponents
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Catalog : Set (SpatialCoordinates d → ℝ))
    (hCatalog : ∀ f ∈ Catalog, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hDense : ∀ B : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ B → HasCompactSupport B →
      tsupport B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ Bs : ℕ → SpatialCoordinates d → ℝ, (∀ n, Bs n ∈ Catalog) ∧
        ∀ m : ℕ, TendstoUniformly
          (fun n x => iteratedFDeriv ℝ m (fun y => Bs n y - B y) x) (fun _ => 0) atTop)
    (alpha : ℝ) (halpha : 1 / 2 < alpha)
    (B : SpatialCoordinates d → ℝ)
    (hBcont : ContinuousOn B (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hBholder : ∀ theta : ℝ, 1 / 2 < theta → theta < min alpha 1 →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn theta (closure (centeredCube z r hr : Set (SpatialCoordinates d))) B)
    (hBvanish : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = 0)
    (hBzero : ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), B x = 0)
    (betaCat betaLocal : ℝ) (hCat : 1 / 2 < betaCat) (hLocal : 1 / 2 < betaLocal)
    (hCatAlpha : betaCat < min alpha 1) (hLocalAlpha : betaLocal < min alpha 1) :
    ∃ Bs : ℕ → SpatialCoordinates d → ℝ,
      (∀ n, Bs n ∈ Catalog) ∧ TendstoUniformly Bs B atTop ∧
      ∀ beta ∈ ({betaCat, betaLocal} : Set ℝ),
        (∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
          (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (fun x => Bs n x - B x)) ∧
        (∀ n, BddAbove {v : ℝ | ∃ x ∈ closure
          (centeredCube z r hr : Set (SpatialCoordinates d)), v = |Bs n x - B x|}) ∧
        Tendsto (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (fun x => Bs n x - B x)) atTop (𝓝 0) := by
  obtain ⟨Bs, hBs, hU, hH, hB, hN⟩ := aux_thm_prop_holder_catalogue_approximation hd z r hr
    Catalog hCatalog hDense alpha halpha B hBcont hBholder hBvanish hBzero
    (max betaCat betaLocal) (hCat.trans_le (le_max_left _ _)) (max_lt hCatAlpha hLocalAlpha)
  refine ⟨Bs, hBs, hU, ?_⟩
  intro beta hbeta
  have hbmax : beta ≤ max betaCat betaLocal := by
    rcases hbeta with rfl | h
    · exact le_max_left _ _
    · have : beta = betaLocal := h
      rw [this]
      exact le_max_right _ _
  have hb0 : 0 ≤ beta := by
    rcases hbeta with rfl | h
    · linarith only [hCat]
    · have : beta = betaLocal := h
      rw [this]
      linarith only [hLocal]
  have hD : 0 ≤ Real.sqrt (d : ℝ) * r := mul_nonneg (Real.sqrt_nonneg _) hr.le
  have hdiam := fun x hx y hy => aux_prop_gluing_euclid_le_of_mem_closure z r hr x y hx hy
  exact ⟨fun n => aux_prop_gluing_isHolderOn_mono _ _ _ beta _ hD hdiam hb0 hbmax (hH n),
    hB, aux_thm_prop_holder_norm_exponent_tendsto _ _ _ beta _ hD hbmax hdiam hH hN⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper
section Standing

variable {d : ℕ} {hd : 2 ≤ d}
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

include BD BDQ EM hcontract


/-- Identify a Hölder boundary response with its actual energy-measure minimum.
The smooth catalogue is completed at its own exponent; no global Hölder
upgrade of the represented estimates is used. -/
theorem aux_thm_prop_holder_boundary_glb
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (ha1 : alpha < 1)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] A n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (Controls : aux_thm_prop_analytic_controls d hd z (3 * r) h3r S aC)
    (GN : ℕ → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (aC n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (hE : ∀ v, E.energy v = limitFormEnergy G v)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (hDq : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) Dq)
    (t : ℝ) (htControl : Controls.t ≤ t)
    (Catalog : Set (SpatialCoordinates d → ℝ))
    (hCatalog : ∀ Phi ∈ Catalog,
      ContDiff ℝ ∞ Phi ∧ HasCompactSupport Phi ∧
        tsupport Phi ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hCatalogBounds : aux_thm_prop_mesh_controls z r h3r hcellsub A Catalog alpha t)
    (hCountable : Catalog.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (Ugrid : OddGridIndex d (triadicHalf 1) → ℕ → ℝ)
    (UgridStar : OddGridIndex d (triadicHalf 1) → ℝ)
    (hUg : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      0 ≤ Ugrid k n ∧ Ugrid k n ≤ UgridStar k)
    (hGridBound : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      ∀ e : H1Function
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)),
      ContinuousOn e.toFun
          (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun →
      cellDirichletInfimum (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) e ≤
        C * Ugrid k n * r ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta
            (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun ^ 2)
    (UStar : ℝ)
    (Uq : ℕ → ℝ) (hUq : ∀ n : ℕ, 0 ≤ Uq n ∧ Uq n ≤ UStar)
    (hBound : ∀ n : ℕ, ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
        ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta z r e.toFun →
        cellDirichletInfimum (A n) (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
          C * Uq n * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
    (hDense : ∀ B : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ B → HasCompactSupport B →
      tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∃ Bs : ℕ → SpatialCoordinates d → ℝ,
        (∀ k, Bs k ∈ Catalog) ∧
        (∀ m : ℕ, TendstoUniformly
          (fun n x => iteratedFDeriv ℝ m (fun y => Bs n y - B y) x) (fun _ => 0) atTop))
    (B : SpatialCoordinates d → ℝ)
    (hBcont : ContinuousOn B (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hBholder : ∀ theta : ℝ, 1 / 2 < theta → theta < min alpha 1 →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn theta (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) B)
    (hBvanish : ∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), B x = 0)
    (hBzero : ∀ x ∉ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), B x = 0)
    (b : SpatialCoordinates d → ℝ)
    (hBb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x)
    (bq : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hbq : ContinuousOn bq.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hbqb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), bq.toFun x = b x)
    (L : ℝ)
    (hResponse : Tendsto (fun n => cellDirichletInfimum (A n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) bq) atTop (𝓝 L)) :
    IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      E.toClosedForm Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) b) L ∧
    (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      E.toClosedForm Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) b).Nonempty := by
  have halpha : (1 / 2 : ℝ) < alpha := lt_trans hbeta hba
  have hbeta1 : beta < (1 : ℝ) := lt_trans hba ha1
  have hbetaAlpha : beta < min alpha (1 : ℝ) := lt_min hba hbeta1
  obtain ⟨Bs, hBsCat, hBsU, hBsHol, hBsBdd, hBsNorm⟩ :=
    aux_thm_prop_holder_catalogue_approximation hd z (3 * r) h3r Catalog hCatalog hDense
      alpha halpha B hBcont hBholder hBvanish hBzero beta hbeta hbetaAlpha
  exact aux_thm_prop_boundary_glb_completion BD BDQ EM hcontract z r hr h3r hcellsub
    beta alpha hbeta hba ha1 S hS A hAcont aC haC hell E Gamma Controls GN G hGN hConv hE hcore
    Dq hDq t htControl Catalog hCatalog hCatalogBounds hCountable C hC Ugrid UgridStar hUg
    hGridBound UStar Uq hUq hBound Bs B hBsU hBsHol hBsBdd hBsNorm b hBb hBsCat bq hbq hbqb L hResponse

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff Manifold

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_holder_product
    {d : ℕ} (alpha : ℝ) (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ)
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S f) (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S g)
    (hfAbs : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|})
    (hgAbs : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|}) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S (fun x => f x * g x) := by
  obtain ⟨Cf, hCf, hfpair⟩ := aux_lem_skeleton_holderOn_dest hf
  obtain ⟨Cg, hCg, hgpair⟩ := aux_lem_skeleton_holderOn_dest hg
  obtain ⟨Mf, hMf⟩ := hfAbs
  obtain ⟨Mg, hMg⟩ := hgAbs
  refine ⟨max Mf 0 * Cg + Cf * max Mg 0, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  have he : 0 < Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) :=
    aux_prop_gluing_euclid_pos x y hxy
  apply (div_le_iff₀ (Real.rpow_pos_of_pos he alpha)).mpr
  have hfx : |f x| ≤ max Mf 0 := (hMf ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  have hgy : |g y| ≤ max Mg 0 := (hMg ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  calc
    |f x * g x - f y * g y| = |f x * (g x - g y) + (f x - f y) * g y| := by
      congr 1
      ring
    _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |f x - f y| * |g y| := by rw [abs_mul, abs_mul]
    _ ≤ max Mf 0 * (Cg * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha) +
        (Cf * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha) * max Mg 0 :=
      add_le_add
        (mul_le_mul hfx (hgpair x hx y hy hxy) (abs_nonneg _) (le_max_right _ _))
        (mul_le_mul (hfpair x hx y hy hxy) hgy (abs_nonneg _)
          (mul_nonneg hCf (Real.rpow_nonneg he.le _)))
    _ = _ := by ring

/-- Cut off a Hölder datum inside the padded cube while retaining its literal
values on the inner cell. This supplies the genuine datum for completion. -/
theorem aux_thm_prop_holder_collar
    {d : ℕ} (_hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (h3r : 0 < 3 * r)
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (b : SpatialCoordinates d → ℝ)
    (hb : ContinuousOn b (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hbh : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) b) :
    ∃ B : SpatialCoordinates d → ℝ,
      ContinuousOn B (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      HasCompactSupport B ∧ tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) B ∧
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x) ∧
      (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), B x = 0) ∧
      (∀ x ∉ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), B x = 0) := by
  let : NeZero d := ⟨by omega⟩
  let Q := centeredCube z (3 * r) h3r
  have hqQ : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)) :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith))
  obtain ⟨K, hKcompact, hKclosed, hqK, hKQ⟩ := exists_compact_closed_between
    (isCompact_closure_centeredCube z hr) Q.isOpen hqQ
  obtain ⟨chi, hchiOne, hchiZero, _hchiRange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, SpatialCoordinates d)) isClosed_closure hqK
  have hchiSmooth : ContDiff ℝ ∞ chi := chi.contMDiff.contDiff
  have hsupp : tsupport (chi : SpatialCoordinates d → ℝ) ⊆ K :=
    closure_minimal (Function.support_subset_iff'.mpr hchiZero) hKclosed
  have hchiComp : HasCompactSupport (chi : SpatialCoordinates d → ℝ) :=
    hKcompact.of_isClosed_subset isClosed_closure hsupp
  have hdist : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (Q : Set (SpatialCoordinates d)), dist x y ≤ 3 * r := by
    intro x hx y hy
    have hx' := Metric.closure_ball_subset_closedBall hx
    have hy' := Metric.closure_ball_subset_closedBall hy
    have h := dist_triangle x z y
    rw [Metric.mem_closedBall] at hx' hy'
    rw [dist_comm z y] at h
    linarith only [hx', hy', h]
  have hchiH := aux_lem_skeleton_isHolderOn_of_contDiff_bounded ha0 ha1
    hchiSmooth hchiComp h3r.le hdist
  have hbound (f : SpatialCoordinates d → ℝ)
      (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) f) :=
    aux_prop_gluing_bddAbove_abs_of_isHolderOn _ f (Real.sqrt (d : ℝ) * (3 * r)) alpha
      (mul_nonneg (Real.sqrt_nonneg _) h3r.le)
      (fun x hx y hy => aux_prop_gluing_euclid_le_of_mem_closure z (3 * r) h3r x y hx hy) ha0.le hf
  let B : SpatialCoordinates d → ℝ := fun x => chi x * b x
  have hBQ : tsupport B ⊆ (Q : Set (SpatialCoordinates d)) :=
    tsupport_mul_subset_left.trans (hsupp.trans hKQ)
  have hzero (x : SpatialCoordinates d) (hx : x ∉ (Q : Set (SpatialCoordinates d))) : B x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hBQ h))
  refine ⟨B, hchiSmooth.continuous.continuousOn.mul hb,
    hKcompact.of_isClosed_subset isClosed_closure (tsupport_mul_subset_left.trans hsupp), hBQ,
    aux_thm_prop_holder_product alpha _ _ _ hchiH hbh (hbound _ hchiH) (hbound _ hbh), ?_, ?_, hzero⟩
  · intro x hx
    change chi x * b x = b x
    rw [hchiOne.self_of_nhdsSet x hx, one_mul]
  · intro x hx
    apply hzero x
    intro h
    apply hx.2
    change x ∈ interior (Q : Set (SpatialCoordinates d))
    rw [Q.isOpen.interior_eq]
    exact h

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The actual finite boundary response has a uniform extension constant for
each fixed local exponent. This exponent is independent of any catalogue. -/
theorem aux_thm_prop_local_extension_bound
    (d : ℕ) (hd : 2 ≤ d) (I : in_J d) (X : in_extension d hd I)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (_hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (aC : PositiveCoefficient (centeredCube z r hr)) (a : SpatialCoordinates d → ℝ)
        (_haC : aC.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] a)
        (Lam : ℝ)
        (_ha0 : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ a x)
        (_haLam : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), a x ≤ Lam)
        (_hameas : AEStronglyMeasurable a
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
        (b : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))),
        ContinuousOn b.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b.toFun →
        cellDirichletInfimum a (centeredCube z r hr : Set (SpatialCoordinates d)) b ≤
          C * I.Lam z r hr aC z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b.toFun) ^ 2 := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hExt⟩ := aux_lem_extension_boundary_half d hd I X Sob beta hbeta
  refine ⟨C, hC, ?_⟩
  intro z r hr hr1 hP aC a haC Lam ha0 haLam hameas b hb hHolder
  rw [aux_thm_prop_cell_response_eq_dirichlet hP aC a haC Lam ha0 haLam hameas b]
  have hclosure : closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (closedCube z r hr : Set (SpatialCoordinates d)) := closure_ball z (half_pos hr).ne'
  exact hExt z r hr hr1 hP aC b.toFun
    ⟨sobolevDataOfH1 b, sobolevDataOfH1_mem_weak b⟩
    (hclosure ▸ hb) hHolder (sobolevDataOfH1_fst_coeFn b)

/-- Pass the local extension estimate using the actual coarse-coefficient
limit. Only the finite response and coefficient convergence are consumed. -/
theorem aux_thm_prop_local_extension_limit
    (d : ℕ) (hd : 2 ≤ d) (I : in_J d) (X : in_extension d hd I)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (_hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (aC : ℕ → PositiveCoefficient (centeredCube z r hr)) (a : ℕ → SpatialCoordinates d → ℝ)
        (_haC : ∀ n, (aC n).val =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] a n)
        (_hbound : ∀ n, ∃ Lam : ℝ,
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ a n x ∧ a n x ≤ Lam) ∧
          AEStronglyMeasurable (a n)
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
        (b : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))),
        ContinuousOn b.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b.toFun →
        ∀ L Uq : ℝ,
          Tendsto (fun n => cellDirichletInfimum (a n)
            (centeredCube z r hr : Set (SpatialCoordinates d)) b) atTop (𝓝 L) →
          Tendsto (fun n => I.Lam z r hr (aC n) z r ((beta - 1 / 2) / 4) 2) atTop (𝓝 Uq) →
          L ≤ C * Uq * r ^ ((d : ℝ) - 2) *
            (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b.toFun) ^ 2 := by
  obtain ⟨C, hC, hfinite⟩ := aux_thm_prop_local_extension_bound d hd I X Sob beta hbeta
  refine ⟨C, hC, ?_⟩
  intro z r hr hr1 hP aC a haC hbound b hb hHolder L Uq hL hUq
  apply le_of_tendsto_of_tendsto hL
    (((hUq.const_mul C).mul_const (r ^ ((d : ℝ) - 2))).mul_const
      ((r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b.toFun) ^ 2))
  filter_upwards with n
  obtain ⟨Lam, ha, hmeas⟩ := hbound n
  exact hfinite z r hr hr1 hP (aC n) (a n) (haC n) Lam
    (fun x hx => (ha x hx).1) (fun x hx => (ha x hx).2) hmeas b hb hHolder

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Fixed geometric choices for the mass argument, made before the model and
the endpoint gap. -/
structure aux_thm_prop_selection_geometry (d : ℕ) where
  H1 : ℕ
  Mm : ℕ
  gamma : ℝ
  zeta : ℝ
  width : ℝ
  H1_pos : 1 ≤ H1
  Mm_two : 2 ≤ Mm
  gamma_mem : gamma ∈ Ioo (0 : ℝ) 1
  zeta_pos : 0 < zeta
  width_pos : 0 < width
  coprime : Nat.Coprime Mm (3 ^ H1)
  shift_bound : (Mm : ℝ) ^ (-1 : ℝ) ≤ ((3 : ℝ) ^ H1) ^ (gamma - 1)
  padded_width : 1 ≤ width * ((3 : ℝ) ^ H1) ^ gamma
  loss : (1 / 32 : ℝ) + ((3 : ℝ) ^ H1) ^ (-zeta) +
    (2 * (d : ℝ) * (width + 2)) * ((3 : ℝ) ^ H1) ^ (gamma - 1) +
      (1 / 32 : ℝ) ≤ 1 / 8

theorem aux_thm_prop_selection_geometry_exists
    (d H0 : ℕ) (gamma zeta width : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) 1) (hzeta : 0 < zeta) (hwidth : 1 ≤ width) :
    ∃ g : aux_thm_prop_selection_geometry d,
      H0 ≤ g.H1 ∧ g.gamma = gamma ∧ g.zeta = zeta ∧ g.width = width := by
  obtain ⟨H1, Mm, hlarge, hH1, hMm, hcop, hshift, hloss⟩ :=
    aux_thm_prop_mass_parameters d H0 gamma zeta width hgamma.1 hgamma.2 hzeta
  have hpower : 1 ≤ ((3 : ℝ) ^ H1) ^ gamma :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) hgamma.1.le
  have hpad : 1 ≤ width * ((3 : ℝ) ^ H1) ^ gamma :=
    one_mul (1 : ℝ) ▸
      (mul_le_mul hwidth hpower (by norm_num) (zero_lt_one.trans_le hwidth).le)
  refine ⟨⟨H1, Mm, gamma, zeta, width, hH1, hMm, hgamma, hzeta,
    zero_lt_one.trans_le hwidth, hcop, hshift, ?_, hloss⟩, hlarge, rfl, rfl, rfl⟩
  simpa only [one_mul] using hpad

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The volume floor gives strictly positive finite mass even when the source
energy vanishes. Its support and all shifted faces are proved separately. -/
theorem aux_thm_prop_floor_mass_properties
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (mu : Measure (SpatialCoordinates d)) [IsFiniteMeasure mu]
    (hsupp : mu (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0)
    (hplanes : ∀ (i : Fin d) (a : ℝ), mu {x | x i = a} = 0)
    (c : ℝ) (hc : 0 < c) :
    let nu := mu + ENNReal.ofReal c •
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
    IsFiniteMeasure nu ∧
      nu (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 ∧
      0 < nu (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      ∀ (i : Fin d) (a : ℝ), nu {x | x i = a} = 0 := by
  let Q := centeredCube z r hr
  have : IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (centeredCube_isBounded z hr).measure_lt_top⟩
  dsimp only
  refine ⟨⟨?_⟩, ?_, ?_, aux_thm_prop_floor_planes_null mu _ c hplanes⟩
  · rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr
      ⟨measure_ne_top mu _, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top (volume.restrict (Q : Set (SpatialCoordinates d))) _)⟩)
  · rw [Measure.add_apply, hsupp, Measure.smul_apply,
      Measure.restrict_apply Q.isOpen.measurableSet.compl,
      compl_inter_self, measure_empty, smul_zero, add_zero]
  · rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply Q.isOpen.measurableSet, inter_self]
    have hv := (ENNReal.toReal_pos_iff.mp (centeredCube_volume_pos z hr)).1
    exact (ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hc))
      (ne_of_gt hv)).trans_le (le_add_left le_rfl)

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The quantitative local affine conclusion, expressed using the genuine
continuous boundary-energy class. This is an estimate provided by the
local affine lemma, not a new assumption on the principal theorem. -/
def aux_thm_prop_affine_error
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (u : DomainL2 Q)
    (U : SpatialCoordinates d → ℝ) (c : ℝ) (q : Set (SpatialCoordinates d)) : Prop :=
  ∃ pc : (Fin d → ℝ) × ℝ,
    let b := fun x => U x - ((∑ i, pc.1 i * x i) + pc.2)
    ∃ Lambda : ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set Q E Gamma q b) Lambda ∧
      (aux_thm_prop_boundary_energy_set Q E Gamma q b).Nonempty ∧
      Lambda ≤ ((3 / 8 : ℝ) * (1 / 8) / 16) *
        ((Gamma.measure u q).toReal + c * (volume q).toReal)

/-- The per-cell data retained from the actual affine approximation and the
relative matrix test. No harmonic minimizer or replacement is assumed. -/
structure aux_thm_prop_boundary_cell_data
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (u : E.domain) (c : ℝ) (q : Set (SpatialCoordinates d)) where
  U : SpatialCoordinates d → ℝ
  continuous : ContinuousOn U (closure (Q : Set (SpatialCoordinates d)))
  represents : ⇑u.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U
  AE : Matrix (Fin d) (Fin d) ℝ
  AF : Matrix (Fin d) (Fin d) ℝ
  minimumE : ∀ (p : Fin d → ℝ) (b : ℝ),
    IsGLB (aux_thm_prop_boundary_energy_set Q E.toClosedForm GammaE q
      (fun x => (∑ i, p i * x i) + b)) ((volume q).toReal * (p ⬝ᵥ AE.mulVec p))
  minimumF : ∀ (p : Fin d → ℝ) (b : ℝ),
    IsGLB (aux_thm_prop_boundary_energy_set Q F.toClosedForm GammaF q
      (fun x => (∑ i, p i * x i) + b)) ((volume q).toReal * (p ⬝ᵥ AF.mulVec p))
  saving : ∀ p : Fin d → ℝ,
    (3 / 8 : ℝ) * (M - m) * ((volume q).toReal * (p ⬝ᵥ AE.mulVec p)) ≤
      M * ((volume q).toReal * (p ⬝ᵥ AE.mulVec p)) -
        (volume q).toReal * (p ⬝ᵥ AF.mulVec p)
  approximation : aux_thm_prop_affine_error Q E.toClosedForm GammaE u.val U c q

/-- Actual fine-cell selection from the local boundary estimates. The proof
constructs the positive floor measure, applies the mass theorem at arbitrarily
fine levels, and constructs the killed trace forms of every selected cell. -/
theorem aux_thm_prop_fine_cells_of_boundary_estimates
    (d : ℕ) (hd : 2 ≤ d) (zQ : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (E F : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 (centeredCube zQ R hR) →L[ℝ] DomainL2 (centeredCube zQ R hR))
    (hdom : E.domain = F.domain)
    (hEdom : E.domain = limitFormDomain GE) (hFdom : F.domain = limitFormDomain GF)
    (hEenergy : ∀ v ∈ E.domain, E.form v v = (limitFormEnergy GE v).toReal)
    (hFenergy : ∀ v ∈ F.domain, F.form v v = (limitFormEnergy GF v).toReal)
    (hEcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (hFcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (horder : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v ∧ F.form v v ≤ M * E.form v v)
    (u : E.domain) (c : ℝ) (hc : 0 < c)
    (hsupp : GammaE.measure u.val (centeredCube zQ R hR : Set (SpatialCoordinates d))ᶜ = 0)
    (hplanes : ∀ (i : Fin d) (a : ℝ), GammaE.measure u.val {x | x i = a} = 0)
    (g : aux_thm_prop_selection_geometry d)
    (Uset : ℕ → Prop) (hU : (1 / 2 : ℝ) ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity Uset)
    (Good : (Fin d → Fin g.Mm) → ℕ → (Fin d → ℤ) → Prop)
    (B : (Fin d → Fin g.Mm) → ℝ) (hB : ∀ sigma, 0 ≤ B sigma)
    (hbad : ∀ sigma x, x ∈ (centeredCube zQ R hR : Set (SpatialCoordinates d)) →
      ∀ J : ℕ,
        (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
          ¬ Good sigma n (aux_thm_prop_mass_point_idx g.H1 g.Mm sigma n x)} : ℝ) ≤
          (1 / 32 : ℝ) * (J : ℝ) + B sigma)
    (baseMesh : ℝ) (hbase : 0 < baseMesh)
    (mu : Measure (SpatialCoordinates d))
    (hmu : mu = GammaE.measure u.val + ENNReal.ofReal c •
      volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (hlocal : ∀ (n : ℕ), 1 ≤ n → Uset n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
      ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
      Good sigma n k → aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
      closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
        (centeredCube zQ R hR : Set (SpatialCoordinates d)) →
      (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
        ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
          (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
      Nonempty (aux_thm_prop_boundary_cell_data (centeredCube zQ R hR) E F GammaE GammaF
        m M u c (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
          (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
            Set (SpatialCoordinates d)))) :
    Nonempty (aux_thm_prop_fine_cells (centeredCube zQ R hR) E F GammaE GammaF m M u c) := by
  have : IsFiniteMeasure (GammaE.measure u.val) :=
    ⟨GammaE.measure_univ_lt_top u.val u.property⟩
  have hmuFacts := aux_thm_prop_floor_mass_properties zQ R hR
    (GammaE.measure u.val) hsupp hplanes c hc
  rw [← hmu] at hmuFacts
  have : IsFiniteMeasure mu := hmuFacts.1
  apply aux_thm_prop_fine_cells_of_mass d hd zQ R hR E F GammaE GammaF m M u c
    mu hmu hmuFacts.2.1 hmuFacts.2.2.1 g.H1 g.Mm g.H1_pos g.Mm_two
    g.gamma g.zeta g.width g.gamma_mem g.zeta_pos g.width_pos g.coprime g.shift_bound
    (fun sigma n i k => hmuFacts.2.2.2 i _) Uset hU Good (1 / 32) (1 / 32)
    (by norm_num) (by norm_num) g.loss B hB hbad baseMesh hbase
  intro n hn hUn hmesh sigma k hgood hpad hparent hratio
  obtain ⟨data⟩ := hlocal n hn hUn hmesh sigma k hgood hpad hparent hratio
  have hqQ : (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
      (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) := by
    have hthree := aux_thm_prop_mass_padded_threefold g.H1 g.Mm n g.width g.gamma
      sigma k g.padded_width hpad
    have hs : 0 < aux_thm_prop_mass_side g.H1 n := aux_thm_prop_grid_side_pos g.H1 n
    have hball : (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
        (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
          Set (SpatialCoordinates d)) ⊆
        (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
          (3 * aux_thm_prop_mass_side g.H1 n)
          (mul_pos (by norm_num) (aux_thm_prop_grid_side_pos g.H1 n)) :
            Set (SpatialCoordinates d)) :=
      Metric.ball_subset_ball (by linarith only [hs])
    exact hball.trans (subset_closure.trans
      (hthree.trans (subset_closure.trans hparent)))
  exact aux_thm_prop_affine_cell_of_boundary_estimates d hd zQ _ R _ hR
    (aux_thm_prop_grid_side_pos g.H1 n) hqQ E F GE GF hdom hEdom hFdom
    hEenergy hFenergy hEcore hFcore GammaE GammaF m M hm hM horder u
    data.U data.continuous data.represents c data.AE data.AF data.minimumE data.minimumF
    data.saving data.approximation

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_boundary_glb_nonneg
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (q : Set (SpatialCoordinates d))
    (b : SpatialCoordinates d → ℝ) (v : ℝ)
    (h : IsGLB (aux_thm_prop_boundary_energy_set Q E Gamma q b) v) : 0 ≤ v := by
  apply h.2
  rintro e ⟨w, W, hw, hW, hrep, hb, rfl⟩
  exact ENNReal.toReal_nonneg

section Branches

variable {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (m M ck : ℝ) (q : Set (SpatialCoordinates d))
    (AE AF : Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ (p : Fin d → ℝ) (b : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set Q E.toClosedForm GammaE q
        (fun x => (∑ i, p i * x i) + b)) ((volume q).toReal * (p ⬝ᵥ AE.mulVec p)))
    (hAF : ∀ (p : Fin d → ℝ) (b : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set Q F.toClosedForm GammaF q
        (fun x => (∑ i, p i * x i) + b)) ((volume q).toReal * (p ⬝ᵥ AF.mulVec p)))
    (hconc : ∀ p : Fin d → ℝ,
      |(volume q).toReal * (p ⬝ᵥ AF.mulVec p) -
        ck * ((volume q).toReal * (p ⬝ᵥ AE.mulVec p))| ≤
        (1 / 8 : ℝ) * (M - m) * ((volume q).toReal * (p ⬝ᵥ AE.mulVec p)))

include hAE hAF hconc

/-- The U alternative uses the actual E-source approximation and the lower
half of the common deterministic coefficient sequence. -/
theorem aux_thm_prop_boundary_cell_U
    (hck : ck ≤ (m + M) / 2) (u : E.domain) (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
    (hrep : ⇑u.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U)
    (c : ℝ) (happrox : aux_thm_prop_affine_error Q E.toClosedForm GammaE u.val U c q) :
    Nonempty (aux_thm_prop_boundary_cell_data Q E F GammaE GammaF m M u c q) := by
  refine ⟨⟨U, hU, hrep, AE, AF, hAE, hAF, ?_, happrox⟩⟩
  intro p
  exact aux_thm_prop_affine_saving_U m M ck _ _
    (aux_thm_prop_boundary_glb_nonneg Q E.toClosedForm GammaE q _ _ (hAE p 0))
    hck (hconc p)

/-- The V alternative really swaps the forms and their source. The reciprocal
gap retains the same absolute saving coefficient. -/
theorem aux_thm_prop_boundary_cell_V
    (hm : 0 < m) (hmM : m ≤ M) (hck : (m + M) / 2 ≤ ck)
    (u : F.domain) (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
    (hrep : ⇑u.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U)
    (c : ℝ) (happrox : aux_thm_prop_affine_error Q F.toClosedForm GammaF u.val U c q) :
    Nonempty (aux_thm_prop_boundary_cell_data Q F E GammaF GammaE M⁻¹ m⁻¹ u c q) := by
  refine ⟨⟨U, hU, hrep, AF, AE, hAF, hAE, ?_, happrox⟩⟩
  intro p
  have hE0 := aux_thm_prop_boundary_glb_nonneg Q E.toClosedForm GammaE q _ _ (hAE p 0)
  have hF0 := aux_thm_prop_boundary_glb_nonneg Q F.toClosedForm GammaF q _ _ (hAF p 0)
  exact aux_thm_prop_reciprocal_saving m M (3 / 8) _ _ hm hmM
    (by norm_num) (by norm_num) hF0
    (aux_thm_prop_affine_lower_V m M ck _ _ hE0 hck (hconc p))

end Branches
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Eligibility means that both actual cubes exist in the bounded catalogue.
It imposes no demand at an unrepresented coarse scale. -/
def aux_thm_prop_cell_available {d : ℕ}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (zc : SpatialCoordinates d) (s : ℝ) : Prop :=
  ∃ pair : ℕ × ℕ,
    z pair.1 = zc ∧ r pair.1 = s ∧ z pair.2 = zc ∧ r pair.2 = 3 * s

noncomputable def aux_thm_prop_cell_index {d : ℕ}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (zc : SpatialCoordinates d) (s : ℝ) : ℕ × ℕ := by
  classical
  exact if h : aux_thm_prop_cell_available z r zc s then Classical.choose h else (0, 0)

theorem aux_thm_prop_cell_index_spec {d : ℕ}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (zc : SpatialCoordinates d) (s : ℝ)
    (h : aux_thm_prop_cell_available z r zc s) :
    let pair := aux_thm_prop_cell_index z r zc s
    z pair.1 = zc ∧ r pair.1 = s ∧ z pair.2 = zc ∧ r pair.2 = 3 * s := by
  classical
  simpa only [aux_thm_prop_cell_index, dite_eq_left h] using Classical.choose_spec h

/-- The literal normalized relative matrix, with the already constructed
deterministic coefficient at this physical radius. -/
noncomputable def aux_thm_prop_relative_matrix {d : ℕ} {Ω : Type*}
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
    (r : ℕ → ℝ) (j : ℕ) (om : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.trace (AE j om))⁻¹ • (AF j om - ck (r j) • AE j om)

noncomputable def aux_thm_prop_cell_relative_matrix {d : ℕ} {Ω : Type*}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
    (zc : SpatialCoordinates d) (s : ℝ) (om : Ω) : Matrix (Fin d) (Fin d) ℝ := by
  classical
  exact if aux_thm_prop_cell_available z r zc s then
    aux_thm_prop_relative_matrix AE AF ck r (aux_thm_prop_cell_index z r zc s).1 om else 0

theorem aux_thm_prop_cell_relative_matrix_eq {d : ℕ} {Ω : Type*}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
    (zc : SpatialCoordinates d) (s : ℝ)
    (h : aux_thm_prop_cell_available z r zc s) (om : Ω) :
    aux_thm_prop_cell_relative_matrix z r AE AF ck zc s om =
      aux_thm_prop_relative_matrix AE AF ck r (aux_thm_prop_cell_index z r zc s).1 om := by
  classical
  exact ite_eq_left h

theorem aux_thm_prop_relative_matrix_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ) (r : ℕ → ℝ)
    (hAE : ∀ j i k, Measurable (fun om => AE j om i k))
    (hAF : ∀ j i k, Measurable (fun om => AF j om i k)) (j : ℕ)
    (a b : Fin d) :
    Measurable (fun om => aux_thm_prop_relative_matrix AE AF ck r j om a b) := by
  have htr : Measurable (fun om => Matrix.trace (AE j om)) :=
    Finset.measurable_sum _ (fun a _ => hAE j a a)
  exact htr.inv.mul ((hAF j a b).sub (measurable_const.mul (hAE j a b)))

theorem aux_thm_prop_cell_matrix_test_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
    (hAE : ∀ j i k, Measurable (fun om => AE j om i k))
    (hAF : ∀ j i k, Measurable (fun om => AF j om i k))
    (zc : SpatialCoordinates d) (s : ℝ) :
    Measurable (fun om => ∑ a : Fin d, ∑ b : Fin d,
      |aux_thm_prop_cell_relative_matrix z r AE AF ck zc s om a b|) := by
  classical
  by_cases h : aux_thm_prop_cell_available z r zc s
  · simp only [aux_thm_prop_cell_relative_matrix, ite_eq_left h]
    exact Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun b _ =>
      (aux_thm_prop_relative_matrix_measurable AE AF ck r hAE hAF _ a b).abs))
  · simp only [aux_thm_prop_cell_relative_matrix, ite_eq_right h, Matrix.zero_apply,
      abs_zero, Finset.sum_const_zero]
    exact measurable_const

/-- The selected catalogue indices really are present for a mass cell. -/
theorem aux_thm_prop_mass_cell_available
    {d : ℕ} {hd : 2 ≤ d} {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {NE NF : ℕ → ℕ} {m M : ℝ}
    (prepared : aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF m M)
    (jQ H1 Mm n : ℕ) (Cwidth gamma : ℝ) (sigma : Fin d → Fin Mm) (k : Fin d → ℤ)
    (hwidth : 1 ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma)
    (hpad : aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k)
    (hparent : closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) :
    aux_thm_prop_cell_available z r (aux_thm_prop_mass_center H1 Mm sigma n k)
      (aux_thm_prop_mass_side H1 n) := by
  obtain ⟨jC, jP, hzC, hrC, hzP, hrP, _⟩ :=
    prepared.mass_indices jQ H1 Mm n Cwidth gamma sigma k hwidth hpad hparent
  exact ⟨(jC, jP), hzC, hrC, hzP, hrP⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper

/-- PROPOSED SUPPLIER INTERFACE ONLY. No inhabitant is asserted by this definition.
This is the local-cell version of prop_conc: one actual observation and its
threefold enclosing cube, at one absolute scale. All physical response limits,
endpoint comparisons, and the real conditional sigma-algebra are retained.
The supplier must choose aexp, delta0 and Cp uniformly before k, the centre,
the endpoint gap and the model, in the same order as prop_conc. -/
def aux_thm_prop_local_concentration_input
    (d : ℕ) (I : _root_.SubdiffusiveProcess.Paper.in_J d) (C0 p delta0 Cp aexp : ℝ) : Prop :=
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr
          Sspace GN GE GF NE NF)
        (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
        (horder : ∀ᵐ omega ∂P, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
                m * (limitFormEnergy (GE i omega) u).toReal ≤
                    (limitFormEnergy (GF i omega) u).toReal ∧
                  (limitFormEnergy (GF i omega) u).toReal ≤
                    M * (limitFormEnergy (GE i omega) u).toReal)
        (zcell : SpatialCoordinates d) (k : ℕ)
        (cellIdx : ℕ)
        (hcell : z cellIdx = zcell ∧
          r cellIdx = (3 : ℝ) ^ (-(k : ℝ)))
        (paddedIdx : ℕ)
        (hpaddedIdx :
          z paddedIdx = zcell ∧
          r paddedIdx = 3 * ((3 : ℝ) ^ (-(k : ℝ))))
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hsymAE : ∀ omega, (AE omega).transpose = AE omega)
        (hsymAF : ∀ omega, (AF omega).transpose = AF omega)
        (hAE : ∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity))
                hPk
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega)
                  (NE j) zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AE omega).mulVec pvec)))
        (hAF : ∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity))
                hPk
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega)
                  (NF j) zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AF omega).mulVec pvec))),
      let ck : ℝ :=
        ∫ omega, Matrix.trace (AF omega) / Matrix.trace (AE omega) ∂P
      let Bk : Ω → Matrix (Fin d) (Fin d) ℝ := fun omega =>
        (Matrix.trace (AE omega))⁻¹ •
          (AF omega - ck • AE omega)
      let Band : ℕ → MeasurableSpace Ω := fun H =>
        ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (H : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      (ck ∈ Icc m M) ∧
      (∀ (i j : Fin d),
        ∫ omega, Bk omega i j ∂P = 0) ∧
      (eLpNorm
            (fun omega => ∑ i : Fin d, ∑ j : Fin d, |Bk omega i j|)
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * model.delta * (M - m))) ∧
      (∀ (H : ℕ),
        eLpNorm
            (fun omega =>
              ∑ i : Fin d, ∑ j : Fin d,
                |Bk omega i j -
                  ((P[fun omega => Bk omega i j | Band H]) omega)|)
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal
            (Cp * model.delta * (M - m) *
              (3 : ℝ) ^ (-aexp * (H : ℝ))))

end SubdiffusiveProcess.Paper

end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
section Family

variable {d : ℕ} {hd : 2 ≤ d} {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {NE NF : ℕ → ℕ} {m M : ℝ}

/-- Exact local-affine supplier target at the selected finite shifted grids.
The mesh threshold precedes the cell, its parent and the affine slope. The
global represented exponent is absent from the quantitative conclusion. -/
def aux_thm_prop_source_cell_approximation
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω) : Prop :=
  ∀ᵐ om ∂P, ∀ jQ,
    ∀ E : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
      (Sspace jQ) (GE jQ om) NE,
    ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
    ∀ _hu : GE jQ om f ∈ E.form.domain, ∀ c : ℝ, 0 < c →
    ∃ baseMesh : ℝ, 0 < baseMesh ∧
      ∀ (n : ℕ), 1 ≤ n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
      ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
      om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
      aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
      closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      let mu := E.gamma.measure (GE jQ om f) + ENNReal.ofReal c •
        volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
      (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
        ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
          (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) ∧
        (⇑(GE jQ om f) =ᵐ[volume.restrict
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))] U) ∧
        aux_thm_prop_affine_error (centeredCube (z jQ) (r jQ) (hr jQ))
          E.form.toClosedForm E.gamma (GE jQ om f) U c
          (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
            (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
              Set (SpatialCoordinates d))

/-- This intermediate proposition records local boundary estimates only.
The following theorem performs the actual mass selection. -/
def aux_thm_prop_boundary_selection
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω)
    (Uset : ℕ → Prop) : Prop :=
  ∀ᵐ om ∂P, ∀ jQ,
    ∀ (E : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
      (Sspace jQ) (GE jQ om) NE)
      (F : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
        (Sspace jQ) (GF jQ om) NF),
    ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
    ∀ hu : GE jQ om f ∈ E.form.domain, ∀ c : ℝ, 0 < c →
    ∃ baseMesh : ℝ, 0 < baseMesh ∧
      ∀ (n : ℕ), 1 ≤ n → Uset n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
      ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
      om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
      aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
      closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      let mu := E.gamma.measure (GE jQ om f) + ENNReal.ofReal c •
        volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
      (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
        ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
          (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
      Nonempty (aux_thm_prop_boundary_cell_data (centeredCube (z jQ) (r jQ) (hr jQ))
        E.form F.form E.gamma F.gamma m M ⟨GE jQ om f, hu⟩ c
        (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
          (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
            Set (SpatialCoordinates d)))

theorem aux_thm_prop_fine_candidates_from_boundary_selection
    (hm : 0 < m) (hM : 0 < M)
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω)
    (Uset : ℕ → Prop) (hU : (1 / 2 : ℝ) ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity Uset)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (hplanes : ∀ᵐ om ∂P, ∀ i,
      ∀ E : aux_thm_prop_limit_side d hd model H (field om) (z i) (r i) (hr i)
        (Sspace i) (GE i om) NE, ∀ u ∈ E.form.domain,
        ∀ (j : Fin d) (a : ℝ), E.gamma.measure u {x | x j = a} = 0)
    (hbad : ∀ i, ∀ᵐ om ∂P, ∃ B : (Fin d → Fin g.Mm) → ℝ,
      (∀ sigma, 0 ≤ B sigma) ∧
      ∀ sigma x, x ∈ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) →
      ∀ J : ℕ,
        (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
          ¬ om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n
            (aux_thm_prop_mass_point_idx g.H1 g.Mm sigma n x))} : ℝ) ≤
          (1 / 32 : ℝ) * (J : ℝ) + B sigma)
    (hlocal : aux_thm_prop_boundary_selection (hd := hd) (model := model) (H := H)
      (P := P) (field := field) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
      (GE := GE) (GF := GF) (NE := NE) (NF := NF) (m := m) (M := M) g Good Uset) :
    aux_thm_prop_fine_candidates (model := model) (H := H) (P := P) (field := field)
      (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GE) (GF := GF)
      (NE := NE) (NF := NF) hd m M := by
  have hbadAll := ae_all_iff.mpr hbad
  filter_upwards [horder, hplanes, hbadAll, hlocal] with om ho hp hb hl i E F f hfs hu c hc
  have hEdom := aux_thm_prop_domain_eq_of_energy E.form.toClosedForm (GE i om) E.energy_eq
  have hFdom := aux_thm_prop_domain_eq_of_energy F.form.toClosedForm (GF i om) F.energy_eq
  have hdom : E.form.domain = F.form.domain :=
    SetLike.coe_injective (hEdom.trans ((ho i).1.trans hFdom.symm))
  have hEe := aux_thm_prop_form_eq_toReal_energy E.form.toClosedForm (GE i om) E.energy_eq
  have hFe := aux_thm_prop_form_eq_toReal_energy F.form.toClosedForm (GF i om) F.energy_eq
  have hforms : ∀ w ∈ E.form.domain,
      m * E.form.form w w ≤ F.form.form w w ∧ F.form.form w w ≤ M * E.form.form w w := by
    intro w hw
    rw [hEe w hw, hFe w (hdom ▸ hw)]
    exact (ho i).2 w (hEdom ▸ hw)
  obtain ⟨Ccore, hcore⟩ := E.core
  have hsupp := aux_thm_prop_energy_measure_support E.gamma
    (centeredCube (z i) (r i) (hr i)).isOpen.measurableSet hcore hu
  obtain ⟨B, hB, hcount⟩ := hb i
  obtain ⟨baseMesh, hbase, hcells⟩ := hl i E F f hfs hu c hc
  exact aux_thm_prop_fine_cells_of_boundary_estimates d hd (z i) (r i) (hr i)
    E.form F.form (GE i om) (GF i om) hdom hEdom hFdom hEe hFe E.core F.core
    E.gamma F.gamma m M hm hM hforms ⟨GE i om f, hu⟩ c hc hsupp (hp i E _ hu)
    g Uset hU (fun sigma n k => om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k))
    B hB hcount baseMesh hbase _ rfl hcells

end Family
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Exact proposed local good-cell supplier. An inhabitant is NOT asserted
here. It combines the local affine estimate with the base-event chain bound
from lem_goodext/lem_prefix_limit on the finite actual shifted grids. The
relative concentration test is deliberately not a field of this structure.
Both original sources are retained, so the V argument uses the F source. -/
structure aux_thm_prop_local_affine_data
    {d : ℕ} {hd : 2 ≤ d} {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {NE NF : ℕ → ℕ} {m M : ℝ}
    (prepared : aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF m M)
    (g : aux_thm_prop_selection_geometry d) (c0 : ℝ) where
  Good : ℕ → SpatialCoordinates d → Set Ω
  measurable : ∀ n zc, MeasurableSet (Good n zc)
  chain : ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
    ∃ Bbase : Ω → ℝ, Measurable Bbase ∧ (∀ om, 0 ≤ Bbase om) ∧
      ∀ᵐ om ∂P, ∀ J : ℕ, 1 ≤ J →
      ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth g.H1),
        (Nat.card {j : Fin J // ¬ om ∈ Good (j.val + 1)
          (descendantCenter (subdivisionHalfWidth g.H1)
            (aux_thm_prop_mass_center g.H1 g.Mm sigma 0 k) 1 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
          ((1 / 32 : ℝ) / 2) * (J : ℝ) + Bbase om
  ellipticity : ∀ᵐ om ∂P, ∀ n zc,
    aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
    om ∈ Good n zc →
    let jC := (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1
    0 < Matrix.trace (prepared.AE jC om) ∧
      ∀ p : Fin d → ℝ,
        c0 * Matrix.trace (prepared.AE jC om) * (p ⬝ᵥ p) ≤
          p ⬝ᵥ (prepared.AE jC om).mulVec p
  approximationE : aux_thm_prop_source_cell_approximation
    (hd := hd) (model := model) (H := H) (P := P) (field := field)
    (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GE) (NE := NE) g Good
  approximationF : aux_thm_prop_source_cell_approximation
    (hd := hd) (model := model) (H := H) (P := P) (field := field)
    (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GF) (NE := NF) g Good

end SubdiffusiveProcess.Paper

end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

def aux_thm_prop_extra_good {d : ℕ} {Ω : Type*}
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
    (H1 : ℕ) (BaseGood : ℕ → SpatialCoordinates d → Set Ω) (c0 m M : ℝ) :
    ℕ → SpatialCoordinates d → Set Ω := fun n zc =>
  {om | om ∈ BaseGood n zc ∧
    (∑ i : Fin d, ∑ j : Fin d,
      |aux_thm_prop_cell_relative_matrix z r AE AF ck zc (aux_thm_prop_mass_side H1 n) om i j|) ≤
        (1 / 8 : ℝ) * c0 * (M - m)}

section Family

variable {d : ℕ} {hd : 2 ≤ d} {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {NE NF : ℕ → ℕ} {m M : ℝ}
    (prepared : aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF m M)
    (g : aux_thm_prop_selection_geometry d)

/-- Identify the genuine boundary minima at the deterministically selected
catalogue indices of each padded mass cell, in the actual enclosing root. -/
theorem aux_thm_prop_mass_cell_minima :
    ∀ᵐ om ∂P, ∀ (jQ n : ℕ) (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
      aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
      closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      let zc := aux_thm_prop_mass_center g.H1 g.Mm sigma n k
      let s := aux_thm_prop_mass_side g.H1 n
      let q := (centeredCube zc s (aux_thm_prop_grid_side_pos g.H1 n) : Set (SpatialCoordinates d))
      let jC := (aux_thm_prop_cell_index z r zc s).1
      (∀ E : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
          (Sspace jQ) (GE jQ om) NE, ∀ (p : Fin d → ℝ) (b : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          E.form.toClosedForm E.gamma q (fun x => (∑ i, p i * x i) + b))
          ((volume q).toReal * (p ⬝ᵥ (prepared.AE jC om).mulVec p))) ∧
      (∀ F : aux_thm_prop_limit_side d hd model H (field om) (z jQ) (r jQ) (hr jQ)
          (Sspace jQ) (GF jQ om) NF, ∀ (p : Fin d → ℝ) (b : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          F.form.toClosedForm F.gamma q (fun x => (∑ i, p i * x i) + b))
          ((volume q).toReal * (p ⬝ᵥ (prepared.AF jC om).mulVec p))) := by
  filter_upwards [prepared.minima] with om hmin jQ n sigma k hpad hparent
  let zc := aux_thm_prop_mass_center g.H1 g.Mm sigma n k
  let s := aux_thm_prop_mass_side g.H1 n
  have havail := aux_thm_prop_mass_cell_available prepared jQ g.H1 g.Mm n
    g.width g.gamma sigma k g.padded_width hpad hparent
  have hs := aux_thm_prop_cell_index_spec z r zc s havail
  let jC := (aux_thm_prop_cell_index z r zc s).1
  let jP := (aux_thm_prop_cell_index z r zc s).2
  have hzc : z jC = zc := hs.1
  have hrc : r jC = s := hs.2.1
  have hzp : z jP = zc := hs.2.2.1
  have hrp : r jP = 3 * s := hs.2.2.2
  have hz : z jC = z jP := hs.1.trans hs.2.2.1.symm
  have hradius : r jP = 3 * r jC := hs.2.2.2.trans (congrArg (3 * ·) hs.2.1.symm)
  have hpQ : (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) := by
    have hthree := aux_thm_prop_mass_padded_threefold g.H1 g.Mm n g.width g.gamma
      sigma k g.padded_width hpad
    have hsub := subset_closure.trans (hthree.trans (subset_closure.trans hparent))
    simpa only [hzp, hrp] using hsub
  have hm := hmin jQ jP jC hz hradius hpQ
  constructor
  · intro E p b
    simpa only [hzc, hrc] using (hm.1 E p b).1
  · intro F p b
    simpa only [hzc, hrc] using (hm.2 F p b).1

theorem aux_thm_prop_extra_good_concentration
    (c0 : ℝ) (hc0 : 0 < c0) (hmM : m ≤ M)
    (affine : aux_thm_prop_local_affine_data prepared g c0) :
    ∀ᵐ om ∂P, ∀ n zc,
      aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
      om ∈ aux_thm_prop_extra_good z r prepared.AE prepared.AF prepared.ck
        g.H1 affine.Good c0 m M n zc →
      let s := aux_thm_prop_mass_side g.H1 n
      let jC := (aux_thm_prop_cell_index z r zc s).1
      let q := (centeredCube zc s (aux_thm_prop_grid_side_pos g.H1 n) : Set (SpatialCoordinates d))
      ∀ p : Fin d → ℝ,
        |(volume q).toReal * (p ⬝ᵥ (prepared.AF jC om).mulVec p) -
          prepared.ck s * ((volume q).toReal * (p ⬝ᵥ (prepared.AE jC om).mulVec p))| ≤
          (1 / 8 : ℝ) * (M - m) *
            ((volume q).toReal * (p ⬝ᵥ (prepared.AE jC om).mulVec p)) := by
  filter_upwards [affine.ellipticity] with om hell n zc havail hgood
  have hs := aux_thm_prop_cell_index_spec z r zc (aux_thm_prop_mass_side g.H1 n) havail
  have hsmall := hgood.2
  simp only [aux_thm_prop_cell_relative_matrix_eq z r prepared.AE prepared.AF
    prepared.ck zc _ havail] at hsmall
  obtain ⟨htr, hcoer⟩ := hell n zc havail hgood.1
  dsimp only
  intro p
  have htest := aux_thm_prop_concentration_matrix_test
    (prepared.AE (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1 om)
    (prepared.AF (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1 om)
    (aux_thm_prop_relative_matrix prepared.AE prepared.AF prepared.ck r
      (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1 om)
    (prepared.ck (r (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1))
    (volume (centeredCube zc (aux_thm_prop_mass_side g.H1 n)
      (aux_thm_prop_grid_side_pos g.H1 n) : Set (SpatialCoordinates d))).toReal
    (1 / 8) c0 m M (by norm_num) hc0 hmM
    (centeredCube_volume_pos zc (aux_thm_prop_grid_side_pos g.H1 n)) htr hcoer rfl hsmall p
  simpa only [hs.2.1, mul_assoc] using htest

end Family
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

def aux_thm_prop_mass_good_counts {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j)
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω) : Prop :=
  ∀ i, ∀ᵐ om ∂P, ∃ B : (Fin d → Fin g.Mm) → ℝ,
    (∀ sigma, 0 ≤ B sigma) ∧
    ∀ sigma x, x ∈ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) →
    ∀ J : ℕ,
      (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
        ¬ om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n
          (aux_thm_prop_mass_point_idx g.H1 g.Mm sigma n x))} : ℝ) ≤
        (1 / 32 : ℝ) * (J : ℝ) + B sigma

section Family

variable {d : ℕ} {hd : 2 ≤ d} {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {field : Ω → BilateralField d}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {NE NF : ℕ → ℕ} {m M : ℝ}
    (prepared : aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF m M)
    (g : aux_thm_prop_selection_geometry d) (c0 : ℝ) (hc0 : 0 < c0) (hmM : m ≤ M)
    (affine : aux_thm_prop_local_affine_data prepared g c0)

include hc0 hmM

theorem aux_thm_prop_boundary_selection_U :
    aux_thm_prop_boundary_selection (hd := hd) (model := model) (H := H)
      (P := P) (field := field) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
      (GE := GE) (GF := GF) (NE := NE) (NF := NF) (m := m) (M := M) g
      (aux_thm_prop_extra_good z r prepared.AE prepared.AF prepared.ck g.H1 affine.Good c0 m M)
      (fun n => prepared.ck (aux_thm_prop_mass_side g.H1 n) ≤ (m + M) / 2) := by
  have hmin := aux_thm_prop_mass_cell_minima prepared g
  have hconc := aux_thm_prop_extra_good_concentration prepared g c0 hc0 hmM affine
  filter_upwards [hmin, hconc, affine.approximationE] with om hmins hconcs happs
    jQ E F f hfs hu c hc
  obtain ⟨baseMesh, hbase, happ⟩ := happs jQ E f hfs hu c hc
  refine ⟨baseMesh, hbase, ?_⟩
  intro n hn hU hmesh sigma k hgood hpad hparent
  dsimp only
  intro hmass
  obtain ⟨U, hUcont, hrep, herror⟩ := happ n hn hmesh sigma k hgood.1 hpad hparent hmass
  have hminimum := hmins jQ n sigma k hpad hparent
  have havail := aux_thm_prop_mass_cell_available prepared jQ g.H1 g.Mm n
    g.width g.gamma sigma k g.padded_width hpad hparent
  have htest := hconcs n _ havail hgood
  exact aux_thm_prop_boundary_cell_U (centeredCube (z jQ) (r jQ) (hr jQ))
    E.form F.form E.gamma F.gamma m M (prepared.ck (aux_thm_prop_mass_side g.H1 n))
    _ _ _ (hminimum.1 E) (hminimum.2 F) htest hU ⟨GE jQ om f, hu⟩ U hUcont hrep c herror

theorem aux_thm_prop_boundary_selection_V (hm : 0 < m) :
    aux_thm_prop_boundary_selection (hd := hd) (model := model) (H := H)
      (P := P) (field := field) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
      (GE := GF) (GF := GE) (NE := NF) (NF := NE) (m := M⁻¹) (M := m⁻¹) g
      (aux_thm_prop_extra_good z r prepared.AE prepared.AF prepared.ck g.H1 affine.Good c0 m M)
      (fun n => ¬ prepared.ck (aux_thm_prop_mass_side g.H1 n) ≤ (m + M) / 2) := by
  have hmin := aux_thm_prop_mass_cell_minima prepared g
  have hconc := aux_thm_prop_extra_good_concentration prepared g c0 hc0 hmM affine
  filter_upwards [hmin, hconc, affine.approximationF] with om hmins hconcs happs
    jQ F E f hfs hu c hc
  obtain ⟨baseMesh, hbase, happ⟩ := happs jQ F f hfs hu c hc
  refine ⟨baseMesh, hbase, ?_⟩
  intro n hn hV hmesh sigma k hgood hpad hparent
  dsimp only
  intro hmass
  obtain ⟨U, hUcont, hrep, herror⟩ := happ n hn hmesh sigma k hgood.1 hpad hparent hmass
  have hminimum := hmins jQ n sigma k hpad hparent
  have havail := aux_thm_prop_mass_cell_available prepared jQ g.H1 g.Mm n
    g.width g.gamma sigma k g.padded_width hpad hparent
  have htest := hconcs n _ havail hgood
  exact aux_thm_prop_boundary_cell_V (centeredCube (z jQ) (r jQ) (hr jQ))
    E.form F.form E.gamma F.gamma m M (prepared.ck (aux_thm_prop_mass_side g.H1 n))
    _ _ _ (hminimum.1 E) (hminimum.2 F) htest hm hmM (le_of_lt (lt_of_not_ge hV))
    ⟨GF jQ om f, hu⟩ U hUcont hrep c herror

/-- The actual U/V choice is made once for the whole probability space. Each
branch selects arbitrarily fine cells for its own source and energy measure. -/
theorem aux_thm_prop_fine_dichotomy_from_local_estimates
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hm : 0 < m) (hM : 0 < M)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (hbad : aux_thm_prop_mass_good_counts P z r hr g
      (aux_thm_prop_extra_good z r prepared.AE prepared.AF prepared.ck g.H1 affine.Good c0 m M)) :
    aux_thm_prop_fine_candidates (model := model) (H := H) (P := P) (field := field)
      (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GE) (GF := GF)
      (NE := NE) (NF := NF) hd m M ∨
    aux_thm_prop_fine_candidates (model := model) (H := H) (P := P) (field := field)
      (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GF) (GF := GE)
      (NE := NF) (NF := NE) hd M⁻¹ m⁻¹ := by
  have hU := aux_thm_prop_boundary_selection_U prepared g c0 hc0 hmM affine
  have hV := aux_thm_prop_boundary_selection_V prepared g c0 hc0 hmM affine hm
  rcases aux_thm_prop_half_density
      (fun n => prepared.ck (aux_thm_prop_mass_side g.H1 n) ≤ (m + M) / 2) with hdens | hdens
  · left
    exact aux_thm_prop_fine_candidates_from_boundary_selection hm hM g _ _ hdens horder
      (prepared.planes.mono fun om h i => (h i).1) hbad hU
  · right
    exact aux_thm_prop_fine_candidates_from_boundary_selection (inv_pos.mpr hM)
      (inv_pos.mpr hm) g _ _ hdens (aux_thm_prop_order_swap m M hm hM horder)
      (prepared.planes.mono fun om h i => (h i).2) hbad hV

end Family
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

@[instance_reducible]
def aux_thm_prop_scale_band {d : ℕ} {Ω : Type*}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (field : Ω → BilateralField d) (k Hband : ℕ) : MeasurableSpace Ω :=
  ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (Hband : ℤ)),
    (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
      (fun om : Ω => field om j)

/-- Moment and conditional-band bounds for the actual selected cell matrices.
Unrepresented cells have the identically zero test. -/
def aux_thm_prop_cell_matrix_moments {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
    (H1 : ℕ) (p C aexp : ℝ) : Prop :=
  ∀ n zc,
    let B := aux_thm_prop_cell_relative_matrix z r AE AF ck zc (aux_thm_prop_mass_side H1 n)
    eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B om i j|)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal C ∧
    ∀ Hband : ℕ,
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
        |B om i j - (P[fun om => B om i j | aux_thm_prop_scale_band field (H1 * n) Hband]) om|)
        (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-aexp * (Hband : ℝ)))

theorem aux_thm_prop_mass_side_rpow (H1 n : ℕ) :
    aux_thm_prop_mass_side H1 n = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) := by
  rw [aux_thm_prop_mass_side_zpow, ← Real.rpow_intCast]
  simp only [Int.cast_neg, Int.cast_natCast]

theorem aux_thm_prop_cell_moments_mask
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
    (H1 : ℕ) (p C aexp : ℝ)
    (hactual : ∀ n zc, aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side H1 n) →
      let B := aux_thm_prop_relative_matrix AE AF ck r
        (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B om i j|)
        (ENNReal.ofReal p) P ≤ ENNReal.ofReal C ∧
      ∀ Hband : ℕ,
        eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
          |B om i j - (P[fun om => B om i j | aux_thm_prop_scale_band field (H1 * n) Hband]) om|)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-aexp * (Hband : ℝ)))) :
    aux_thm_prop_cell_matrix_moments P field z r AE AF ck H1 p C aexp := by
  classical
  intro n zc
  by_cases h : aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side H1 n)
  · simpa only [aux_thm_prop_cell_relative_matrix, ite_eq_left h] using hactual n zc h
  · simp only [aux_thm_prop_cell_relative_matrix, ite_eq_right h, Matrix.zero_apply,
      abs_zero, Finset.sum_const_zero, ← Pi.zero_def, condExp_zero, Pi.zero_apply, sub_zero, eLpNorm_zero,
      zero_le, implies_true, and_self]

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Local relative moments produce counts on the actual finite shifted grids.
The disorder threshold is fixed before the model and the endpoint gap. -/
theorem aux_thm_prop_matrix_mass_counts
    (d : ℕ) (hd : 2 ≤ d) (g : aux_thm_prop_selection_geometry d)
    (c0 : ℝ) (hc0 : 0 < c0) (p : ℝ) (hp : 0 < p)
    (Cp : ℝ) (hCp : 0 < Cp) (aexp : ℝ) (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / (1 / 32 : ℝ)) *
      (((g.H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (field : Ω → BilateralField d) (_hfield : Measurable field)
      (_hlaw : Measure.map field P = (chaosSampleLaw model).toMeasure)
      (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
      (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ → ℝ)
      (_hAE : ∀ j i k, Measurable (fun om => AE j om i k))
      (_hAF : ∀ j i k, Measurable (fun om => AF j om i k))
      (m M : ℝ) (_hmM : m ≤ M)
      (BaseGood : ℕ → SpatialCoordinates d → Set Ω),
      (∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
        ∃ Bbase : Ω → ℝ, Measurable Bbase ∧ (∀ om, 0 ≤ Bbase om) ∧
          ∀ᵐ om ∂P, ∀ J : ℕ, 1 ≤ J →
          ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth g.H1),
            (Nat.card {j : Fin J // ¬ om ∈ BaseGood (j.val + 1)
              (descendantCenter (subdivisionHalfWidth g.H1)
                (aux_thm_prop_mass_center g.H1 g.Mm sigma 0 k) 1 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
              ((1 / 32 : ℝ) / 2) * (J : ℝ) + Bbase om) →
      aux_thm_prop_cell_matrix_moments P field z r AE AF ck g.H1 p
        (Cp * model.delta * (M - m)) aexp →
      aux_thm_prop_mass_good_counts P z r hr g
        (aux_thm_prop_extra_good z r AE AF ck g.H1 BaseGood c0 m M) := by
  obtain ⟨delta0, hdelta0, hchain⟩ := aux_thm_prop_concentration_extra_chain
    d g.H1 g.H1_pos (1 / 8) (by norm_num) (1 / 32) (by norm_num) (by norm_num)
    c0 hc0 p hp Cp hCp aexp haexp hpRate
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Ω _ P _ field hfield hlaw z r hr AE AF ck hAE hAF m M hmM
    BaseGood hbase hmom
  let ExtraGood := aux_thm_prop_extra_good z r AE AF ck g.H1 BaseGood c0 m M
  have hroot (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ) :
      ∀ᵐ om ∂P, ∃ B : ℝ, 0 ≤ B ∧
        ∀ (J : ℕ) (pi : Fin J → OddGridIndex d (subdivisionHalfWidth g.H1)),
          (Nat.card {j : Fin J // ¬ om ∈ ExtraGood (j.val + 1)
            (descendantCenter (subdivisionHalfWidth g.H1)
              (aux_thm_prop_mass_center g.H1 g.Mm sigma 0 k) 1 (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
            (1 / 32 : ℝ) * (J : ℝ) + B := by
    let zc (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth g.H1)) :=
      descendantCenter (subdivisionHalfWidth g.H1)
        (aux_thm_prop_mass_center g.H1 g.Mm sigma 0 k) 1 n w
    let Bk (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth g.H1)) :=
      aux_thm_prop_cell_relative_matrix z r AE AF ck (zc n w) (aux_thm_prop_mass_side g.H1 n)
    obtain ⟨Bextra, hBextraMeas, hBextraNonneg, hExtra⟩ :=
      hchain model hmodel Ω P field hfield hlaw m M hmM Bk
        (fun n w => aux_thm_prop_cell_matrix_test_measurable z r AE AF ck hAE hAF (zc n w) _)
        (fun n w => (hmom n (zc n w)).1)
        (fun n w Hband => (hmom n (zc n w)).2 Hband)
    obtain ⟨Bbase, hBbaseMeas, hBbaseNonneg, hBase⟩ := hbase sigma k
    let Good2 (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth g.H1)) : Set Ω :=
      {om | (∑ i : Fin d, ∑ j : Fin d, |Bk n w om i j|) ≤ (1 / 8 : ℝ) * c0 * (M - m)}
    obtain ⟨Bnew, _, hBnew, hNew⟩ := aux_cor_32_hBound_of_base_and_extra g.H1 P
      (fun n w => BaseGood n (zc n w)) Good2 (1 / 32) Bbase Bextra
      hBbaseMeas hBbaseNonneg hBextraMeas hBextraNonneg hBase hExtra
    filter_upwards [hNew] with om hom
    refine ⟨Bnew om, hBnew om, ?_⟩
    intro J pi
    by_cases hJ : 1 ≤ J
    · exact hom J hJ pi
    · have hJ0 : J = 0 := by omega
      subst J
      simpa only [Nat.card_of_isEmpty, Nat.cast_zero, mul_zero, zero_add] using hBnew om
  intro i
  exact aux_thm_prop_mass_bad_of_tree_ae P d g.H1 g.Mm hd g.H1_pos g.Mm_two
    (z i) (r i) (hr i) ExtraGood (1 / 32) hroot

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Proposed uniform affine/base-good supplier. This is a proposition only,
not a proof. All choices precede the model, endpoints, floor and sources.
There is no endpoint-gap or proportionality assumption in this interface. -/
def aux_thm_prop_uniform_local_affine_input
    (d : ℕ) (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Cresp : ℝ) : Prop :=
    ∃ (g : aux_thm_prop_selection_geometry d) (c0 delta0 : ℝ),
      0 < c0 ∧ 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) →
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) →
        (hRm : Rm.C ≤ Cresp) →
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) →
        (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg) →
        (hBounds : _root_.SubdiffusiveProcess.Paper.aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF) →
        (hEnum : _root_.SubdiffusiveProcess.Paper.in_represented_enum d z r hr) →
        ∀ {beta t : ℝ}, (@aux_thm_prop_catalogue d hd _ _ model H Ω _ P hJoint.1 field z r hr Sspace NE NF
          (aux_thm_prop_alpha d hd) (1 / 128) beta t) →
        ∀ m M : ℝ,
          ∀ prepared : aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF m M,
            Nonempty (aux_thm_prop_local_affine_data prepared g c0)

/-- Proposed uniform one-cell concentration supplier. Interpolation is an
existing dimension-level proposition recovered from hBounds and the joint
limits when this is applied. No interpolation premise is added to thm_prop. -/
def aux_thm_prop_uniform_local_concentration_input
    (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d) : Prop :=
  ∃ aexp : ℝ, 0 < aexp ∧
    ∀ C0 : ℝ, 1 ≤ C0 → ∀ p : ℝ, 0 < p →
      ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
        (CubeFractionalInterpolationInput d hd →
          aux_thm_prop_local_concentration_input d I C0 p delta0 Cp aexp)

end SubdiffusiveProcess.Paper

end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Specialize a one-cell concentration supplier to the actual measurable
matrix bank and the deterministic catalogue selection. No outside-root index
and no artificial matrix is used on an eligible cell. -/
theorem aux_thm_prop_cell_moments_of_local_concentration
    (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (C0 p delta0 Cp aexp : ℝ)
    (hsupplier : aux_thm_prop_local_concentration_input d I C0 p delta0 Cp aexp)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (hmodel : model.delta ≤ delta0)
    (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
    (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (prepared : aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF m M)
    (H1 : ℕ) :
    aux_thm_prop_cell_matrix_moments P field z r prepared.AE prepared.AF prepared.ck H1 p
      (Cp * model.delta * (M - m)) aexp := by
  apply aux_thm_prop_cell_moments_mask
  intro n zc havail
  let jC := (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1
  let jP := (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).2
  have hspec := aux_thm_prop_cell_index_spec z r zc (aux_thm_prop_mass_side H1 n) havail
  have hzc : z jC = zc := hspec.1
  have hzp : z jP = zc := hspec.2.2.1
  have hrc : r jC = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) :=
    hspec.2.1.trans (aux_thm_prop_mass_side_rpow H1 n)
  have hrp : r jP = 3 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) :=
    hspec.2.2.2.trans (congrArg (3 * ·) (aux_thm_prop_mass_side_rpow H1 n))
  have hQ : centeredCube (z jC) (r jC) (hr jC) =
      centeredCube zc ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity) := by
    apply TopologicalSpace.Opens.ext
    change Metric.ball (z jC) (r jC / 2) =
      Metric.ball zc (((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) / 2)
    rw [hzc, hrc]
  have hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube zc ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity)),
      ‖(u : SobolevData (centeredCube zc ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube zc ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity))) u‖ := by
    have hp := prepared.hP jC
    rw [hQ] at hp
    exact hp
  have hE : ∀ᵐ om ∂P,
      aux_thm_prop_affine_converges model H (field om) zc
        ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity) NE hPk (prepared.AE jC om) := by
    filter_upwards [prepared.converges] with om h
    simpa only [hzc, hrc] using (h jC).1
  have hF : ∀ᵐ om ∂P,
      aux_thm_prop_affine_converges model H (field om) zc
        ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity) NF hPk (prepared.AF jC om) := by
    filter_upwards [prepared.converges] with om h
    simpa only [hzc, hrc] using (h jC).2
  have hout := hsupplier model hmodel Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF
    hJoint m M hm hmM hM horder zc (H1 * n) jC ⟨hzc, hrc⟩ jP ⟨hzp, hrp⟩ hPk
    (prepared.AE jC) (prepared.AF jC) (prepared.symmetricE jC) (prepared.symmetricF jC) hE hF
  dsimp only at hout
  rw [prepared.expected jC] at hout
  exact ⟨hout.2.2.1, hout.2.2.2⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper

/-- Choose the moment order after the geometric subdivision, and before the
model or endpoint gap. This uses exactly the proposed uniform local supplier. -/
theorem aux_thm_prop_local_concentration_parameters
    (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (hinput : aux_thm_prop_uniform_local_concentration_input d hd I)
    (C0 : ℝ) (hC0 : 1 ≤ C0) (H1 : ℕ) (theta : ℝ) :
    ∃ p aexp Cp delta0 : ℝ,
      0 < p ∧ 0 < aexp ∧ 0 < Cp ∧ 0 < delta0 ∧
      2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3 ∧
      (CubeFractionalInterpolationInput d hd →
        aux_thm_prop_local_concentration_input d I C0 p delta0 Cp aexp) := by
  obtain ⟨aexp, haexp, hsupplier⟩ := hinput
  let A : ℝ := 2 * Real.log 2 + 1 + (48 / theta) *
    (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)
  let p : ℝ := max 1 (2 * A / (aexp * Real.log 3))
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha : 0 < aexp * Real.log 3 := mul_pos haexp (Real.log_pos (by norm_num))
  have hrate : 2 * A ≤ p * aexp * Real.log 3 := by
    have h := (div_le_iff₀ ha).mp (le_max_right 1 (2 * A / (aexp * Real.log 3)))
    exact h.trans_eq (mul_assoc p aexp (Real.log 3)).symm
  obtain ⟨delta0, Cp, hdelta0, hCp, hconc⟩ := hsupplier C0 hC0 p hp
  exact ⟨p, aexp, Cp, delta0, hp, haexp, hCp, hdelta0, hrate, hconc⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Full fine-cell selection from the two exact local upstream suppliers.
The actual matrices, minima, floors, both density branches, all-chain counts,
and every parameter-order constraint are assembled in the proof. -/
theorem aux_thm_prop_select_from_uniform_suppliers
    (d : ℕ) (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (C0 : ℝ) (hC0 : 1 ≤ C0) (Cresp : ℝ)
    (hUniformAffine : aux_thm_prop_uniform_local_affine_input d hd I Cresp)
    (hUniformConcentration : aux_thm_prop_uniform_local_concentration_input d hd I) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) →
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) →
        (hRm : Rm.C ≤ Cresp) →
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) →
        (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg) →
        (hBounds : _root_.SubdiffusiveProcess.Paper.aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF) →
        (hEnum : _root_.SubdiffusiveProcess.Paper.in_represented_enum d z r hr) →
        ∀ {beta t : ℝ}, (@aux_thm_prop_catalogue d hd _ _ model H Ω _ P hJoint.1 field z r hr Sspace NE NF
          (aux_thm_prop_alpha d hd) (1 / 128) beta t) →
        (∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega) →
        (∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) →
        ∀ cL cU : ℝ,
          (∀ᵐ omega ∂P, sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = cL ∧
            sInf (aux_thm_prop_upperSet z r hr GE GF omega) = cU) →
          cL < cU →
          aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF cL cU →
          aux_thm_prop_fine_candidates (model := model) (H := H) (P := P)
            (field := field) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
            (GE := GE) (GF := GF) (NE := NE) (NF := NF) hd cL cU ∨
          aux_thm_prop_fine_candidates (model := model) (H := H) (P := P)
            (field := field) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
            (GE := GF) (GF := GE) (NE := NF) (NF := NE) hd cU⁻¹ cL⁻¹ := by
  obtain ⟨g, c0, deltaA, hc0, hdeltaA, hAffine⟩ := hUniformAffine
  obtain ⟨p, aexp, Cp, deltaC, hp, haexp, hCp, hdeltaC, hRate, hConc⟩ :=
    aux_thm_prop_local_concentration_parameters d hd I hUniformConcentration
      C0 hC0 g.H1 (1 / 32)
  obtain ⟨deltaCount, hdeltaCount, hCount⟩ := aux_thm_prop_matrix_mass_counts
    d hd g c0 hc0 p hp Cp hCp aexp haexp hRate
  refine ⟨min deltaA (min deltaC deltaCount), lt_min hdeltaA (lt_min hdeltaC hdeltaCount), ?_⟩
  intro _ _ model hmodel H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint
    Rm hRm Sreg It hBounds hEnum beta t hCat hcomp hnz m M hdet hlt prepared
  have : IsProbabilityMeasure P := hJoint.1
  have hmodelA : model.delta ≤ deltaA := hmodel.trans (min_le_left _ _)
  have hmodelC : model.delta ≤ deltaC :=
    hmodel.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmodelCount : model.delta ≤ deltaCount :=
    hmodel.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨affine⟩ := hAffine model hmodelA H Ω P field z r hr Sspace GN GE GF NE NF hJoint
    Rm hRm Sreg It hBounds hEnum hCat m M prepared
  have hopt := aux_thm_prop_endpoint_order hd C0 hC0 m M hcomp hnz hdet
  obtain ⟨om, hb⟩ := hopt.exists
  have hm : 0 < m := (inv_pos.mpr (zero_lt_one.trans_le hC0)).trans_le hb.1
  have hM : 0 < M := hm.trans hlt
  have horder := hopt.mono fun _ h => h.2.2.2
  have hInterp := aux_thm_prop_interpolation_of_joint_bounds hd hJoint hBounds
  have hmom := aux_thm_prop_cell_moments_of_local_concentration d hd I C0 p deltaC Cp aexp
    (hConc hInterp) model hmodelC Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF hJoint
    m M hb.1 hlt.le hb.2.2.1 horder prepared g.H1
  have hbad := hCount model hmodelCount Ω P field hJoint.2.1 hJoint.2.2.1 z r hr
    prepared.AE prepared.AF prepared.ck prepared.measurableE prepared.measurableF
    m M hlt.le affine.Good affine.chain hmom
  exact aux_thm_prop_fine_dichotomy_from_local_estimates prepared g c0 hc0 hlt.le affine
    hm hM horder hbad

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology

namespace SubdiffusiveProcess.Paper

/-- Factor an actual matrix limit through the canonical field. This needs
neither a completed probability space nor a catalogue outside the cell. -/
theorem aux_thm_prop_matrix_limit_factor
    {d : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (μ : Measure Ξ) (field : Ω → Ξ)
    (hfield : Measurable field) (hlaw : P.map field = μ)
    (A : ℕ → Ξ → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ n, Measurable (A n)) (L : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hlim : ∀ᵐ om ∂P, Tendsto (fun n => A n (field om)) atTop (𝓝 (L om))) :
    ∃ g : Ξ → Matrix (Fin d) (Fin d) ℝ, Measurable g ∧
      (∀ᵐ om ∂P, g (field om) = L om) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (g x)) := by
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  let : TopologicalSpace.IsCompletelyMetrizableSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyMetrizableSpace (Fin d → Fin d → ℝ))
  let : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let g : Ξ → Matrix (Fin d) (Fin d) ℝ :=
    fun x => limUnder atTop (fun n => A n x)
  have hg : Measurable g :=
    (StronglyMeasurable.limUnder (fun n => (hA n).stronglyMeasurable)).measurable
  have heq : ∀ᵐ om ∂P, g (field om) = L om :=
    hlim.mono fun _ h => h.limUnder_eq
  refine ⟨g, hg, heq, ?_⟩
  rw [← hlaw, ae_map_iff hfield.aemeasurable (measurableSet_tendsto_fun hA hg)]
  filter_upwards [hlim, heq] with om h he
  rwa [he]

/-- A common infrared gauge cancels after passing a cell's matrix responses
to their genuine limits. The normalization is only required to be measurable;
no continuity at singular matrices and no off-event equivariance is assumed. -/
theorem aux_thm_prop_matrix_pair_law
    {d : ℕ} {Ω Ξ Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Y]
    (P : Measure Ω) (μ : Measure Ξ) (field : Ω → Ξ)
    (hfield : Measurable field) (hlaw : P.map field = μ)
    (T : Ξ → Ξ) (hT : MeasurePreserving T μ μ)
    (A B : ℕ → Ξ → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ᵐ om ∂P, Tendsto (fun n => A n (field om)) atTop (𝓝 (AE om)))
    (hAF : ∀ᵐ om ∂P, Tendsto (fun n => B n (field om)) atTop (𝓝 (AF om)))
    (L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (c : Ξ → ℝ)
    (hcov : ∀ᵐ x ∂μ, c x ≠ 0 ∧ ∀ n,
      A n (T x) = c x • L (A n x) ∧ B n (T x) = c x • L (B n x))
    (N : (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) → Y)
    (hN : Measurable N) (S : Y → Y) (hS : Measurable S)
    (hscale : ∀ (a b : Matrix (Fin d) (Fin d) ℝ) (t : ℝ), t ≠ 0 →
      N (t • a, t • b) = N (a, b))
    (htransform : ∀ a b, N (L a, L b) = S (N (a, b))) :
    P.map (fun om => N (AE om, AF om)) =
      P.map (fun om => S (N (AE om, AF om))) := by
  obtain ⟨gE, hmE, heE, hlE⟩ :=
    aux_thm_prop_matrix_limit_factor P μ field hfield hlaw A hA AE hAE
  obtain ⟨gF, hmF, heF, hlF⟩ :=
    aux_thm_prop_matrix_limit_factor P μ field hfield hlaw B hB AF hAF
  have hequiv : ∀ᵐ x ∂μ, N (gE (T x), gF (T x)) = S (N (gE x, gF x)) := by
    filter_upwards [hlE, hlF, hT.quasiMeasurePreserving.ae hlE,
      hT.quasiMeasurePreserving.ae hlF, hcov] with x hE hF hET hFT hc
    have hgE : gE (T x) = c x • L (gE x) :=
      tendsto_nhds_unique hET
        (((L.continuous.tendsto _).comp hE).const_smul (c x) |>.congr
          fun n => (hc.2 n).1.symm)
    have hgF : gF (T x) = c x • L (gF x) :=
      tendsto_nhds_unique hFT
        (((L.continuous.tendsto _).comp hF).const_smul (c x) |>.congr
          fun n => (hc.2 n).2.symm)
    rw [hgE, hgF, hscale _ _ _ hc.1, htransform]
  have hm : Measurable (fun x => N (gE x, gF x)) := hN.comp (hmE.prodMk hmF)
  have hmS : Measurable (fun x => S (N (gE x, gF x))) := hS.comp hm
  have heq : (fun om => N (AE om, AF om)) =ᵐ[P]
      (fun x => N (gE x, gF x)) ∘ field := by
    filter_upwards [heE, heF] with om hE hF
    simp only [Function.comp_apply, hE, hF]
  have heqS : (fun om => S (N (AE om, AF om))) =ᵐ[P]
      (fun x => S (N (gE x, gF x))) ∘ field := by
    filter_upwards [heq] with om h
    exact congrArg S h
  rw [Measure.map_congr heq, Measure.map_congr heqS,
    ← Measure.map_map hm hfield, ← Measure.map_map hmS hfield, hlaw]
  calc
    μ.map (fun x => N (gE x, gF x)) =
        μ.map ((fun x => N (gE x, gF x)) ∘ T) := by
      rw [← Measure.map_map hm hT.measurable, hT.map_eq]
    _ = μ.map (fun x => S (N (gE x, gF x))) := Measure.map_congr hequiv

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology BigOperators NNReal ENNReal

namespace SubdiffusiveProcess.Paper

/-- The polarization matrix of a scalar quadratic response. -/
def aux_thm_prop_polar_matrix {d : ℕ} (R : (Fin d → ℝ) → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  (R (Pi.single i 1 + Pi.single j 1) - R (Pi.single i 1) - R (Pi.single j 1)) / 2

theorem aux_thm_prop_polar_matrix_symmetric {d : ℕ} (R : (Fin d → ℝ) → ℝ) :
    (aux_thm_prop_polar_matrix R).transpose = aux_thm_prop_polar_matrix R := by
  ext i j
  change (R (Pi.single j 1 + Pi.single i 1) - R (Pi.single j 1) - R (Pi.single i 1)) / 2 = _
  rw [add_comm (Pi.single j (1 : ℝ) : Fin d → ℝ) (Pi.single i 1)]
  unfold aux_thm_prop_polar_matrix
  ring

theorem aux_thm_prop_polar_matrix_of_quadratic {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose = A) :
    aux_thm_prop_polar_matrix (fun p => p ⬝ᵥ A.mulVec p) = A := by
  ext i j
  unfold aux_thm_prop_polar_matrix
  simp only [aux_thm_prop_matrix_quadratic_eq]
  exact aux_thm_prop_matrix_polarization A
    (fun a b => (congrFun (congrFun hA a) b).symm) i j

theorem aux_thm_prop_symmetric_matrix_ext {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = A) (hB : B.transpose = B)
    (h : ∀ p : Fin d → ℝ, p ⬝ᵥ A.mulVec p = p ⬝ᵥ B.mulVec p) : A = B := by
  rw [← aux_thm_prop_polar_matrix_of_quadratic A hA,
    ← aux_thm_prop_polar_matrix_of_quadratic B hB]
  exact congrArg aux_thm_prop_polar_matrix (funext h)

theorem aux_thm_prop_polar_matrix_measurable {d : ℕ}
    {Ξ : Type*} [MeasurableSpace Ξ] (R : Ξ → (Fin d → ℝ) → ℝ)
    (hR : ∀ p, Measurable (fun x => R x p)) :
    Measurable (fun x => aux_thm_prop_polar_matrix (R x)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (((hR (Pi.single i 1 + Pi.single j 1)).sub (hR (Pi.single i 1))).sub
    (hR (Pi.single j 1))).div_const 2

theorem aux_thm_prop_polar_matrix_limit {d : ℕ}
    (R : ℕ → (Fin d → ℝ) → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A)
    (hR : ∀ p, Tendsto (fun n => R n p) atTop (𝓝 (p ⬝ᵥ A.mulVec p))) :
    Tendsto (fun n => aux_thm_prop_polar_matrix (R n)) atTop (𝓝 A) := by
  rw [← aux_thm_prop_polar_matrix_of_quadratic A hA]
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
    (((hR (Pi.single i 1 + Pi.single j 1)).sub (hR (Pi.single i 1))).sub
      (hR (Pi.single j 1))).div_const 2

/-- The literal volume-normalized finite-cutoff matrix at one physical cell. -/
def aux_thm_prop_cutoff_affine_matrix {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ) (om : BilateralField d) : Matrix (Fin d) (Fin d) ℝ :=
  aux_thm_prop_polar_matrix fun p =>
    affineDirichletResponse (centeredCube_isBounded z hr) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal

theorem aux_thm_prop_cutoff_affine_matrix_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ) :
    Measurable (aux_thm_prop_cutoff_affine_matrix model H z hr hP N) :=
  aux_thm_prop_polar_matrix_measurable _ fun p =>
    (aux_thm_prop_affine_response_measurable model H hH N z hr hP p).div_const _

theorem aux_thm_prop_cutoff_affine_matrix_quadratic {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ) (om : BilateralField d) (p : Fin d → ℝ) :
    p ⬝ᵥ (aux_thm_prop_cutoff_affine_matrix model H z hr hP N om).mulVec p =
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z hr) p /
          (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  obtain ⟨A, hsym, hquad⟩ := aux_lem_band_rcJ_bridge_B2_dirichlet_quadratic
    (centeredCube_isBounded z hr) hP (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z hr)
  let v : ℝ := (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  let B : Matrix (Fin d) (Fin d) ℝ := fun i j => A i j / v
  have hB : B.transpose = B := by
    ext i j
    exact congrArg (fun x => x / v) (hsym j i)
  have hR : ∀ q : Fin d → ℝ,
      affineDirichletResponse (centeredCube_isBounded z hr) hP
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z hr) q / v = q ⬝ᵥ B.mulVec q := by
    intro q
    rw [hquad, aux_thm_prop_matrix_quadratic_eq]
    simp only [Finset.sum_div, B, div_mul_eq_mul_div]
  have hmatrix : aux_thm_prop_cutoff_affine_matrix model H z hr hP N om = B := by
    change aux_thm_prop_polar_matrix
      (fun q => affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z hr) q / v) = B
    rw [funext hR, aux_thm_prop_polar_matrix_of_quadratic B hB]
  rw [hmatrix]
  exact (hR p).symm

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper

def aux_thm_prop_lc_rel {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (v : Fin d → ℝ) : ℝ :=
  (v ⬝ᵥ B.mulVec v - c * (v ⬝ᵥ A.mulVec v)) / Matrix.trace A

/-- The finite affine set of slopes `e_i`, `e_i + e_j` used for polarization. -/
def aux_thm_prop_lc_slope {d : ℕ} (v : Fin d → ℝ) : Prop :=
  (∃ i : Fin d, v = Pi.single i (1 : ℝ)) ∨
    (∃ i j : Fin d, v = Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))

/-- Sign of the reflection in coordinate `i`. -/
def aux_thm_prop_lc_sign {d : ℕ} (i j : Fin d) : ℝ := if j = i then -(1 : ℝ) else 1

/-- The trace-normalized pair `(A_E/tr A_E, A_F/tr A_E)`, as plain arrays. -/
def aux_thm_prop_lc_normpair {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
  (fun j l => A j l / Matrix.trace A, fun j l => B j l / Matrix.trace A)

/-- Conjugation of a pair of arrays by the reflection in coordinate `i`. -/
def aux_thm_prop_lc_reflpair {d : ℕ} (i : Fin d)
    (XY : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
  (fun j l => aux_thm_prop_lc_sign i j * aux_thm_prop_lc_sign i l * XY.1 j l,
    fun j l => aux_thm_prop_lc_sign i j * aux_thm_prop_lc_sign i l * XY.2 j l)

/-- Conjugation of a pair of arrays by a coordinate permutation. -/
def aux_thm_prop_lc_permpair {d : ℕ} (σ : Equiv.Perm (Fin d))
    (XY : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
  (fun j l => XY.1 (σ j) (σ l), fun j l => XY.2 (σ j) (σ l))

theorem aux_thm_prop_lc_single_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    Pi.single i (1 : ℝ) ⬝ᵥ A.mulVec (Pi.single j (1 : ℝ)) = A i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem aux_thm_prop_lc_symm_apply {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) (i j : Fin d) : A j i = A i j := by
  have h := congrFun (congrFun hA i) j
  simpa [Matrix.transpose_apply] using h

theorem aux_thm_prop_lc_pair_quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (i j : Fin d) :
    (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) ⬝ᵥ
        A.mulVec (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) =
      A i i + A j j + 2 * A i j := by
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    aux_thm_prop_lc_single_mulVec, aux_thm_prop_lc_single_mulVec,
    aux_thm_prop_lc_single_mulVec, aux_thm_prop_lc_single_mulVec,
    aux_thm_prop_lc_symm_apply hA i j]
  ring

theorem aux_thm_prop_lc_diff_quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (i j : Fin d) :
    (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) ⬝ᵥ
        A.mulVec (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) =
      A i i + A j j - 2 * A i j := by
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    aux_thm_prop_lc_single_mulVec, aux_thm_prop_lc_single_mulVec,
    aux_thm_prop_lc_single_mulVec, aux_thm_prop_lc_single_mulVec,
    aux_thm_prop_lc_symm_apply hA i j]
  ring

/-- Polarization: every entry of the centred matrix is a combination of three
relative scalar responses (paper label `mfd:thm-prop`, "after polarization over the finite
affine set"). -/
theorem aux_thm_prop_lc_entry_polar {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) (c : ℝ) (i j : Fin d) :
    ((Matrix.trace A)⁻¹ • (B - c • A)) i j =
      (aux_thm_prop_lc_rel A B c (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) -
        aux_thm_prop_lc_rel A B c (Pi.single i (1 : ℝ)) -
        aux_thm_prop_lc_rel A B c (Pi.single j (1 : ℝ))) / 2 := by
  simp only [aux_thm_prop_lc_rel, aux_thm_prop_lc_pair_quad A hA, aux_thm_prop_lc_pair_quad B hB,
    aux_thm_prop_lc_single_mulVec, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The trace is the sum of the diagonal quadratic values. -/
theorem aux_thm_prop_lc_trace_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace A = ∑ j : Fin d,
      Pi.single j (1 : ℝ) ⬝ᵥ A.mulVec (Pi.single j (1 : ℝ)) := by
  simp only [aux_thm_prop_lc_single_mulVec]
  rfl

/-- On a slope, the quadratic value of a positive semidefinite matrix is at most
four times its trace. -/
theorem aux_thm_prop_lc_quad_le_trace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ A.mulVec v)
    (v : Fin d → ℝ) (hv : aux_thm_prop_lc_slope v) :
    v ⬝ᵥ A.mulVec v ≤ 4 * Matrix.trace A := by
  have hdiag : ∀ j : Fin d, 0 ≤ A j j := by
    intro j
    have h := hpsd (Pi.single j (1 : ℝ))
    rwa [aux_thm_prop_lc_single_mulVec] at h
  have hle : ∀ j : Fin d, A j j ≤ Matrix.trace A := by
    intro j
    have h := Finset.single_le_sum (f := fun l : Fin d => A l l)
      (fun l _ => hdiag l) (Finset.mem_univ j)
    simpa [Matrix.trace, Matrix.diag] using h
  have htr : 0 ≤ Matrix.trace A := (hdiag ⟨0, by
    rcases hv with ⟨i, _⟩ | ⟨i, _, _⟩ <;> exact lt_of_le_of_lt (Nat.zero_le _) i.2⟩).trans
      (hle _)
  rcases hv with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · rw [aux_thm_prop_lc_single_mulVec]
    linarith [hle i]
  · rw [aux_thm_prop_lc_pair_quad A hA]
    have hd := hpsd (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))
    rw [aux_thm_prop_lc_diff_quad A hA] at hd
    linarith [hle i, hle j]

/-- The relative scalar is bounded by `4 M` on the slopes under the form order. -/
theorem aux_thm_prop_lc_rel_abs_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ A.mulVec v)
    (m M c : ℝ) (hm : 0 ≤ m) (hc0 : 0 ≤ c) (hcM : c ≤ M)
    (htr : 0 < Matrix.trace A)
    (hord : ∀ v : Fin d → ℝ, m * (v ⬝ᵥ A.mulVec v) ≤ v ⬝ᵥ B.mulVec v ∧
      v ⬝ᵥ B.mulVec v ≤ M * (v ⬝ᵥ A.mulVec v))
    (v : Fin d → ℝ) (hv : aux_thm_prop_lc_slope v) :
    |aux_thm_prop_lc_rel A B c v| ≤ 4 * M := by
  have hq := aux_thm_prop_lc_quad_le_trace A hA hpsd v hv
  have hq0 := hpsd v
  have hB0 : 0 ≤ v ⬝ᵥ B.mulVec v := le_trans (mul_nonneg hm hq0) (hord v).1
  have hBle : v ⬝ᵥ B.mulVec v ≤ M * (4 * Matrix.trace A) :=
    (hord v).2.trans (mul_le_mul_of_nonneg_left hq (hc0.trans hcM))
  have hcle : c * (v ⬝ᵥ A.mulVec v) ≤ M * (4 * Matrix.trace A) :=
    mul_le_mul hcM hq hq0 (hc0.trans hcM)
  have hc0' : 0 ≤ c * (v ⬝ᵥ A.mulVec v) := mul_nonneg hc0 hq0
  unfold aux_thm_prop_lc_rel
  rw [abs_div, abs_of_pos htr, div_le_iff₀ htr, abs_le]
  constructor <;> nlinarith

/-! ### Probability assembly -/

section aux_thm_prop_lc_prob

variable {Ω : Type} [MeasurableSpace Ω]

/-- A three-term combination is controlled by the sum of the three `L^q` norms. -/
theorem aux_thm_prop_lc_three_le (P : Measure Ω) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (f1 f2 f3 : Ω → ℝ) (h1 : AEStronglyMeasurable f1 P) (h2 : AEStronglyMeasurable f2 P)
    (h3 : AEStronglyMeasurable f3 P) :
    eLpNorm (fun omega => (f1 omega - f2 omega - f3 omega) / 2) q P ≤
      eLpNorm f1 q P + eLpNorm f2 q P + eLpNorm f3 q P := by
  have hmono : eLpNorm (fun omega => (f1 omega - f2 omega - f3 omega) / 2) q P ≤
      eLpNorm (f1 - f2 - f3) q P := by
    have hm : AEStronglyMeasurable (fun omega => (f1 omega - f2 omega - f3 omega) / 2) P := by
      simpa only [Pi.sub_apply, Function.comp_apply] using!
        (continuous_id.div_const (2 : ℝ)).comp_aestronglyMeasurable ((h1.sub h2).sub h3)
    apply eLpNorm_mono hm
    intro omega
    simp only [Real.norm_eq_abs, Pi.sub_apply, abs_div, abs_two]
    have := abs_nonneg (f1 omega - f2 omega - f3 omega)
    linarith
  refine hmono.trans ?_
  calc eLpNorm (f1 - f2 - f3) q P ≤ eLpNorm (f1 - f2) q P + eLpNorm f3 q P :=
        eLpNorm_sub_le hq
    _ ≤ eLpNorm f1 q P + eLpNorm f2 q P + eLpNorm f3 q P := by
        gcongr
        exact eLpNorm_sub_le hq

/-- The double entry sum of absolute values is controlled entrywise. -/
theorem aux_thm_prop_lc_double_sum_le {d : ℕ} (P : Measure Ω) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (F : Fin d → Fin d → Ω → ℝ) (hF : ∀ i j, AEStronglyMeasurable (F i j) P)
    (X : ℝ≥0∞) (hX : ∀ i j, eLpNorm (F i j) q P ≤ X) :
    eLpNorm (fun omega => ∑ i : Fin d, ∑ j : Fin d, |F i j omega|) q P ≤ (d : ℝ≥0∞) * (d * X) := by
  have hrow : ∀ i, AEStronglyMeasurable (fun omega => ∑ j : Fin d, |F i j omega|) P := by
    intro i
    have : (fun omega => ∑ j : Fin d, |F i j omega|) = ∑ j : Fin d, (fun omega => |F i j omega|) := by
      funext omega; simp
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => (hF i j).norm
  have hsum : (fun omega => ∑ i : Fin d, ∑ j : Fin d, |F i j omega|) =
      ∑ i : Fin d, (fun omega => ∑ j : Fin d, |F i j omega|) := by
    funext omega; simp
  rw [hsum]
  refine (eLpNorm_sum_le hq).trans ?_
  have hrowle : ∀ i, eLpNorm (fun omega => ∑ j : Fin d, |F i j omega|) q P ≤ d * X := by
    intro i
    have : (fun omega => ∑ j : Fin d, |F i j omega|) = ∑ j : Fin d, (fun omega => |F i j omega|) := by
      funext omega; simp
    rw [this]
    refine (eLpNorm_sum_le hq).trans ?_
    calc ∑ j : Fin d, eLpNorm (fun omega => |F i j omega|) q P
        ≤ ∑ _j : Fin d, X := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := eLpNorm_norm (p := q) (μ := P) (F i j) (hF i j)
          simp only [Real.norm_eq_abs] at h
          rw [h]
          exact hX i j
      _ = d * X := by simp
  calc ∑ i : Fin d, eLpNorm (fun omega => ∑ j : Fin d, |F i j omega|) q P
      ≤ ∑ _i : Fin d, (d : ℝ≥0∞) * X := Finset.sum_le_sum fun i _ => hrowle i
    _ = (d : ℝ≥0∞) * (d * X) := by simp

/-- Conditional expectation commutes with the three-term polarization combination. -/
theorem aux_thm_prop_lc_three_condExp (P : Measure Ω) (mB : MeasurableSpace Ω)
    (f1 f2 f3 : Ω → ℝ) (h1 : Integrable f1 P) (h2 : Integrable f2 P)
    (h3 : Integrable f3 P) :
    (fun omega => (f1 omega - f2 omega - f3 omega) / 2 -
        (P[fun omega' => (f1 omega' - f2 omega' - f3 omega') / 2 | mB]) omega) =ᵐ[P]
      fun omega => ((f1 omega - (P[f1 | mB]) omega) - (f2 omega - (P[f2 | mB]) omega) -
        (f3 omega - (P[f3 | mB]) omega)) / 2 := by
  have hfun : (fun omega' => (f1 omega' - f2 omega' - f3 omega') / 2) = (1 / 2 : ℝ) • (f1 - f2 - f3) := by
    funext omega; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hc : P[fun omega' => (f1 omega' - f2 omega' - f3 omega') / 2 | mB] =ᵐ[P]
      (1 / 2 : ℝ) • (P[f1 | mB] - P[f2 | mB] - P[f3 | mB]) := by
    rw [hfun]
    refine (condExp_smul (1 / 2 : ℝ) (f1 - f2 - f3) mB).trans ?_
    have hs1 := condExp_sub (h1.sub h2) h3 mB
    have hs2 := condExp_sub h1 h2 mB
    filter_upwards [hs1, hs2] with omega e1 e2
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2]
  filter_upwards [hc] with omega homega
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at homega
  rw [homega]
  ring

/-- Mean value of a random variable almost surely in `[m, M]`. -/
theorem aux_thm_prop_lc_integral_mem_Icc (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P) (m M : ℝ)
    (hfm : ∀ᵐ omega ∂P, m ≤ f omega ∧ f omega ≤ M) :
    Integrable f P ∧ (∫ omega, f omega ∂P) ∈ Icc m M := by
  have hint : Integrable f P := by
    refine Integrable.of_bound hf (max |m| |M|) ?_
    filter_upwards [hfm] with omega homega
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := neg_abs_le m; have := le_max_left |m| |M|; linarith [homega.1]
    · have := le_abs_self M; have := le_max_right |m| |M|; linarith [homega.2]
  refine ⟨hint, ?_, ?_⟩
  · have h := integral_mono_ae (integrable_const m) hint (hfm.mono fun omega homega => homega.1)
    simpa using h
  · have h := integral_mono_ae hint (integrable_const M) (hfm.mono fun omega homega => homega.2)
    simpa using h

/-- Hyperoctahedral invariance of the law of the normalized pair forces the mean of
the centred matrix to vanish (paper label `mfd:thm-prop`). -/
theorem aux_thm_prop_lc_mean_zero {d : ℕ} (hd : 0 < d) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ)
    (hmeasE : ∀ j l, AEStronglyMeasurable (fun omega => AE omega j l) P)
    (hmeasF : ∀ j l, AEStronglyMeasurable (fun omega => AF omega j l) P)
    (hint : ∀ j l, Integrable (fun omega => ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) j l) P)
    (htrace : ∫ omega, Matrix.trace ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) ∂P = 0)
    (hrefl : ∀ i : Fin d,
      Measure.map (fun omega => aux_thm_prop_lc_normpair (AE omega) (AF omega)) P =
        Measure.map (fun omega => aux_thm_prop_lc_reflpair i
          (aux_thm_prop_lc_normpair (AE omega) (AF omega))) P)
    (hperm : ∀ σ : Equiv.Perm (Fin d),
      Measure.map (fun omega => aux_thm_prop_lc_normpair (AE omega) (AF omega)) P =
        Measure.map (fun omega => aux_thm_prop_lc_permpair σ
          (aux_thm_prop_lc_normpair (AE omega) (AF omega))) P) :
    ∀ j l, ∫ omega, ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) j l ∂P = 0 := by
  set NP : Ω → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
    fun omega => aux_thm_prop_lc_normpair (AE omega) (AF omega) with hNP
  have htrm : AEStronglyMeasurable (fun omega => Matrix.trace (AE omega)) P := by
    have : (fun omega => Matrix.trace (AE omega)) = ∑ j : Fin d, (fun omega => AE omega j j) := by
      funext omega; simp [Matrix.trace, Matrix.diag]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => hmeasE j j
  have hNPm : AEMeasurable NP P := by
    refine AEMeasurable.prodMk ?_ ?_
    · refine AEMeasurable.of_eval fun j => AEMeasurable.of_eval fun l => ?_
      exact (hmeasE j l).aemeasurable.div htrm.aemeasurable
    · refine AEMeasurable.of_eval fun j => AEMeasurable.of_eval fun l => ?_
      exact (hmeasF j l).aemeasurable.div htrm.aemeasurable
  let g : Fin d → Fin d → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) → ℝ :=
    fun j l XY => XY.2 j l - ck * XY.1 j l
  have hgc : ∀ j l, Continuous (g j l) := by
    intro j l
    have h1 : Continuous fun XY : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) => XY.1 j l :=
      (continuous_apply l).comp ((continuous_apply j).comp continuous_fst)
    have h2 : Continuous fun XY : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) => XY.2 j l :=
      (continuous_apply l).comp ((continuous_apply j).comp continuous_snd)
    exact h2.sub (continuous_const.mul h1)
  have hB : ∀ j l omega, ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) j l = g j l (NP omega) := by
    intro j l omega
    simp only [g, hNP, aux_thm_prop_lc_normpair, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul]
    ring
  -- transport of integrals along equal laws
  have htrans : ∀ (Φ : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) →
      (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)), Continuous Φ →
      Measure.map NP P = Measure.map (fun omega => Φ (NP omega)) P →
      ∀ j l, ∫ omega, g j l (NP omega) ∂P = ∫ omega, g j l (Φ (NP omega)) ∂P := by
    intro Φ hΦ hlaw j l
    have hΦm : AEMeasurable (fun omega => Φ (NP omega)) P := hΦ.measurable.comp_aemeasurable hNPm
    rw [← integral_map hNPm (hgc j l).aestronglyMeasurable, hlaw,
      integral_map hΦm (hgc j l).aestronglyMeasurable]
  let EB : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun j l => ∫ omega, g j l (NP omega) ∂P
  have hrefl' : ∀ (i j k : Fin d),
      EB j k = (if j = i then -(1 : ℝ) else 1) * (if k = i then -(1 : ℝ) else 1) * EB j k := by
    intro i j k
    have hc : Continuous (aux_thm_prop_lc_reflpair (d := d) i) := by
      refine Continuous.prodMk ?_ ?_
      · refine continuous_pi fun a => continuous_pi fun b => ?_
        exact continuous_const.mul
          ((continuous_apply b).comp ((continuous_apply a).comp continuous_fst))
      · refine continuous_pi fun a => continuous_pi fun b => ?_
        exact continuous_const.mul
          ((continuous_apply b).comp ((continuous_apply a).comp continuous_snd))
    have h := htrans _ hc (hrefl i) j k
    have hpt : ∀ omega, g j k (aux_thm_prop_lc_reflpair i (NP omega)) =
        (if j = i then -(1 : ℝ) else 1) * (if k = i then -(1 : ℝ) else 1) * g j k (NP omega) := by
      intro omega
      simp only [g, aux_thm_prop_lc_reflpair, aux_thm_prop_lc_sign]
      ring
    show ∫ omega, g j k (NP omega) ∂P = _ * _ * ∫ omega, g j k (NP omega) ∂P
    conv_lhs => rw [h]
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  have hperm' : ∀ (σ : Equiv.Perm (Fin d)) (j k : Fin d), EB (σ j) (σ k) = EB j k := by
    intro σ j k
    have hc : Continuous (aux_thm_prop_lc_permpair (d := d) σ) := by
      refine Continuous.prodMk ?_ ?_
      · exact continuous_pi fun a => continuous_pi fun b =>
          (continuous_apply (σ b)).comp ((continuous_apply (σ a)).comp continuous_fst)
      · exact continuous_pi fun a => continuous_pi fun b =>
          (continuous_apply (σ b)).comp ((continuous_apply (σ a)).comp continuous_snd)
    have h := htrans _ hc (hperm σ) j k
    simp only [EB, Matrix.of_apply]
    rw [h]
    rfl
  have htr0 : Matrix.trace EB = 0 := by
    have hsum : Matrix.trace EB = ∑ j : Fin d, ∫ omega, g j j (NP omega) ∂P := by
      simp only [Matrix.trace, Matrix.diag, EB, Matrix.of_apply]
    have hint' : ∀ j, Integrable (fun omega => g j j (NP omega)) P := fun j =>
      (hint j j).congr (Eventually.of_forall fun omega => hB j j omega)
    have hswap := integral_finsetSum (μ := P) Finset.univ (fun j _ => hint' j)
    rw [hsum, ← hswap, ← htrace]
    refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
    show ∑ j ∈ Finset.univ, g j j (NP omega) =
      ∑ j, Matrix.diag ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) j
    exact Finset.sum_congr rfl fun j _ => (hB j j omega).symm
  have hzero := _root_.SubdiffusiveProcess.ResponseMoments.relative_concentration_mean_matrix_eq_zero
    d hd EB hrefl' hperm' htr0
  intro j l
  have h := congrFun (congrFun hzero j) l
  simp only [EB, Matrix.of_apply, Matrix.zero_apply] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
  simp only
  rw [hB]

end aux_thm_prop_lc_prob

/-- `c_k` of paper label `mfd:thm-prop`. -/
def aux_thm_prop_lc_ck {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (k : ℕ) : ℝ :=
  ∫ omega, Matrix.trace (AF k omega) / Matrix.trace (AE k omega) ∂P

/-- `B_k` of paper label `mfd:thm-prop`. -/
def aux_thm_prop_lc_Bk {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (omega : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.trace (AE k omega))⁻¹ • (AF k omega - aux_thm_prop_lc_ck P AE AF k • AE k omega)

theorem aux_thm_prop_lc_ennreal (d : ℕ) (X : ℝ) :
    (d : ℝ≥0∞) * ((d : ℝ≥0∞) * (ENNReal.ofReal X + ENNReal.ofReal X + ENNReal.ofReal X)) =
      ENNReal.ofReal (3 * ((d : ℝ) * (d : ℝ)) * X) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  ring

section aux_thm_prop_lc_generic

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Entry, trace and relative-scalar measurability from the quadratic values. -/
theorem aux_thm_prop_lc_gen_meas (P : Measure Ω)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymAE : ∀ k omega, (AE k omega).transpose = AE k omega)
    (hsymAF : ∀ k omega, (AF k omega).transpose = AF k omega)
    (hmE : ∀ (k : ℕ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => v ⬝ᵥ (AE k omega).mulVec v) P)
    (hmF : ∀ (k : ℕ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => v ⬝ᵥ (AF k omega).mulVec v) P) :
    (∀ (k : ℕ) (i j : Fin d), AEStronglyMeasurable (fun omega => AE k omega i j) P) ∧
    (∀ (k : ℕ) (i j : Fin d), AEStronglyMeasurable (fun omega => AF k omega i j) P) ∧
    (∀ k : ℕ, AEStronglyMeasurable (fun omega => Matrix.trace (AE k omega)) P) ∧
    (∀ k : ℕ, AEStronglyMeasurable (fun omega => Matrix.trace (AF k omega) / Matrix.trace (AE k omega)) P) ∧
    (∀ (k : ℕ) (c : ℝ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => aux_thm_prop_lc_rel (AE k omega) (AF k omega) c v) P) := by
  have hent : ∀ (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ),
      (∀ k omega, (A k omega).transpose = A k omega) →
      (∀ (k : ℕ) (v : Fin d → ℝ),
        AEStronglyMeasurable (fun omega => v ⬝ᵥ (A k omega).mulVec v) P) →
      ∀ (k : ℕ) (i j : Fin d), AEStronglyMeasurable (fun omega => A k omega i j) P := by
    intro A hA hm k i j
    have h : AEStronglyMeasurable (fun omega =>
        ((Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) ⬝ᵥ
            (A k omega).mulVec (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) -
          Pi.single i (1 : ℝ) ⬝ᵥ (A k omega).mulVec (Pi.single i (1 : ℝ)) -
          Pi.single j (1 : ℝ) ⬝ᵥ (A k omega).mulVec (Pi.single j (1 : ℝ))) * (1 / 2)) P :=
      (((hm k _).sub (hm k _)).sub (hm k _)).mul_const _
    refine h.congr (Eventually.of_forall fun omega => ?_)
    simp only [aux_thm_prop_lc_pair_quad _ (hA k omega), aux_thm_prop_lc_single_mulVec]
    ring
  have hE := hent AE hsymAE hmE
  have hF := hent AF hsymAF hmF
  have htr : ∀ (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ),
      (∀ (k : ℕ) (i j : Fin d), AEStronglyMeasurable (fun omega => A k omega i j) P) →
      ∀ k : ℕ, AEStronglyMeasurable (fun omega => Matrix.trace (A k omega)) P := by
    intro A hA k
    have : (fun omega => Matrix.trace (A k omega)) = ∑ j : Fin d, (fun omega => A k omega j j) := by
      funext omega; simp [Matrix.trace, Matrix.diag]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => hA k j j
  have htrE := htr AE hE
  have htrF := htr AF hF
  refine ⟨hE, hF, htrE, fun k => ?_, fun k c v => ?_⟩
  · exact ((htrF k).aemeasurable.div (htrE k).aemeasurable).aestronglyMeasurable
  · exact (((hmF k v).aemeasurable.sub ((hmE k v).aemeasurable.const_mul c)).div
      (htrE k).aemeasurable).aestronglyMeasurable

/-- Per-entry moment bound from the per-slope centred bounds and the mean-zero clause. -/
theorem aux_thm_prop_lc_entry_moment (P : Measure Ω)
    (A B : Ω → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ omega, (A omega).transpose = A omega)
    (hB : ∀ omega, (B omega).transpose = B omega) (c : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q) (X0 : ℝ)
    (i j : Fin d)
    (hint : ∀ v : Fin d → ℝ, aux_thm_prop_lc_slope v →
      Integrable (fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c v) P)
    (hmean : ∫ omega, ((Matrix.trace (A omega))⁻¹ • (B omega - c • A omega)) i j ∂P = 0)
    (hbd : ∀ v : Fin d → ℝ, aux_thm_prop_lc_slope v →
      eLpNorm (fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c v -
          ∫ omega', aux_thm_prop_lc_rel (A omega') (B omega') c v ∂P) q P ≤ ENNReal.ofReal X0) :
    eLpNorm (fun omega => ((Matrix.trace (A omega))⁻¹ • (B omega - c • A omega)) i j) q P ≤
      ENNReal.ofReal X0 + ENNReal.ofReal X0 + ENNReal.ofReal X0 := by
  have s1 : aux_thm_prop_lc_slope (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) :=
    Or.inr ⟨i, j, rfl⟩
  have s2 : aux_thm_prop_lc_slope (Pi.single i (1 : ℝ)) := Or.inl ⟨i, rfl⟩
  have s3 : aux_thm_prop_lc_slope (Pi.single j (1 : ℝ)) := Or.inl ⟨j, rfl⟩
  set f1 := fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
    with hf1
  set f2 := fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c (Pi.single i (1 : ℝ)) with hf2
  set f3 := fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c (Pi.single j (1 : ℝ)) with hf3
  have hpol : ∀ omega, ((Matrix.trace (A omega))⁻¹ • (B omega - c • A omega)) i j =
      (f1 omega - f2 omega - f3 omega) / 2 := fun omega => aux_thm_prop_lc_entry_polar (A omega) (B omega) (hA omega) (hB omega) c i j
  have hI1 := hint _ s1
  have hI2 := hint _ s2
  have hI3 := hint _ s3
  have hmean' : (∫ omega, f1 omega ∂P) - (∫ omega, f2 omega ∂P) - (∫ omega, f3 omega ∂P) = 0 := by
    have h12 : Integrable (fun omega => f1 omega - f2 omega) P := hI1.sub hI2
    have h := hmean
    rw [integral_congr_ae (Eventually.of_forall hpol), integral_div,
      integral_sub h12 hI3, integral_sub hI1 hI2] at h
    linarith
  have hfun : (fun omega => ((Matrix.trace (A omega))⁻¹ • (B omega - c • A omega)) i j) =
      fun omega => ((f1 omega - ∫ omega', f1 omega' ∂P) - (f2 omega - ∫ omega', f2 omega' ∂P) -
        (f3 omega - ∫ omega', f3 omega' ∂P)) / 2 := by
    funext omega
    rw [hpol omega]
    linarith
  rw [hfun]
  refine (aux_thm_prop_lc_three_le P q hq _ _ _
    (hI1.aestronglyMeasurable.sub aestronglyMeasurable_const)
    (hI2.aestronglyMeasurable.sub aestronglyMeasurable_const)
    (hI3.aestronglyMeasurable.sub aestronglyMeasurable_const)).trans ?_
  gcongr
  · exact hbd _ s1
  · exact hbd _ s2
  · exact hbd _ s3

/-- Per-entry band bound from the per-slope band bounds. -/
theorem aux_thm_prop_lc_entry_band (P : Measure Ω)
    (A B : Ω → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ omega, (A omega).transpose = A omega)
    (hB : ∀ omega, (B omega).transpose = B omega) (c : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q) (Y : ℝ)
    (mBs : ℕ → MeasurableSpace Ω) (n : ℕ) (i j : Fin d)
    (hint : ∀ v : Fin d → ℝ, aux_thm_prop_lc_slope v →
      Integrable (fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c v) P)
    (hbd : ∀ v : Fin d → ℝ, aux_thm_prop_lc_slope v →
      eLpNorm (fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c v -
          (P[fun omega' => aux_thm_prop_lc_rel (A omega') (B omega') c v | mBs n]) omega) q P ≤
        ENNReal.ofReal Y) :
    eLpNorm (fun omega => ((Matrix.trace (A omega))⁻¹ • (B omega - c • A omega)) i j -
        (P[fun omega' => ((Matrix.trace (A omega'))⁻¹ • (B omega' - c • A omega')) i j | mBs n]) omega) q P ≤
      ENNReal.ofReal Y + ENNReal.ofReal Y + ENNReal.ofReal Y := by
  have s1 : aux_thm_prop_lc_slope (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) :=
    Or.inr ⟨i, j, rfl⟩
  have s2 : aux_thm_prop_lc_slope (Pi.single i (1 : ℝ)) := Or.inl ⟨i, rfl⟩
  have s3 : aux_thm_prop_lc_slope (Pi.single j (1 : ℝ)) := Or.inl ⟨j, rfl⟩
  set f1 := fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
    with hf1
  set f2 := fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c (Pi.single i (1 : ℝ)) with hf2
  set f3 := fun omega => aux_thm_prop_lc_rel (A omega) (B omega) c (Pi.single j (1 : ℝ)) with hf3
  have hpol : ∀ omega, ((Matrix.trace (A omega))⁻¹ • (B omega - c • A omega)) i j =
      (f1 omega - f2 omega - f3 omega) / 2 := fun omega =>
    aux_thm_prop_lc_entry_polar (A omega) (B omega) (hA omega) (hB omega) c i j
  have hI1 := hint _ s1
  have hI2 := hint _ s2
  have hI3 := hint _ s3
  simp only [hpol]
  rw [eLpNorm_congr_ae (aux_thm_prop_lc_three_condExp P (mBs n) f1 f2 f3 hI1 hI2 hI3)]
  refine (aux_thm_prop_lc_three_le P q hq _ _ _
    (hI1.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable)
    (hI2.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable)
    (hI3.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable)).trans ?_
  gcongr
  · exact hbd _ s1
  · exact hbd _ s2
  · exact hbd _ s3

theorem aux_thm_prop_lc_double_sum_aesm (P : Measure Ω)
    (F : Fin d → Fin d → Ω → ℝ) (hF : ∀ i j, AEStronglyMeasurable (F i j) P) :
    AEStronglyMeasurable (fun omega => ∑ i : Fin d, ∑ j : Fin d, |F i j omega|) P := by
  have hsum : (fun omega => ∑ i : Fin d, ∑ j : Fin d, |F i j omega|) =
      ∑ i : Fin d, ∑ j : Fin d, (fun omega => |F i j omega|) := by
    funext omega; simp
  rw [hsum]
  exact Finset.aestronglyMeasurable_sum _ fun i _ =>
    Finset.aestronglyMeasurable_sum _ fun j _ => (hF i j).norm

/-- The four conclusions of `prop_conc` from the affine order, the law symmetry and
the per-slope concentration bounds. -/
theorem aux_thm_prop_lc_assemble_generic (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymAE : ∀ k omega, (AE k omega).transpose = AE k omega)
    (hsymAF : ∀ k omega, (AF k omega).transpose = AF k omega)
    (hmE : ∀ (k : ℕ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => v ⬝ᵥ (AE k omega).mulVec v) P)
    (hmF : ∀ (k : ℕ) (v : Fin d → ℝ),
      AEStronglyMeasurable (fun omega => v ⬝ᵥ (AF k omega).mulVec v) P)
    (hpsd : ∀ᵐ omega ∂P, ∀ (k : ℕ) (v : Fin d → ℝ), 0 ≤ v ⬝ᵥ (AE k omega).mulVec v)
    (m M : ℝ) (hm : 0 ≤ m) (_hmM : m ≤ M)
    (hord : ∀ᵐ omega ∂P, ∀ k : ℕ, 0 < Matrix.trace (AE k omega) ∧
      ∀ v : Fin d → ℝ, m * (v ⬝ᵥ (AE k omega).mulVec v) ≤ v ⬝ᵥ (AF k omega).mulVec v ∧
        v ⬝ᵥ (AF k omega).mulVec v ≤ M * (v ⬝ᵥ (AE k omega).mulVec v))
    (hsym : ∀ k : ℕ,
      (∀ i : Fin d, Measure.map (fun omega => aux_thm_prop_lc_normpair (AE k omega) (AF k omega)) P =
        Measure.map (fun omega => aux_thm_prop_lc_reflpair i
          (aux_thm_prop_lc_normpair (AE k omega) (AF k omega))) P) ∧
      (∀ σ : Equiv.Perm (Fin d),
        Measure.map (fun omega => aux_thm_prop_lc_normpair (AE k omega) (AF k omega)) P =
          Measure.map (fun omega => aux_thm_prop_lc_permpair σ
            (aux_thm_prop_lc_normpair (AE k omega) (AF k omega))) P))
    (mB : ℕ → ℕ → MeasurableSpace Ω) (q0 q : ℝ≥0∞) (hq0 : q0 ≤ q) (hq : 1 ≤ q)
    (X0 : ℝ) (X : ℕ → ℝ)
    (hconc : ∀ c ∈ Icc m M, ∀ (k : ℕ) (v : Fin d → ℝ), aux_thm_prop_lc_slope v →
      eLpNorm (fun omega => aux_thm_prop_lc_rel (AE k omega) (AF k omega) c v -
          ∫ omega', aux_thm_prop_lc_rel (AE k omega') (AF k omega') c v ∂P) q P ≤ ENNReal.ofReal X0 ∧
      ∀ Hb : ℕ,
        eLpNorm (fun omega => aux_thm_prop_lc_rel (AE k omega) (AF k omega) c v -
            (P[fun omega' => aux_thm_prop_lc_rel (AE k omega') (AF k omega') c v | mB k Hb]) omega) q P ≤
          ENNReal.ofReal (X Hb)) :
    (∀ k : ℕ, aux_thm_prop_lc_ck P AE AF k ∈ Icc m M) ∧
    (∀ (k : ℕ) (i j : Fin d), ∫ omega, aux_thm_prop_lc_Bk P AE AF k omega i j ∂P = 0) ∧
    (∀ k : ℕ, eLpNorm (fun omega => ∑ i : Fin d, ∑ j : Fin d,
        |aux_thm_prop_lc_Bk P AE AF k omega i j|) q0 P ≤
        ENNReal.ofReal (3 * ((d : ℝ) * (d : ℝ)) * X0)) ∧
    (∀ k Hb : ℕ, eLpNorm (fun omega => ∑ i : Fin d, ∑ j : Fin d,
        |aux_thm_prop_lc_Bk P AE AF k omega i j -
          (P[fun omega => aux_thm_prop_lc_Bk P AE AF k omega i j | mB k Hb]) omega|) q0 P ≤
        ENNReal.ofReal (3 * ((d : ℝ) * (d : ℝ)) * X Hb)) := by
  obtain ⟨hEntE, hEntF, htrE, hratm, hrelm⟩ :=
    aux_thm_prop_lc_gen_meas P AE AF hsymAE hsymAF hmE hmF
  -- integrability of the relative scalars on the slopes
  have hrelInt : ∀ c, 0 ≤ c → c ≤ M → ∀ (k : ℕ) (v : Fin d → ℝ), aux_thm_prop_lc_slope v →
      Integrable (fun omega => aux_thm_prop_lc_rel (AE k omega) (AF k omega) c v) P := by
    intro c hc0 hcM k v hv
    refine Integrable.of_bound (hrelm k c v) (4 * M) ?_
    filter_upwards [hpsd, hord] with omega hp ho
    rw [Real.norm_eq_abs]
    exact aux_thm_prop_lc_rel_abs_le _ _ (hsymAE k omega) (hp k) m M c hm hc0 hcM (ho k).1 (ho k).2 v hv
  -- the trace ratio and `c_k`
  have hck : ∀ k : ℕ, Integrable (fun omega => Matrix.trace (AF k omega) / Matrix.trace (AE k omega)) P ∧
      aux_thm_prop_lc_ck P AE AF k ∈ Icc m M := by
    intro k
    refine aux_thm_prop_lc_integral_mem_Icc P _ (hratm k) m M ?_
    filter_upwards [hord] with omega ho
    exact _root_.SubdiffusiveProcess.ResponseMoments.trace_ratio_mem_Icc_of_form_order (AE k omega) (AF k omega) m M
      (ho k).1 (ho k).2
  have hc0 : ∀ k : ℕ, 0 ≤ aux_thm_prop_lc_ck P AE AF k := fun k => hm.trans (hck k).2.1
  have hcM : ∀ k : ℕ, aux_thm_prop_lc_ck P AE AF k ≤ M := fun k => (hck k).2.2
  -- integrability of the entries of `B_k`
  have hBint : ∀ (k : ℕ) (i j : Fin d),
      Integrable (fun omega => aux_thm_prop_lc_Bk P AE AF k omega i j) P := by
    intro k i j
    have h := (((hrelInt _ (hc0 k) (hcM k) k _ (Or.inr ⟨i, j, rfl⟩)).sub
      (hrelInt _ (hc0 k) (hcM k) k _ (Or.inl ⟨i, rfl⟩))).sub
      (hrelInt _ (hc0 k) (hcM k) k _ (Or.inl ⟨j, rfl⟩))).div_const 2
    refine h.congr (Eventually.of_forall fun omega => ?_)
    simp only [Pi.sub_apply]
    exact (aux_thm_prop_lc_entry_polar (AE k omega) (AF k omega) (hsymAE k omega) (hsymAF k omega) _ i j).symm
  -- mean zero
  have hmean : ∀ (k : ℕ) (i j : Fin d), ∫ omega, aux_thm_prop_lc_Bk P AE AF k omega i j ∂P = 0 := by
    intro k
    have htrace : ∫ omega, Matrix.trace ((Matrix.trace (AE k omega))⁻¹ •
        (AF k omega - aux_thm_prop_lc_ck P AE AF k • AE k omega)) ∂P = 0 := by
      have hae : (fun omega => Matrix.trace ((Matrix.trace (AE k omega))⁻¹ •
          (AF k omega - aux_thm_prop_lc_ck P AE AF k • AE k omega))) =ᵐ[P]
          fun omega => Matrix.trace (AF k omega) / Matrix.trace (AE k omega) -
            aux_thm_prop_lc_ck P AE AF k := by
        filter_upwards [hord] with omega ho
        have hne := (ho k).1.ne'
        rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
        field_simp
      rw [integral_congr_ae hae, integral_sub (hck k).1 (integrable_const _)]
      simp [aux_thm_prop_lc_ck]
    exact aux_thm_prop_lc_mean_zero hd P (AE k) (AF k) (aux_thm_prop_lc_ck P AE AF k)
      (hEntE k) (hEntF k) (hBint k) htrace (hsym k).1 (hsym k).2
  refine ⟨fun k => (hck k).2, hmean, fun k => ?_, fun k Hb => ?_⟩
  · -- moment bound
    have hentry : ∀ i j : Fin d, eLpNorm (fun omega => aux_thm_prop_lc_Bk P AE AF k omega i j) q P ≤
        ENNReal.ofReal X0 + ENNReal.ofReal X0 + ENNReal.ofReal X0 := by
      intro i j
      exact aux_thm_prop_lc_entry_moment P (AE k) (AF k) (hsymAE k) (hsymAF k) _ q hq X0 i j
        (fun v hv => hrelInt _ (hc0 k) (hcM k) k v hv) (hmean k i j)
        (fun v hv => (hconc _ (hck k).2 k v hv).1)
    have hF : ∀ i j : Fin d,
        AEStronglyMeasurable (fun omega => aux_thm_prop_lc_Bk P AE AF k omega i j) P :=
      fun i j => (hBint k i j).aestronglyMeasurable
    refine (eLpNorm_le_eLpNorm_of_exponent_le hq0).trans ?_
    refine (aux_thm_prop_lc_double_sum_le P q hq _ hF _ hentry).trans ?_
    rw [aux_thm_prop_lc_ennreal]
  · -- band bound
    have hentry : ∀ i j : Fin d, eLpNorm (fun omega => aux_thm_prop_lc_Bk P AE AF k omega i j -
          (P[fun omega => aux_thm_prop_lc_Bk P AE AF k omega i j | mB k Hb]) omega) q P ≤
        ENNReal.ofReal (X Hb) + ENNReal.ofReal (X Hb) + ENNReal.ofReal (X Hb) := by
      intro i j
      exact aux_thm_prop_lc_entry_band P (AE k) (AF k) (hsymAE k) (hsymAF k) _ q hq (X Hb)
        (mB k) Hb i j (fun v hv => hrelInt _ (hc0 k) (hcM k) k v hv)
        (fun v hv => (hconc _ (hck k).2 k v hv).2 Hb)
    have hF : ∀ i j : Fin d, AEStronglyMeasurable (fun omega => aux_thm_prop_lc_Bk P AE AF k omega i j -
          (P[fun omega => aux_thm_prop_lc_Bk P AE AF k omega i j | mB k Hb]) omega) P :=
      fun i j => (hBint k i j).aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable
    refine (eLpNorm_le_eLpNorm_of_exponent_le hq0).trans ?_
    refine (aux_thm_prop_lc_double_sum_le P q hq _ hF _ hentry).trans ?_
    rw [aux_thm_prop_lc_ennreal]

end aux_thm_prop_lc_generic

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper

section PCSwapScope
open scoped ContDiff Distributions


variable {d : ℕ}

/-- Transpose the coordinates `a, b` about the point `z`. -/
def aux_thm_prop_lc_swap (z : SpatialCoordinates d) (a b : Fin d) (x : SpatialCoordinates d) :
    SpatialCoordinates d :=
  fun i => z i + (x (Equiv.swap a b i) - z (Equiv.swap a b i))

theorem aux_thm_prop_lc_swap_involutive (z : SpatialCoordinates d) (a b : Fin d) :
    Function.Involutive (aux_thm_prop_lc_swap z a b) := by
  intro x
  funext i
  simp only [aux_thm_prop_lc_swap, Equiv.swap_apply_self]
  ring

theorem aux_thm_prop_lc_swap_continuous (z : SpatialCoordinates d) (a b : Fin d) :
    Continuous (aux_thm_prop_lc_swap z a b) :=
  continuous_pi fun _i => continuous_const.add ((continuous_apply _).sub continuous_const)

theorem aux_thm_prop_lc_swap_dist_le (z : SpatialCoordinates d) (a b : Fin d)
    (x y : SpatialCoordinates d) :
    dist (aux_thm_prop_lc_swap z a b x) (aux_thm_prop_lc_swap z a b y) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  have h : dist (aux_thm_prop_lc_swap z a b x i) (aux_thm_prop_lc_swap z a b y i) =
      dist (x (Equiv.swap a b i)) (y (Equiv.swap a b i)) := by
    simp only [aux_thm_prop_lc_swap, Real.dist_eq]
    congr 1
    ring
  rw [h]
  exact dist_le_pi_dist x y _

theorem aux_thm_prop_lc_swap_dist (z : SpatialCoordinates d) (a b : Fin d)
    (x y : SpatialCoordinates d) :
    dist (aux_thm_prop_lc_swap z a b x) (aux_thm_prop_lc_swap z a b y) = dist x y := by
  refine le_antisymm (aux_thm_prop_lc_swap_dist_le z a b x y) ?_
  have h := aux_thm_prop_lc_swap_dist_le z a b (aux_thm_prop_lc_swap z a b x)
    (aux_thm_prop_lc_swap z a b y)
  rwa [aux_thm_prop_lc_swap_involutive z a b x, aux_thm_prop_lc_swap_involutive z a b y] at h

/-- The swap as a homeomorphism of the spatial carrier. -/
def aux_thm_prop_lc_swapHomeo (z : SpatialCoordinates d) (a b : Fin d) :
    SpatialCoordinates d ≃ₜ SpatialCoordinates d where
  toFun := aux_thm_prop_lc_swap z a b
  invFun := aux_thm_prop_lc_swap z a b
  left_inv := aux_thm_prop_lc_swap_involutive z a b
  right_inv := aux_thm_prop_lc_swap_involutive z a b
  continuous_toFun := aux_thm_prop_lc_swap_continuous z a b
  continuous_invFun := aux_thm_prop_lc_swap_continuous z a b

theorem aux_thm_prop_lc_swap_self (z : SpatialCoordinates d) (a b : Fin d) :
    aux_thm_prop_lc_swap z a b z = z := by
  funext i
  simp [aux_thm_prop_lc_swap]

/-- The swap about the centre maps the centred cube onto itself. -/
theorem aux_thm_prop_lc_swap_preimage_cube (z : SpatialCoordinates d) (a b : Fin d)
    {r : ℝ} (hr : 0 < r) :
    aux_thm_prop_lc_swap z a b ⁻¹' (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  change dist (aux_thm_prop_lc_swap z a b x) z < r / 2 ↔ dist x z < r / 2
  have h := aux_thm_prop_lc_swap_dist z a b x z
  rw [aux_thm_prop_lc_swap_self] at h
  rw [h]

theorem aux_thm_prop_lc_swap_measurePreserving (z : SpatialCoordinates d) (a b : Fin d) :
    MeasurePreserving (aux_thm_prop_lc_swap z a b) volume volume := by
  have h1 : MeasurePreserving (fun x : SpatialCoordinates d => x - z) volume volume :=
    measurePreserving_sub_right volume z
  have h2 : MeasurePreserving
      (MeasurableEquiv.arrowCongr' (Equiv.swap a b) (MeasurableEquiv.refl ℝ) :
        SpatialCoordinates d → SpatialCoordinates d) volume volume :=
    volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)
  have h3 : MeasurePreserving (fun x : SpatialCoordinates d => x + z) volume volume :=
    measurePreserving_add_right volume z
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext x
  funext i
  simp only [Function.comp_apply, MeasurableEquiv.arrowCongr', Equiv.arrowCongr',
    Equiv.arrowCongr, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.refl,
    Equiv.symm_swap, Pi.add_apply, Pi.sub_apply, aux_thm_prop_lc_swap]
  rw [add_comm]
  rfl

theorem aux_thm_prop_lc_swap_preimage_reverse (z : SpatialCoordinates d) (a b : Fin d)
    {U Ω : Opens (SpatialCoordinates d)}
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    aux_thm_prop_lc_swap z a b ⁻¹' (U : Set (SpatialCoordinates d)) = Ω := by
  ext x
  have h := Set.ext_iff.mp hU (aux_thm_prop_lc_swap z a b x)
  simpa only [mem_preimage, aux_thm_prop_lc_swap_involutive z a b x] using h.symm

theorem aux_thm_prop_lc_swap_domain_measurePreserving (z : SpatialCoordinates d) (a b : Fin d)
    {U Ω : Opens (SpatialCoordinates d)}
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    MeasurePreserving (aux_thm_prop_lc_swap z a b)
      (volume.restrict (U : Set (SpatialCoordinates d)))
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have h := (aux_thm_prop_lc_swap_measurePreserving z a b).restrict_preimage
    Ω.isOpen.measurableSet
  rwa [hU] at h

/-! ### Smooth calculus of the swap -/

/-- The derivative of the swap: permute the coordinates of the increment. -/
def aux_thm_prop_lc_swapDeriv (a b : Fin d) : SpatialCoordinates d →L[ℝ] SpatialCoordinates d :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Equiv.swap a b i)

theorem aux_thm_prop_lc_swapDeriv_single (a b : Fin d) (i : Fin d) :
    aux_thm_prop_lc_swapDeriv a b (Pi.single i 1) =
      (Pi.single (Equiv.swap a b i) 1 : SpatialCoordinates d) := by
  funext j
  simp only [aux_thm_prop_lc_swapDeriv, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply]
  by_cases h : j = Equiv.swap a b i
  · subst h
    rw [Equiv.swap_apply_self, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    apply h
    rw [← h', Equiv.swap_apply_self]

theorem aux_thm_prop_lc_swap_hasFDerivAt (z : SpatialCoordinates d) (a b : Fin d)
    (x : SpatialCoordinates d) :
    HasFDerivAt (aux_thm_prop_lc_swap z a b) (aux_thm_prop_lc_swapDeriv a b) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  change HasFDerivAt (fun y : SpatialCoordinates d => z i + (y (Equiv.swap a b i) -
    z (Equiv.swap a b i))) (ContinuousLinearMap.proj (Equiv.swap a b i)) x
  exact ((hasFDerivAt_apply (𝕜 := ℝ) (Equiv.swap a b i) x).sub_const _).const_add _

theorem aux_thm_prop_lc_swap_contDiff (z : SpatialCoordinates d) (a b : Fin d) :
    ContDiff ℝ ∞ (aux_thm_prop_lc_swap z a b) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.add ((contDiff_apply ℝ ℝ _).sub contDiff_const)

theorem aux_thm_prop_lc_fderiv_comp_swap (z : SpatialCoordinates d) (a b : Fin d)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : SpatialCoordinates d) (i : Fin d) :
    fderiv ℝ (f ∘ aux_thm_prop_lc_swap z a b) x (Pi.single i 1) =
      fderiv ℝ f (aux_thm_prop_lc_swap z a b x) (Pi.single (Equiv.swap a b i) 1) := by
  rw [fderiv_comp x (hf.differentiable (by norm_num) _)
    (aux_thm_prop_lc_swap_hasFDerivAt z a b x).differentiableAt,
    (aux_thm_prop_lc_swap_hasFDerivAt z a b x).fderiv, ContinuousLinearMap.comp_apply,
    aux_thm_prop_lc_swapDeriv_single]

/-! ### Lp pullback -/

section swapLp
variable {U Ω : Opens (SpatialCoordinates d)}

def aux_thm_prop_lc_swapLp (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d))) →ₗᵢ[ℝ]
      Lp ℝ p (volume.restrict (U : Set (SpatialCoordinates d))) :=
  Lp.compMeasurePreservingₗᵢ ℝ (aux_thm_prop_lc_swap z a b)
    (aux_thm_prop_lc_swap_domain_measurePreserving z a b hU)

theorem aux_thm_prop_lc_swapLp_coeFn (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    (aux_thm_prop_lc_swapLp z a b hU f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] f ∘ aux_thm_prop_lc_swap z a b :=
  Lp.coeFn_compMeasurePreserving f (aux_thm_prop_lc_swap_domain_measurePreserving z a b hU)

theorem aux_thm_prop_lc_swapLp_inverse (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    aux_thm_prop_lc_swapLp z a b (aux_thm_prop_lc_swap_preimage_reverse z a b hU)
      (aux_thm_prop_lc_swapLp z a b hU f) = f := by
  apply Lp.ext
  have hm := aux_thm_prop_lc_swap_domain_measurePreserving z a b
    (aux_thm_prop_lc_swap_preimage_reverse z a b hU)
  filter_upwards [aux_thm_prop_lc_swapLp_coeFn z a b
    (aux_thm_prop_lc_swap_preimage_reverse z a b hU) (aux_thm_prop_lc_swapLp z a b hU f),
    hm.quasiMeasurePreserving.ae_eq_comp (aux_thm_prop_lc_swapLp_coeFn z a b hU f)] with x hx hy
  exact hx.trans (hy.trans (congrArg f (aux_thm_prop_lc_swap_involutive z a b x)))

/-! ### Smooth tests -/

def aux_thm_prop_lc_swapTest (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) : 𝓓(U, ℝ) where
  toFun := φ ∘ aux_thm_prop_lc_swap z a b
  contDiff' := φ.contDiff.comp (aux_thm_prop_lc_swap_contDiff z a b)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (aux_thm_prop_lc_swapHomeo z a b)
  tsupport_subset' := by
    change tsupport (φ ∘ (aux_thm_prop_lc_swapHomeo z a b)) ⊆ U
    rw [tsupport_comp_eq_preimage]
    intro x hx
    rw [← hU]
    exact φ.tsupport_subset hx

theorem aux_thm_prop_lc_testL2_swapTest (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) :
    testL2 (aux_thm_prop_lc_swapTest z a b hU φ) = aux_thm_prop_lc_swapLp z a b hU (testL2 φ) := by
  apply Lp.ext
  have hm := aux_thm_prop_lc_swap_domain_measurePreserving z a b hU
  filter_upwards [testL2_coeFn (aux_thm_prop_lc_swapTest z a b hU φ),
    aux_thm_prop_lc_swapLp_coeFn z a b hU (testL2 φ),
    hm.quasiMeasurePreserving.ae_eq_comp (testL2_coeFn φ)] with x hx hy hz
  exact hx.trans (hz.symm.trans hy.symm)

theorem aux_thm_prop_lc_testPartialL2_swapTest (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    testPartialL2 (aux_thm_prop_lc_swapTest z a b hU φ) i =
      aux_thm_prop_lc_swapLp z a b hU (testPartialL2 φ (Equiv.swap a b i)) := by
  apply Lp.ext
  have hm := aux_thm_prop_lc_swap_domain_measurePreserving z a b hU
  filter_upwards [testPartialL2_coeFn (aux_thm_prop_lc_swapTest z a b hU φ) i,
    aux_thm_prop_lc_swapLp_coeFn z a b hU (testPartialL2 φ (Equiv.swap a b i)),
    hm.quasiMeasurePreserving.ae_eq_comp (testPartialL2_coeFn φ (Equiv.swap a b i))]
    with x hx hy hz
  simp only [Function.comp_apply] at hy hz
  rw [hx, hy, hz]
  exact aux_thm_prop_lc_fderiv_comp_swap z a b φ.contDiff x i

theorem aux_thm_prop_lc_swapTest_inverse (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) :
    aux_thm_prop_lc_swapTest z a b (aux_thm_prop_lc_swap_preimage_reverse z a b hU)
      (aux_thm_prop_lc_swapTest z a b hU φ) = φ := by
  apply TestFunction.ext
  intro x
  exact congrArg φ (aux_thm_prop_lc_swap_involutive z a b x)

/-! ### Sobolev graphs -/

def aux_thm_prop_lc_swapSobolevData (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    SobolevData Ω →L[ℝ] SobolevData U :=
  ((aux_thm_prop_lc_swapLp z a b hU).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.pi fun i =>
      ((aux_thm_prop_lc_swapLp z a b hU).toContinuousLinearMap.comp
        ((ContinuousLinearMap.proj (Equiv.swap a b i)).comp (ContinuousLinearMap.snd ℝ _ _))))

theorem aux_thm_prop_lc_swapSobolevData_smooth (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) :
    aux_thm_prop_lc_swapSobolevData z a b hU (smoothSobolevData φ) =
      smoothSobolevData (aux_thm_prop_lc_swapTest z a b hU φ) := by
  apply Prod.ext
  · exact (aux_thm_prop_lc_testL2_swapTest z a b hU φ).symm
  · funext i
    exact (aux_thm_prop_lc_testPartialL2_swapTest z a b hU φ i).symm

theorem aux_thm_prop_lc_weakGradientTest_swap (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) (i : Fin d) (u : SobolevData Ω) :
    weakGradientTest (aux_thm_prop_lc_swapTest z a b hU φ) i
        (aux_thm_prop_lc_swapSobolevData z a b hU u) =
      weakGradientTest φ (Equiv.swap a b i) u := by
  change inner ℝ (testL2 (aux_thm_prop_lc_swapTest z a b hU φ))
      (aux_thm_prop_lc_swapLp z a b hU (u.2 (Equiv.swap a b i))) +
    inner ℝ (testPartialL2 (aux_thm_prop_lc_swapTest z a b hU φ) i)
      (aux_thm_prop_lc_swapLp z a b hU u.1) =
      inner ℝ (testL2 φ) (u.2 (Equiv.swap a b i)) +
        inner ℝ (testPartialL2 φ (Equiv.swap a b i)) u.1
  rw [aux_thm_prop_lc_testL2_swapTest, aux_thm_prop_lc_testPartialL2_swapTest,
    (aux_thm_prop_lc_swapLp z a b hU (p := 2)).inner_map_map,
    (aux_thm_prop_lc_swapLp z a b hU (p := 2)).inner_map_map]

theorem aux_thm_prop_lc_swapSobolevData_mem_weak (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {u : SobolevData Ω} (hu : u ∈ weakSobolevGraph Ω) :
    aux_thm_prop_lc_swapSobolevData z a b hU u ∈ weakSobolevGraph U := by
  simp only [weakSobolevGraph, Submodule.mem_iInf, LinearMap.mem_ker] at hu ⊢
  intro ψ i
  let φ := aux_thm_prop_lc_swapTest z a b (aux_thm_prop_lc_swap_preimage_reverse z a b hU) ψ
  have hinv : aux_thm_prop_lc_swapTest z a b hU φ = ψ :=
    aux_thm_prop_lc_swapTest_inverse z a b (aux_thm_prop_lc_swap_preimage_reverse z a b hU) ψ
  have h := aux_thm_prop_lc_weakGradientTest_swap z a b hU φ i u
  rw [hinv] at h
  have hh : (weakGradientTest ψ i) (aux_thm_prop_lc_swapSobolevData z a b hU u) =
      (weakGradientTest φ (Equiv.swap a b i)) u := by
    simpa only using! h
  exact hh.trans (hu φ (Equiv.swap a b i))

theorem aux_thm_prop_lc_swapSobolevData_mem_killed (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {u : SobolevData Ω} (hu : u ∈ killedSobolevGraph Ω) :
    aux_thm_prop_lc_swapSobolevData z a b hU u ∈ killedSobolevGraph U := by
  have hm : Set.MapsTo (aux_thm_prop_lc_swapSobolevData z a b hU)
      (Set.range (smoothSobolevData (Ω := Ω)))
      (killedSobolevGraph U : Set (SobolevData U)) := by
    rintro v ⟨φ, rfl⟩
    rw [aux_thm_prop_lc_swapSobolevData_smooth]
    exact smoothSobolevData_mem_killed _
  apply hm.closure_left (aux_thm_prop_lc_swapSobolevData z a b hU).continuous
    (isClosed_killedSobolevGraph (Ω := U))
  rw [← killedSobolevGraph_coe_eq_closure]
  exact hu

theorem aux_thm_prop_lc_swapSobolevData_inverse (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) :
    aux_thm_prop_lc_swapSobolevData z a b (aux_thm_prop_lc_swap_preimage_reverse z a b hU)
      (aux_thm_prop_lc_swapSobolevData z a b hU u) = u := by
  apply Prod.ext
  · exact aux_thm_prop_lc_swapLp_inverse z a b hU u.1
  · funext i
    change aux_thm_prop_lc_swapLp z a b (aux_thm_prop_lc_swap_preimage_reverse z a b hU)
      (aux_thm_prop_lc_swapLp z a b hU (u.2 (Equiv.swap a b (Equiv.swap a b i)))) = u.2 i
    rw [Equiv.swap_apply_self, aux_thm_prop_lc_swapLp_inverse]

def aux_thm_prop_lc_swapKilledEquiv (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    killedSobolevGraph Ω ≃ killedSobolevGraph U where
  toFun u := ⟨aux_thm_prop_lc_swapSobolevData z a b hU u.val,
    aux_thm_prop_lc_swapSobolevData_mem_killed z a b hU u.property⟩
  invFun u := ⟨aux_thm_prop_lc_swapSobolevData z a b
      (aux_thm_prop_lc_swap_preimage_reverse z a b hU) u.val,
    aux_thm_prop_lc_swapSobolevData_mem_killed z a b
      (aux_thm_prop_lc_swap_preimage_reverse z a b hU) u.property⟩
  left_inv u := Subtype.ext (aux_thm_prop_lc_swapSobolevData_inverse z a b hU u.val)
  right_inv u := Subtype.ext (aux_thm_prop_lc_swapSobolevData_inverse z a b
    (aux_thm_prop_lc_swap_preimage_reverse z a b hU) u.val)

/-! ### Coefficients and energies -/

def aux_thm_prop_lc_swapCoefficient (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (c : PositiveCoefficient Ω) : PositiveCoefficient U := by
  refine ⟨aux_thm_prop_lc_swapLp z a b hU c.val, ?_⟩
  obtain ⟨e, he, hc⟩ := c.property
  refine ⟨e, he, ?_⟩
  have hm := aux_thm_prop_lc_swap_domain_measurePreserving z a b hU
  filter_upwards [aux_thm_prop_lc_swapLp_coeFn z a b hU c.val,
    hm.quasiMeasurePreserving.ae hc] with x hx hy
  exact hx.symm ▸ hy

theorem aux_thm_prop_lc_swapCoefficient_coeFn (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (c : PositiveCoefficient Ω) :
    ((aux_thm_prop_lc_swapCoefficient z a b hU c).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] c.val ∘ aux_thm_prop_lc_swap z a b :=
  aux_thm_prop_lc_swapLp_coeFn z a b hU c.val

theorem aux_thm_prop_lc_swapSobolevData_gradient_coeFn (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) (i : Fin d) :
    ((aux_thm_prop_lc_swapSobolevData z a b hU u).2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
      fun x => u.2 (Equiv.swap a b i) (aux_thm_prop_lc_swap z a b x) :=
  aux_thm_prop_lc_swapLp_coeFn z a b hU (u.2 (Equiv.swap a b i))

/-- Swapping the domain, coefficient, variation and slope preserves the affine objective. -/
theorem aux_thm_prop_lc_affineDirichletObjective_swap (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (c : PositiveCoefficient Ω) (p : Fin d → ℝ) (u : SobolevData Ω) :
    (∑ i : Fin d, ∫ x in (U : Set (SpatialCoordinates d)),
      (aux_thm_prop_lc_swapCoefficient z a b hU c).val x *
        (p (Equiv.swap a b i) + (aux_thm_prop_lc_swapSobolevData z a b hU u).2 i x) ^ 2) =
    ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
      c.val x * (p i + u.2 i x) ^ 2 := by
  have hterm : ∀ i : Fin d, (∫ x in (U : Set (SpatialCoordinates d)),
      (aux_thm_prop_lc_swapCoefficient z a b hU c).val x *
        (p (Equiv.swap a b i) + (aux_thm_prop_lc_swapSobolevData z a b hU u).2 i x) ^ 2) =
      ∫ x in (Ω : Set (SpatialCoordinates d)),
        c.val x * (p (Equiv.swap a b i) + u.2 (Equiv.swap a b i) x) ^ 2 := by
    intro i
    calc
      _ = ∫ x in (U : Set (SpatialCoordinates d)),
          c.val (aux_thm_prop_lc_swap z a b x) *
            (p (Equiv.swap a b i) + u.2 (Equiv.swap a b i) (aux_thm_prop_lc_swap z a b x)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [aux_thm_prop_lc_swapCoefficient_coeFn z a b hU c,
          aux_thm_prop_lc_swapSobolevData_gradient_coeFn z a b hU u i] with x hc hu
        rw [hc, hu, Function.comp_apply]
      _ = _ := (aux_thm_prop_lc_swap_domain_measurePreserving z a b hU).integral_comp
        (aux_thm_prop_lc_swapHomeo z a b).measurableEmbedding
        (fun y => c.val y * (p (Equiv.swap a b i) + u.2 (Equiv.swap a b i) y) ^ 2)
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact Fintype.sum_equiv (Equiv.swap a b) _ _ fun i => rfl

variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
variable [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]

/-- The affine Dirichlet minimum is unchanged by swapping domain, coefficient and slope. -/
theorem aux_thm_prop_lc_affineDirichletResponse_swap (z : SpatialCoordinates d) (a b : Fin d)
    (hU : aux_thm_prop_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hUb : Bornology.IsBounded (U : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (hDU : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) u‖)
    (c : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineDirichletResponse hUb hDU (aux_thm_prop_lc_swapCoefficient z a b hU c)
      (p ∘ Equiv.swap a b) = affineDirichletResponse hΩ hD c p := by
  let f : killedSobolevGraph U → ℝ := fun u =>
    ∑ i : Fin d, ∫ x in (U : Set (SpatialCoordinates d)),
      (aux_thm_prop_lc_swapCoefficient z a b hU c).val x *
        ((p ∘ Equiv.swap a b) i + (u : SobolevData U).2 i x) ^ 2
  have he : Set.range f = Set.range (fun u : killedSobolevGraph Ω =>
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        c.val x * (p i + (u : SobolevData Ω).2 i x) ^ 2) := by
    rw [← (aux_thm_prop_lc_swapKilledEquiv z a b hU).surjective.range_comp f]
    congr 1
    funext u
    exact aux_thm_prop_lc_affineDirichletObjective_swap z a b hU c p u.val
  apply (affineDirichletResponse_isLeast hUb hDU
    (aux_thm_prop_lc_swapCoefficient z a b hU c) (p ∘ Equiv.swap a b)).unique
  change IsLeast (Set.range f) _
  rw [he]
  exact affineDirichletResponse_isLeast hΩ hD c p

end swapLp


end PCSwapScope

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
variable {d : ℕ}

def aux_thm_prop_lc_reflAct (i : Fin d) (N : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => (if a = i then -(1 : ℝ) else 1) * (if b = i then -(1 : ℝ) else 1) * N a b

theorem aux_thm_prop_lc_reflAct_diag (i a : Fin d) (N : Matrix (Fin d) (Fin d) ℝ) :
    aux_thm_prop_lc_reflAct i N a a = N a a := by
  unfold aux_thm_prop_lc_reflAct
  rcases eq_or_ne a i with h | h <;> simp [h]

theorem aux_thm_prop_lc_reflAct_symm (i : Fin d) {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) :
    (aux_thm_prop_lc_reflAct i A).transpose = aux_thm_prop_lc_reflAct i A := by
  have hsym : ∀ a b, A b a = A a b := by
    intro a b
    have h := congrFun (congrFun hA a) b
    simpa [Matrix.transpose_apply] using h
  funext a b
  simp only [Matrix.transpose_apply, aux_thm_prop_lc_reflAct]
  rw [hsym]; ring

theorem aux_thm_prop_lc_reflAct_trace (i : Fin d) (A : Matrix (Fin d) (Fin d) ℝ) :
    (aux_thm_prop_lc_reflAct i A).trace = A.trace := by
  unfold Matrix.trace Matrix.diag
  exact Finset.sum_congr rfl (fun a _ => aux_thm_prop_lc_reflAct_diag i a A)


theorem aux_thm_prop_lc_reflAct_quadForm (i : Fin d) (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
    p ⬝ᵥ (aux_thm_prop_lc_reflAct i A).mulVec p =
      (fun a => (if a = i then -(1 : ℝ) else 1) * p a) ⬝ᵥ
        A.mulVec (fun a => (if a = i then -(1 : ℝ) else 1) * p a) := by
  simp only [dotProduct, Matrix.mulVec, aux_thm_prop_lc_reflAct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rcases eq_or_ne a i with ha | ha <;> rcases eq_or_ne b i with hb | hb <;> simp [ha, hb]




def aux_thm_prop_lc_permAct (σ : Equiv.Perm (Fin d)) (N : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a b => N (σ a) (σ b)

theorem aux_thm_prop_lc_permAct_diag (σ : Equiv.Perm (Fin d)) (a : Fin d)
    (N : Matrix (Fin d) (Fin d) ℝ) :
    aux_thm_prop_lc_permAct σ N a a = N (σ a) (σ a) := rfl

theorem aux_thm_prop_lc_permAct_symm (σ : Equiv.Perm (Fin d)) {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) :
    (aux_thm_prop_lc_permAct σ A).transpose = aux_thm_prop_lc_permAct σ A := by
  have hsym : ∀ a b, A b a = A a b := by
    intro a b
    have h := congrFun (congrFun hA a) b
    simpa [Matrix.transpose_apply] using h
  funext a b
  simp only [Matrix.transpose_apply, aux_thm_prop_lc_permAct]
  rw [hsym]

theorem aux_thm_prop_lc_swapAct_trace (a b : Fin d) (A : Matrix (Fin d) (Fin d) ℝ) :
    (aux_thm_prop_lc_permAct (Equiv.swap a b) A).trace = A.trace := by
  unfold Matrix.trace Matrix.diag
  simp only [aux_thm_prop_lc_permAct]
  exact Equiv.sum_comp (Equiv.swap a b) (fun c => A c c)

theorem aux_thm_prop_lc_permAct_submatrix (σ : Equiv.Perm (Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) :
    aux_thm_prop_lc_permAct σ A = A.submatrix (⇑σ) (⇑σ) := rfl


theorem aux_thm_prop_lc_swapAct_quadForm (a b : Fin d) (A : Matrix (Fin d) (Fin d) ℝ)
    (p : Fin d → ℝ) :
    p ⬝ᵥ (aux_thm_prop_lc_permAct (Equiv.swap a b) A).mulVec p =
      (p ∘ Equiv.swap a b) ⬝ᵥ A.mulVec (p ∘ Equiv.swap a b) := by
  rw [aux_thm_prop_lc_permAct_submatrix, Matrix.submatrix_mulVec_equiv, Equiv.symm_swap]
  rw [← comp_equiv_symm_dotProduct p (A.mulVec (p ∘ ⇑(Equiv.swap a b))) (Equiv.swap a b),
    Equiv.symm_swap]



theorem aux_thm_prop_lc_matrix_entry_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {g : X → Matrix (Fin d) (Fin d) ℝ} (hg : Measurable g) (i j : Fin d) :
    Measurable (fun x => g x i j) := by
  have h1 : Measurable (fun x => g x i) := (measurable_pi_apply i).comp hg
  exact (measurable_pi_apply j).comp h1

theorem aux_thm_prop_lc_trace_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {g : X → Matrix (Fin d) (Fin d) ℝ} (hg : Measurable g) :
    Measurable (fun x => Matrix.trace (g x)) := by
  unfold Matrix.trace Matrix.diag
  exact Finset.measurable_sum _ fun i _ => aux_thm_prop_lc_matrix_entry_measurable hg i i


theorem aux_thm_prop_lc_normpair_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {gE gF : X → Matrix (Fin d) (Fin d) ℝ} (hgE : Measurable gE) (hgF : Measurable gF) :
    Measurable (fun x => aux_thm_prop_lc_normpair (gE x) (gF x)) := by
  unfold aux_thm_prop_lc_normpair
  apply Measurable.prodMk
  · exact Measurable.of_eval fun j => Measurable.of_eval fun l =>
      (aux_thm_prop_lc_matrix_entry_measurable hgE j l).div (aux_thm_prop_lc_trace_measurable hgE)
  · exact Measurable.of_eval fun j => Measurable.of_eval fun l =>
      (aux_thm_prop_lc_matrix_entry_measurable hgF j l).div (aux_thm_prop_lc_trace_measurable hgE)

theorem aux_thm_prop_lc_reflpair_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {XY : X → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hXY : Measurable XY) (i : Fin d) :
    Measurable (fun x => aux_thm_prop_lc_reflpair i (XY x)) := by
  unfold aux_thm_prop_lc_reflpair
  exact Measurable.prodMk
    (Measurable.of_eval fun a => Measurable.of_eval fun b =>
      measurable_const.mul ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hXY.fst)))
    (Measurable.of_eval fun a => Measurable.of_eval fun b =>
      measurable_const.mul ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hXY.snd)))

theorem aux_thm_prop_lc_permpair_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {XY : X → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hXY : Measurable XY)
    (σ : Equiv.Perm (Fin d)) :
    Measurable (fun x => aux_thm_prop_lc_permpair σ (XY x)) := by
  unfold aux_thm_prop_lc_permpair
  exact Measurable.prodMk
    (Measurable.of_eval fun a => Measurable.of_eval fun b =>
      (measurable_pi_apply (σ b)).comp ((measurable_pi_apply (σ a)).comp hXY.fst))
    (Measurable.of_eval fun a => Measurable.of_eval fun b =>
      (measurable_pi_apply (σ b)).comp ((measurable_pi_apply (σ a)).comp hXY.snd))


theorem aux_thm_prop_lc_normpair_smul {d : ℕ} (c : ℝ) (hc : c ≠ 0)
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    aux_thm_prop_lc_normpair (c • A) (c • B) = aux_thm_prop_lc_normpair A B := by
  unfold aux_thm_prop_lc_normpair
  rw [Matrix.trace_smul, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> funext j l <;>
    simp only [Matrix.smul_apply, smul_eq_mul] <;> exact mul_div_mul_left _ _ hc


theorem aux_thm_prop_lc_normpair_permAct {d : ℕ} (σ : Equiv.Perm (Fin d))
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    aux_thm_prop_lc_normpair (aux_thm_prop_lc_permAct σ A) (aux_thm_prop_lc_permAct σ B) =
      aux_thm_prop_lc_permpair σ (aux_thm_prop_lc_normpair A B) := by
  have htr : (aux_thm_prop_lc_permAct σ A).trace = A.trace := by
    unfold Matrix.trace Matrix.diag aux_thm_prop_lc_permAct
    exact Equiv.sum_comp σ (fun c => A c c)
  unfold aux_thm_prop_lc_normpair aux_thm_prop_lc_permpair
  rw [htr]
  rfl


theorem aux_thm_prop_lc_normpair_reflAct {d : ℕ} (i : Fin d) (A B : Matrix (Fin d) (Fin d) ℝ) :
    aux_thm_prop_lc_normpair (aux_thm_prop_lc_reflAct i A) (aux_thm_prop_lc_reflAct i B) =
      aux_thm_prop_lc_reflpair i (aux_thm_prop_lc_normpair A B) := by
  simp only [aux_thm_prop_lc_normpair, aux_thm_prop_lc_reflpair, aux_thm_prop_lc_reflAct_trace]
  refine Prod.ext ?_ ?_ <;> funext j l <;>
    simp only [aux_thm_prop_lc_reflAct, aux_thm_prop_lc_sign] <;> ring


def aux_thm_prop_lc_reflLinear (i : Fin d) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ where
  toFun := aux_thm_prop_lc_reflAct i
  map_add' := by
    intro A B
    ext a b
    simp only [aux_thm_prop_lc_reflAct, Matrix.add_apply]
    ring
  map_smul' := by
    intro c A
    ext a b
    simp only [aux_thm_prop_lc_reflAct, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  cont := continuous_pi fun a => continuous_pi fun b =>
    continuous_const.mul ((continuous_apply b).comp (continuous_apply a))

def aux_thm_prop_lc_permLinear (s : Equiv.Perm (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ where
  toFun := aux_thm_prop_lc_permAct s
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply (s b)).comp (continuous_apply (s a))

/-- Law invariance under transpositions gives law invariance under all
coordinate permutations for an arbitrary measurable random matrix pair. -/
theorem aux_thm_prop_lc_perm_law_of_swaps
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ))
    (hX : AEMeasurable X P)
    (hswap : ∀ a b, P.map X = P.map (fun x => aux_thm_prop_lc_permpair (Equiv.swap a b) (X x))) :
    ∀ s : Equiv.Perm (Fin d), P.map X =
      P.map (fun x => aux_thm_prop_lc_permpair s (X x)) := by
  intro s
  induction s using Equiv.Perm.swap_induction_on with
  | one =>
    have h : (fun x => aux_thm_prop_lc_permpair (1 : Equiv.Perm (Fin d)) (X x)) = X := by
      funext x
      simp only [aux_thm_prop_lc_permpair, Equiv.Perm.one_apply]
    rw [h]
  | swap_mul s a b _ ih =>
    have hs : Measurable (aux_thm_prop_lc_permpair (d := d) s) :=
      aux_thm_prop_lc_permpair_measurable measurable_id s
    have hsw : Measurable (aux_thm_prop_lc_permpair (d := d) (Equiv.swap a b)) :=
      aux_thm_prop_lc_permpair_measurable measurable_id (Equiv.swap a b)
    have hcomp : (fun x => aux_thm_prop_lc_permpair (Equiv.swap a b * s) (X x)) =
        aux_thm_prop_lc_permpair s ∘
          (fun x => aux_thm_prop_lc_permpair (Equiv.swap a b) (X x)) := by
      funext x
      simp only [Function.comp_apply, aux_thm_prop_lc_permpair, Equiv.Perm.mul_apply]
    have hSX : AEMeasurable
        (fun x => aux_thm_prop_lc_permpair (Equiv.swap a b) (X x)) P :=
      hsw.comp_aemeasurable hX
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hSX,
      ← hswap a b]
    exact ih.trans (AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hX).symm

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
variable {d : ℕ}

def aux_thm_prop_lc_reflSign (a : Fin d) (i : Fin d) : ℝ := if i = a then -1 else 1

theorem aux_thm_prop_lc_refl_isSigned (a : Fin d) :
    IsSignedPermutationMatrix (Matrix.diagonal (aux_thm_prop_lc_reflSign a) : Homogenization.Mat d) := by
  refine ⟨Equiv.refl _, aux_thm_prop_lc_reflSign a, fun i => ?_, fun i j => ?_⟩
  · unfold aux_thm_prop_lc_reflSign
    split_ifs <;> simp
  · simp only [Matrix.diagonal_apply, Equiv.refl_apply]
    split_ifs with h
    · subst h; simp only [ite_true]
    · simp only [h, ite_false]


def aux_thm_prop_lc_swapMat (a b : Fin d) : Homogenization.Mat d :=
  fun i j => if i = Equiv.swap a b j then 1 else 0

theorem aux_thm_prop_lc_swap_isSigned (a b : Fin d) :
    IsSignedPermutationMatrix (aux_thm_prop_lc_swapMat a b) :=
  ⟨Equiv.swap a b, fun _ => 1, fun _ => Or.inl rfl, fun _ _ => rfl⟩

theorem aux_thm_prop_lc_matVecMul_refl (a : Fin d) (y : SpatialCoordinates d) (i : Fin d) :
    matVecMul (Matrix.diagonal (aux_thm_prop_lc_reflSign a) : Homogenization.Mat d) y i =
      aux_thm_prop_lc_reflSign a i * y i := by
  simp only [matVecMul, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem aux_thm_prop_lc_matVecMul_swap (a b : Fin d) (y : SpatialCoordinates d) (i : Fin d) :
    matVecMul (aux_thm_prop_lc_swapMat a b) y i = y (Equiv.swap a b i) := by
  simp only [matVecMul, aux_thm_prop_lc_swapMat]
  rw [Finset.sum_eq_single (Equiv.swap a b i)]
  · simp
  · intro j _ hj
    rw [ite_eq_right]
    · ring
    · intro h
      apply hj
      rw [h, Equiv.swap_apply_self]
  · simp

theorem aux_thm_prop_lc_cpc_coeFn (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ y ∂volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d)),
      y ∈ (centeredCube z s hs : Set (SpatialCoordinates d)) →
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N z hs).val y =
        cutoffCoefficient model H x N y := by
  have : Fact ((centeredCube z s hs : Set (SpatialCoordinates d)) ⊆ closedCube z s hs) :=
    ⟨centeredCube_subset_closedCube z hs⟩
  filter_upwards [normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z s hs)
    (closedCube z s hs) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM model H x N z hs)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos model H x N z hs) 1 one_pos] with y hy hmem
  have h := hy hmem
  rw [div_one] at h
  exact h


theorem aux_thm_prop_lc_cpc_transform (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x x' : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (π : SpatialCoordinates d → SpatialCoordinates d)
    (hmp : MeasurePreserving π (volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))))
    (hmaps : ∀ y ∈ (centeredCube z s hs : Set (SpatialCoordinates d)),
      π y ∈ (centeredCube z s hs : Set (SpatialCoordinates d)))
    (piCoef : PositiveCoefficient (centeredCube z s hs) →
      PositiveCoefficient (centeredCube z s hs))
    (hpi : ∀ a : PositiveCoefficient (centeredCube z s hs),
      ((piCoef a).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] a.val ∘ π)
    (c : ℝ)
    (hcoef : ∀ y, cutoffCoefficient model H x' N y =
      Real.exp (-c) * cutoffCoefficient model H x N (π y)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x' N z hs =
      smulPositiveCoefficient (Real.exp_pos (-c))
        (piCoef (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N z hs)) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [aux_thm_prop_lc_cpc_coeFn model H x' N z hs,
    smulPositiveCoefficient_coeFn (Real.exp_pos (-c))
      (piCoef (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N z hs)),
    hpi (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N z hs),
    hmp.quasiMeasurePreserving.ae (aux_thm_prop_lc_cpc_coeFn model H x N z hs),
    ae_restrict_mem (centeredCube z s hs).isOpen.measurableSet] with y e1 e2 e3 e4 hy
  change (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x' N z hs).val y =
    (smulPositiveCoefficient (Real.exp_pos (-c))
      (piCoef (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N z hs))).val y
  rw [e1 hy, e2, e3, Function.comp_apply, e4 (hmaps y hy), hcoef]




def aux_thm_prop_lc_reflShift (z : SpatialCoordinates d) (a : Fin d) : SpatialCoordinates d :=
  fun i => if i = a then 2 * z i else 0

theorem aux_thm_prop_lc_affineMap_refl (z : SpatialCoordinates d) (a : Fin d)
    (y : SpatialCoordinates d) :
    aux_thm_prop_affineMap (Matrix.diagonal (aux_thm_prop_lc_reflSign a))
      (aux_thm_prop_lc_reflShift z a) y = coordinateReflection z {a} y := by
  funext i
  rw [aux_thm_prop_affineMap_apply, Pi.add_apply, aux_thm_prop_lc_matVecMul_refl]
  simp only [aux_thm_prop_lc_reflSign, aux_thm_prop_lc_reflShift, coordinateReflection,
    Finset.mem_singleton]
  split_ifs <;> ring


def aux_thm_prop_lc_swapShift (z : SpatialCoordinates d) (a b : Fin d) : SpatialCoordinates d :=
  fun i => z i - z (Equiv.swap a b i)

theorem aux_thm_prop_lc_affineMap_swap (z : SpatialCoordinates d) (a b : Fin d)
    (y : SpatialCoordinates d) :
    aux_thm_prop_affineMap (aux_thm_prop_lc_swapMat a b) (aux_thm_prop_lc_swapShift z a b) y =
      aux_thm_prop_lc_swap z a b y := by
  funext i
  rw [aux_thm_prop_affineMap_apply, Pi.add_apply, aux_thm_prop_lc_matVecMul_swap]
  simp only [aux_thm_prop_lc_swapShift, aux_thm_prop_lc_swap]
  ring

theorem aux_thm_prop_lc_refl_self (z : SpatialCoordinates d) (a : Fin d) :
    coordinateReflection z {a} z = z := by
  funext i
  simp only [coordinateReflection]
  split_ifs <;> ring

theorem aux_thm_prop_lc_refl_preimage_cube (z : SpatialCoordinates d) (a : Fin d) {s : ℝ}
    (hs : 0 < s) :
    coordinateReflection z {a} ⁻¹' (centeredCube z s hs : Set (SpatialCoordinates d)) =
      (centeredCube z s hs : Set (SpatialCoordinates d)) := by
  have h := coordinateReflection_preimage_cube z {a} z hs
  rwa [aux_thm_prop_lc_refl_self] at h

def aux_thm_prop_lc_response
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zcell : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell s hs),
      ‖(u : SobolevData (centeredCube zcell s hs)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell s hs)) u‖)
    (N : ℕ) (x : BilateralField d) (p : Fin d → ℝ) : ℝ :=
  affineDirichletResponse (centeredCube_isBounded zcell hs) hP
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N zcell hs) p /
      (volume (centeredCube zcell s hs : Set (SpatialCoordinates d))).toReal

theorem aux_thm_prop_lc_resp_refl (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (zcell : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell s hs),
      ‖(u : SobolevData (centeredCube zcell s hs)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell s hs)) u‖)
    (a : Fin d) (x : BilateralField d)
    (hH : H (aux_thm_prop_T (Matrix.diagonal (aux_thm_prop_lc_reflSign a))
        (aux_thm_prop_lc_reflShift zcell a) x) =
      aux_thm_prop_gauge (Matrix.diagonal (aux_thm_prop_lc_reflSign a))
        (aux_thm_prop_lc_reflShift zcell a) (H x))
    (N : ℕ) (p : Fin d → ℝ) :
    aux_thm_prop_lc_response model H zcell hs hP N
        (aux_thm_prop_T (Matrix.diagonal (aux_thm_prop_lc_reflSign a))
          (aux_thm_prop_lc_reflShift zcell a) x) p =
      Real.exp (-(H x (aux_thm_prop_affineMap (Matrix.diagonal (aux_thm_prop_lc_reflSign a))
          (aux_thm_prop_lc_reflShift zcell a) 0))) *
        aux_thm_prop_lc_response model H zcell hs hP N x (coordinateReflectionDerivative {a} p) := by
  have hU := aux_thm_prop_lc_refl_preimage_cube zcell a hs
  have hcpc := aux_thm_prop_lc_cpc_transform model H x
    (aux_thm_prop_T (Matrix.diagonal (aux_thm_prop_lc_reflSign a))
      (aux_thm_prop_lc_reflShift zcell a) x) N zcell hs (coordinateReflection zcell {a})
    (coordinateReflection_domain_measurePreserving zcell {a} hU)
    (fun y hy => by rw [← hU] at hy; exact hy)
    (reflectionCoefficient zcell {a} hU) (fun c => reflectionCoefficient_coeFn zcell {a} hU c)
    (H x (aux_thm_prop_affineMap (Matrix.diagonal (aux_thm_prop_lc_reflSign a))
      (aux_thm_prop_lc_reflShift zcell a) 0))
    (fun y => by
      rw [aux_thm_prop_cutoffCoefficient_T model _ _ H x hH N y,
        aux_thm_prop_lc_affineMap_refl zcell a y])
  unfold aux_thm_prop_lc_response
  rw [hcpc, affineDirichletResponse_smulCoeff, mul_div_assoc]
  congr 2
  have h := affineDirichletResponse_reflection zcell {a} hU (centeredCube_isBounded zcell hs)
    (centeredCube_isBounded zcell hs) hP hP
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N zcell hs) (coordinateReflectionDerivative {a} p)
  rwa [coordinateReflectionDerivative_involutive] at h


theorem aux_thm_prop_lc_resp_swap (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (zcell : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell s hs),
      ‖(u : SobolevData (centeredCube zcell s hs)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell s hs)) u‖)
    (a b : Fin d) (x : BilateralField d)
    (hH : H (aux_thm_prop_T (aux_thm_prop_lc_swapMat a b) (aux_thm_prop_lc_swapShift zcell a b) x) =
      aux_thm_prop_gauge (aux_thm_prop_lc_swapMat a b) (aux_thm_prop_lc_swapShift zcell a b) (H x))
    (N : ℕ) (p : Fin d → ℝ) :
    aux_thm_prop_lc_response model H zcell hs hP N
        (aux_thm_prop_T (aux_thm_prop_lc_swapMat a b) (aux_thm_prop_lc_swapShift zcell a b) x) p =
      Real.exp (-(H x (aux_thm_prop_affineMap (aux_thm_prop_lc_swapMat a b)
          (aux_thm_prop_lc_swapShift zcell a b) 0))) *
        aux_thm_prop_lc_response model H zcell hs hP N x (p ∘ Equiv.swap a b) := by
  have hU := aux_thm_prop_lc_swap_preimage_cube zcell a b hs
  have hcpc := aux_thm_prop_lc_cpc_transform model H x
    (aux_thm_prop_T (aux_thm_prop_lc_swapMat a b) (aux_thm_prop_lc_swapShift zcell a b) x) N zcell hs
    (aux_thm_prop_lc_swap zcell a b)
    (aux_thm_prop_lc_swap_domain_measurePreserving zcell a b hU)
    (fun y hy => by rw [← hU] at hy; exact hy)
    (aux_thm_prop_lc_swapCoefficient zcell a b hU)
    (fun c => aux_thm_prop_lc_swapCoefficient_coeFn zcell a b hU c)
    (H x (aux_thm_prop_affineMap (aux_thm_prop_lc_swapMat a b)
      (aux_thm_prop_lc_swapShift zcell a b) 0))
    (fun y => by
      rw [aux_thm_prop_cutoffCoefficient_T model _ _ H x hH N y,
        aux_thm_prop_lc_affineMap_swap zcell a b y])
  unfold aux_thm_prop_lc_response
  rw [hcpc, affineDirichletResponse_smulCoeff, mul_div_assoc]
  congr 2
  have h := aux_thm_prop_lc_affineDirichletResponse_swap zcell a b hU
    (centeredCube_isBounded zcell hs) (centeredCube_isBounded zcell hs) hP hP
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N zcell hs) (p ∘ Equiv.swap a b)
  have hpp : (p ∘ Equiv.swap a b) ∘ Equiv.swap a b = p := by
    funext i
    simp [Equiv.swap_apply_self]
  rwa [hpp] at h



end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_lc_field_symmetry_preserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R) (w : SpatialCoordinates d) :
    MeasurePreserving (aux_thm_prop_T R w)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure :=
  ⟨Measurable.of_eval (fun j =>
    (aux_thm_prop_precomp_measurable R w).comp (measurable_pi_apply j)),
    aux_thm_prop_chaos_invariant model R hR w⟩

theorem aux_thm_prop_lc_matrix_transform {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose = A) (_hB : B.transpose = B)
    (L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (hL : (L B).transpose = L B) (c : ℝ)
    (h : ∀ p : Fin d → ℝ, p ⬝ᵥ A.mulVec p = c * (p ⬝ᵥ (L B).mulVec p)) :
    A = c • L B := by
  apply aux_thm_prop_symmetric_matrix_ext hA
    (by rw [Matrix.transpose_smul, hL])
  intro p
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact h p

section Cell

variable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zcell : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell r hr),
      ‖(u : SobolevData (centeredCube zcell r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) u‖)

/-- Normalized matrix laws at one physical cube, obtained directly from its
two cutoff response sequences. No other cube or scale is in the hypotheses. -/
theorem aux_thm_prop_lc_one_cell_pair_law
    (hH : Measurable H) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (field : Ω → BilateralField d)
    (hfield : Measurable field) (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (NE NF : ℕ → ℕ) (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymE : ∀ om, (AE om).transpose = AE om)
    (hsymF : ∀ om, (AF om).transpose = AF om)
    (hAE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zcell r hr NE hP (AE om))
    (hAF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zcell r hr NF hP (AF om))
    (T : BilateralField d → BilateralField d)
    (hT : MeasurePreserving T (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure)
    (L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (hLsym : ∀ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = A → (L A).transpose = L A)
    (slope : (Fin d → ℝ) → (Fin d → ℝ))
    (hLquad : ∀ (A : Matrix (Fin d) (Fin d) ℝ) p,
      p ⬝ᵥ (L A).mulVec p = slope p ⬝ᵥ A.mulVec (slope p))
    (c : BilateralField d → ℝ)
    (hcov : ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, c x ≠ 0 ∧ ∀ N p,
      aux_thm_prop_lc_response model H zcell hr hP N (T x) p =
        c x * aux_thm_prop_lc_response model H zcell hr hP N x (slope p))
    (S : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) →
      (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ))
    (hS : Measurable S)
    (hNS : ∀ A B, aux_thm_prop_lc_normpair (L A) (L B) = S (aux_thm_prop_lc_normpair A B)) :
    P.map (fun om => aux_thm_prop_lc_normpair (AE om) (AF om)) =
      P.map (fun om => S (aux_thm_prop_lc_normpair (AE om) (AF om))) := by
  let AN := aux_thm_prop_cutoff_affine_matrix model H zcell hr hP
  have hAN : ∀ N, Measurable (AN N) :=
    aux_thm_prop_cutoff_affine_matrix_measurable model H hH zcell hr hP
  have hANE : ∀ᵐ om ∂P, Tendsto (fun n => AN (NE n) (field om)) atTop (𝓝 (AE om)) :=
    hAE.mono fun om h => aux_thm_prop_polar_matrix_limit _ _ (hsymE om) h
  have hANF : ∀ᵐ om ∂P, Tendsto (fun n => AN (NF n) (field om)) atTop (𝓝 (AF om)) :=
    hAF.mono fun om h => aux_thm_prop_polar_matrix_limit _ _ (hsymF om) h
  have hmatcov : ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, c x ≠ 0 ∧
      ∀ N, AN N (T x) = c x • L (AN N x) := by
    filter_upwards [hcov] with x hc
    refine ⟨hc.1, fun N => ?_⟩
    have hsym : ∀ y, (AN N y).transpose = AN N y :=
      fun y => aux_thm_prop_polar_matrix_symmetric _
    apply aux_thm_prop_lc_matrix_transform _ _ (hsym _) (hsym _) L (hLsym _ (hsym _))
    intro p
    rw [hLquad]
    exact (aux_thm_prop_cutoff_affine_matrix_quadratic model H zcell hr hP N (T x) p).trans
      ((hc.2 N p).trans (congrArg (c x * ·)
        (aux_thm_prop_cutoff_affine_matrix_quadratic model H zcell hr hP N x (slope p)).symm))
  exact aux_thm_prop_matrix_pair_law P (chaosSampleLaw model).toMeasure field hfield hlaw T hT
    (fun n => AN (NE n)) (fun n => AN (NF n)) (fun n => hAN (NE n)) (fun n => hAN (NF n))
    AE AF hANE hANF L c
    (hmatcov.mono fun x h => ⟨h.1, fun n => ⟨h.2 (NE n), h.2 (NF n)⟩⟩)
    (fun AB => aux_thm_prop_lc_normpair AB.1 AB.2)
    (aux_thm_prop_lc_normpair_measurable measurable_fst measurable_snd) S hS
    (fun A B t ht => aux_thm_prop_lc_normpair_smul t ht A B) hNS

end Cell
end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
section Cell

variable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hIR : InfraredCharacterization model H)
    (zcell : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell r hr),
      ‖(u : SobolevData (centeredCube zcell r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) u‖)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (hfield : Measurable field) (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (NE NF : ℕ → ℕ) (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymE : ∀ om, (AE om).transpose = AE om)
    (hsymF : ∀ om, (AF om).transpose = AF om)
    (hAE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zcell r hr NE hP (AE om))
    (hAF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zcell r hr NF hP (AF om))

include hIR hfield hlaw hsymE hsymF hAE hAF

theorem aux_thm_prop_lc_one_cell_refl_law (a : Fin d) :
    P.map (fun om => aux_thm_prop_lc_normpair (AE om) (AF om)) =
      P.map (fun om => aux_thm_prop_lc_reflpair a (aux_thm_prop_lc_normpair (AE om) (AF om))) := by
  let R : Homogenization.Mat d := Matrix.diagonal (aux_thm_prop_lc_reflSign a)
  let w := aux_thm_prop_lc_reflShift zcell a
  have hT := aux_thm_prop_lc_field_symmetry_preserving model R
    (aux_thm_prop_lc_refl_isSigned a) w
  have hquad (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
      p ⬝ᵥ ((aux_thm_prop_lc_reflLinear a) A).mulVec p =
        coordinateReflectionDerivative {a} p ⬝ᵥ A.mulVec (coordinateReflectionDerivative {a} p) := by
    have hslope : coordinateReflectionDerivative {a} p =
        (fun i => (if i = a then -(1 : ℝ) else 1) * p i) := by
      funext i
      simp only [coordinateReflectionDerivative_apply, coordinateReflectionSign,
        Finset.mem_singleton]
    rw [hslope]
    exact aux_thm_prop_lc_reflAct_quadForm a A p
  apply aux_thm_prop_lc_one_cell_pair_law model H zcell hr hP hIR.1 P field hfield hlaw
    NE NF AE AF hsymE hsymF hAE hAF (aux_thm_prop_T R w) hT
    (aux_thm_prop_lc_reflLinear a) (fun A hA => aux_thm_prop_lc_reflAct_symm a hA)
    (coordinateReflectionDerivative {a})
    hquad (fun x => Real.exp (-(H x (aux_thm_prop_affineMap R w 0))))
    ?_ (aux_thm_prop_lc_reflpair a)
    (aux_thm_prop_lc_reflpair_measurable measurable_id a)
    (fun A B => aux_thm_prop_lc_normpair_reflAct a A B)
  filter_upwards [hIR.2, hT.quasiMeasurePreserving.ae hIR.2] with x hx hTx
  exact ⟨Real.exp_ne_zero _, fun N p =>
    aux_thm_prop_lc_resp_refl model H zcell hr hP a x
      (aux_thm_prop_H_T R w H x hx hTx) N p⟩

theorem aux_thm_prop_lc_one_cell_swap_law (a b : Fin d) :
    P.map (fun om => aux_thm_prop_lc_normpair (AE om) (AF om)) =
      P.map (fun om => aux_thm_prop_lc_permpair (Equiv.swap a b)
        (aux_thm_prop_lc_normpair (AE om) (AF om))) := by
  let R : Homogenization.Mat d := aux_thm_prop_lc_swapMat a b
  let w := aux_thm_prop_lc_swapShift zcell a b
  have hT := aux_thm_prop_lc_field_symmetry_preserving model R
    (aux_thm_prop_lc_swap_isSigned a b) w
  apply aux_thm_prop_lc_one_cell_pair_law model H zcell hr hP hIR.1 P field hfield hlaw
    NE NF AE AF hsymE hsymF hAE hAF (aux_thm_prop_T R w) hT
    (aux_thm_prop_lc_permLinear (Equiv.swap a b))
    (fun A hA => aux_thm_prop_lc_permAct_symm (Equiv.swap a b) hA)
    (fun p => p ∘ Equiv.swap a b)
    (aux_thm_prop_lc_swapAct_quadForm a b)
    (fun x => Real.exp (-(H x (aux_thm_prop_affineMap R w 0))))
    ?_ (aux_thm_prop_lc_permpair (Equiv.swap a b))
    (aux_thm_prop_lc_permpair_measurable measurable_id (Equiv.swap a b))
    (fun A B => aux_thm_prop_lc_normpair_permAct (Equiv.swap a b) A B)
  filter_upwards [hIR.2, hT.quasiMeasurePreserving.ae hIR.2] with x hx hTx
  exact ⟨Real.exp_ne_zero _, fun N p =>
    aux_thm_prop_lc_resp_swap model H zcell hr hP a b x
      (aux_thm_prop_H_T R w H x hx hTx) N p⟩

/-- Signed-permutation invariance of the actual normalized limiting pair on
one cell. Its hypotheses mention no observation family at other scales. -/
theorem aux_thm_prop_lc_one_cell_laws :
    (∀ a : Fin d, P.map (fun om => aux_thm_prop_lc_normpair (AE om) (AF om)) =
      P.map (fun om => aux_thm_prop_lc_reflpair a (aux_thm_prop_lc_normpair (AE om) (AF om)))) ∧
    (∀ s : Equiv.Perm (Fin d), P.map (fun om => aux_thm_prop_lc_normpair (AE om) (AF om)) =
      P.map (fun om => aux_thm_prop_lc_permpair s (aux_thm_prop_lc_normpair (AE om) (AF om)))) := by
  have hmeasE := aux_thm_prop_matrix_limit_aemeasurable P
    (fun n om p => aux_thm_prop_lc_response model H zcell hr hP (NE n) (field om) p)
    (fun n p => ((aux_thm_prop_affine_response_measurable model H hIR.1 (NE n) zcell hr hP p).div_const _).comp hfield) AE hsymE hAE
  have hmeasF := aux_thm_prop_matrix_limit_aemeasurable P
    (fun n om p => aux_thm_prop_lc_response model H zcell hr hP (NF n) (field om) p)
    (fun n p => ((aux_thm_prop_affine_response_measurable model H hIR.1 (NF n) zcell hr hP p).div_const _).comp hfield) AF hsymF hAF
  have hmatE : AEMeasurable AE P := AEMeasurable.of_eval fun i => AEMeasurable.of_eval (hmeasE i)
  have hmatF : AEMeasurable AF P := AEMeasurable.of_eval fun i => AEMeasurable.of_eval (hmeasF i)
  have hX : AEMeasurable (fun om => aux_thm_prop_lc_normpair (AE om) (AF om)) P :=
    (aux_thm_prop_lc_normpair_measurable measurable_fst measurable_snd).comp_aemeasurable
      (hmatE.prodMk hmatF)
  exact ⟨aux_thm_prop_lc_one_cell_refl_law model H hIR zcell hr hP P field hfield hlaw
      NE NF AE AF hsymE hsymF hAE hAF,
    aux_thm_prop_lc_perm_law_of_swaps P _ hX
      (aux_thm_prop_lc_one_cell_swap_law model H hIR zcell hr hP P field hfield hlaw
        NE NF AE AF hsymE hsymF hAE hAF)⟩

end Cell
end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Complete one-cell matrix concentration assembly. The only quantitative
input is scalar centered and band concentration on the polarization slopes.
Positivity comes from the true Dirichlet responses and centering from the
proved signed-permutation law; neither is an asserted resampling input. -/
theorem aux_thm_prop_one_cell_concentration_of_scalar
    {d : ℕ} (hd : 0 < d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hIR : InfraredCharacterization model H)
    (zcell : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell r hr),
      ‖(u : SobolevData (centeredCube zcell r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) u‖)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (hfield : Measurable field)
    (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (NE NF : ℕ → ℕ) (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymE : ∀ om, (AE om).transpose = AE om)
    (hsymF : ∀ om, (AF om).transpose = AF om)
    (hAE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zcell r hr NE hP (AE om))
    (hAF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zcell r hr NF hP (AF om))
    (m M : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (horder : ∀ᵐ om ∂P, 0 < Matrix.trace (AE om) ∧
      ∀ p : Fin d → ℝ,
        m * (p ⬝ᵥ (AE om).mulVec p) ≤ p ⬝ᵥ (AF om).mulVec p ∧
        p ⬝ᵥ (AF om).mulVec p ≤ M * (p ⬝ᵥ (AE om).mulVec p))
    (Band : ℕ → MeasurableSpace Ω) (p : ℝ) (hp : 1 ≤ p)
    (X0 : ℝ) (X : ℕ → ℝ)
    (hscalar : ∀ c ∈ Icc m M, ∀ v : Fin d → ℝ, aux_thm_prop_lc_slope v →
      eLpNorm (fun om => aux_thm_prop_lc_rel (AE om) (AF om) c v -
        ∫ om', aux_thm_prop_lc_rel (AE om') (AF om') c v ∂P) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal X0 ∧
      ∀ Hb : ℕ,
        eLpNorm (fun om => aux_thm_prop_lc_rel (AE om) (AF om) c v -
          (P[fun om' => aux_thm_prop_lc_rel (AE om') (AF om') c v | Band Hb]) om)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (X Hb)) :
    let ck : ℝ := ∫ om, Matrix.trace (AF om) / Matrix.trace (AE om) ∂P
    let B : Ω → Matrix (Fin d) (Fin d) ℝ := fun om =>
      (Matrix.trace (AE om))⁻¹ • (AF om - ck • AE om)
    ck ∈ Icc m M ∧
      (∀ i j : Fin d, ∫ om, B om i j ∂P = 0) ∧
      (eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B om i j|)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (3 * ((d : ℝ) * d) * X0)) ∧
      (∀ Hb : ℕ,
        eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
          |B om i j - (P[fun om' => B om' i j | Band Hb]) om|)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (3 * ((d : ℝ) * d) * X Hb)) := by
  have hmeas (N : ℕ) (v : Fin d → ℝ) :
      Measurable (fun om => aux_thm_prop_lc_response model H zcell hr hP N (field om) v) :=
    ((aux_thm_prop_affine_response_measurable model H hIR.1 N zcell hr hP v).div_const _).comp hfield
  have hmE (v : Fin d → ℝ) : AEStronglyMeasurable (fun om => v ⬝ᵥ (AE om).mulVec v) P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hmeas (NE n) v).aestronglyMeasurable) (hAE.mono fun om h => h v)
  have hmF (v : Fin d → ℝ) : AEStronglyMeasurable (fun om => v ⬝ᵥ (AF om).mulVec v) P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hmeas (NF n) v).aestronglyMeasurable) (hAF.mono fun om h => h v)
  have hpsd : ∀ᵐ om ∂P, ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (AE om).mulVec v := by
    filter_upwards [hAE] with om h v
    apply ge_of_tendsto (h v)
    exact Eventually.of_forall fun n =>
      div_nonneg (dirichletResponse_nonneg _ _ _) ENNReal.toReal_nonneg
  have hlaws := aux_thm_prop_lc_one_cell_laws model H hIR zcell hr hP P field hfield hlaw
    NE NF AE AF hsymE hsymF hAE hAF
  have hout := aux_thm_prop_lc_assemble_generic hd P (fun _ => AE) (fun _ => AF)
    (fun _ => hsymE) (fun _ => hsymF) (fun _ => hmE) (fun _ => hmF)
    (hpsd.mono fun om h _ => h) m M hm hmM (horder.mono fun om h _ => h)
    (fun _ => hlaws) (fun _ => Band) (ENNReal.ofReal p) (ENNReal.ofReal p) le_rfl
    (ENNReal.one_le_ofReal.mpr hp) X0 X (fun c hc _ v hv => hscalar c hc v hv)
  exact ⟨hout.1 0, hout.2.1 0, hout.2.2.1 0, hout.2.2.2 0⟩

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_one_cell_scalar_moments
    {d : ℕ} (hd : 0 < d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hIR : InfraredCharacterization model H)
    (zcell : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell r hr),
      ‖(u : SobolevData (centeredCube zcell r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) u‖)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (hfield : Measurable field)
    (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (NE NF : ℕ → ℕ) (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymE : ∀ om, (AE om).transpose = AE om)
    (hsymF : ∀ om, (AF om).transpose = AF om)
    (hAE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zcell r hr NE hP (AE om))
    (hAF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zcell r hr NF hP (AF om))
    (m M : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (horder : ∀ᵐ om ∂P, 0 < Matrix.trace (AE om) ∧
      ∀ p : Fin d → ℝ,
        m * (p ⬝ᵥ (AE om).mulVec p) ≤ p ⬝ᵥ (AF om).mulVec p ∧
        p ⬝ᵥ (AF om).mulVec p ≤ M * (p ⬝ᵥ (AE om).mulVec p))
    (Band : ℕ → MeasurableSpace Ω) (p : ℝ) (hp : 1 ≤ p)
    (Cp delta gap aexp : ℝ)
    (hscalar : ∀ c ∈ Icc m M, ∀ v : Fin d → ℝ, aux_thm_prop_lc_slope v →
      eLpNorm (fun om => aux_thm_prop_lc_rel (AE om) (AF om) c v -
        ∫ om', aux_thm_prop_lc_rel (AE om') (AF om') c v ∂P) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * delta * gap) ∧
      ∀ Hb : ℕ,
        eLpNorm (fun om => aux_thm_prop_lc_rel (AE om) (AF om) c v -
          (P[fun om' => aux_thm_prop_lc_rel (AE om') (AF om') c v | Band Hb]) om)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cp * delta * gap * (3 : ℝ) ^ (-aexp * (Hb : ℝ))))
    (ck : ℝ) (hexp : (∫ om, Matrix.trace (AF om) / Matrix.trace (AE om) ∂P) = ck) :
    let B : Ω → Matrix (Fin d) (Fin d) ℝ := fun om =>
      (Matrix.trace (AE om))⁻¹ • (AF om - ck • AE om)
    (eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B om i j|)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal ((3 * ((d : ℝ) * d) * Cp) * delta * gap)) ∧
    (∀ Hb : ℕ,
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
        |B om i j - (P[fun om' => B om' i j | Band Hb]) om|)
        (ENNReal.ofReal p) P ≤ ENNReal.ofReal
          ((3 * ((d : ℝ) * d) * Cp) * delta * gap * (3 : ℝ) ^ (-aexp * (Hb : ℝ)))) := by
  have hout := aux_thm_prop_one_cell_concentration_of_scalar hd model H hIR zcell hr hP
    P field hfield hlaw NE NF AE AF hsymE hsymF hAE hAF m M hm hmM horder Band p hp
    (Cp * delta * gap) (fun Hb => Cp * delta * gap * (3 : ℝ) ^ (-aexp * (Hb : ℝ))) hscalar
  dsimp only at hout
  rw [hexp] at hout
  exact ⟨by simpa only [mul_assoc] using hout.2.2.1,
    fun Hb => by simpa only [mul_assoc] using hout.2.2.2 Hb⟩

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper

/-- Proposed local scalar resampling supplier, the two quantitative estimates
from the relative concentration estimate of the paper. The matrix law, centering, positivity, and all
fine-cell selection steps are proved separately. This definition asserts no
existence theorem and is not a new principal premise. -/
def aux_thm_prop_local_relative_input
    (d : ℕ) (I : _root_.SubdiffusiveProcess.Paper.in_J d) (C0 p delta0 Cp aexp : ℝ) : Prop :=
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr
          Sspace GN GE GF NE NF)
        (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
        (horder : ∀ᵐ omega ∂P, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
                m * (limitFormEnergy (GE i omega) u).toReal ≤
                    (limitFormEnergy (GF i omega) u).toReal ∧
                  (limitFormEnergy (GF i omega) u).toReal ≤
                    M * (limitFormEnergy (GE i omega) u).toReal)
        (zcell : SpatialCoordinates d) (k : ℕ)
        (cellIdx : ℕ)
        (hcell : z cellIdx = zcell ∧
          r cellIdx = (3 : ℝ) ^ (-(k : ℝ)))
        (paddedIdx : ℕ)
        (hpaddedIdx :
          z paddedIdx = zcell ∧
          r paddedIdx = 3 * ((3 : ℝ) ^ (-(k : ℝ))))
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hsymAE : ∀ omega, (AE omega).transpose = AE omega)
        (hsymAF : ∀ omega, (AF omega).transpose = AF omega)
        (hAE : ∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity))
                hPk
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega)
                  (NE j) zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AE omega).mulVec pvec)))
        (hAF : ∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity))
                hPk
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega)
                  (NF j) zcell
                  (show 0 < (3 : ℝ) ^ (-(k : ℝ)) by positivity)) pvec /
                (volume
                  (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                    (by positivity) : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AF omega).mulVec pvec))),
      ∀ c ∈ Icc m M, ∀ pvec : Fin d → ℝ,
        ((∃ i : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∨
          (∃ i j : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ) +
            (Pi.single j (1 : ℝ) : Fin d → ℝ))) →
      let R : Ω → ℝ := fun om =>
        (pvec ⬝ᵥ (AF om).mulVec pvec - c * (pvec ⬝ᵥ (AE om).mulVec pvec)) /
          Matrix.trace (AE om)
      let Band : ℕ → MeasurableSpace Ω := fun Hband =>
        ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (Hband : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun om : Ω => field om j)
      (eLpNorm (fun om => R om - ∫ om', R om' ∂P) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * model.delta * (M - m))) ∧
      ∀ Hband : ℕ,
        eLpNorm (fun om => R om - (P[R | Band Hband]) om) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * model.delta * (M - m) *
            (3 : ℝ) ^ (-aexp * (Hband : ℝ)))

/-- Uniform form of the remaining local scalar resampling target. -/
def aux_thm_prop_uniform_local_relative_input
    (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d) : Prop :=
  ∃ aexp : ℝ, 0 < aexp ∧
    ∀ C0 : ℝ, 1 ≤ C0 → ∀ p : ℝ, 2 ≤ p →
      ∃ delta0 Cp : ℝ, 0 < delta0 ∧ 0 < Cp ∧
        (CubeFractionalInterpolationInput d hd →
          aux_thm_prop_local_relative_input d I C0 p delta0 Cp aexp)

end SubdiffusiveProcess.Paper

end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper

/-- Choose the moment order after the geometric subdivision, and before the
model or endpoint gap. This uses exactly the proposed uniform local supplier. -/
theorem aux_thm_prop_local_relative_parameters
    (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (hinput : aux_thm_prop_uniform_local_relative_input d hd I)
    (C0 : ℝ) (hC0 : 1 ≤ C0) (H1 : ℕ) (theta : ℝ) :
    ∃ p aexp Cp delta0 : ℝ,
      2 ≤ p ∧ 0 < aexp ∧ 0 < Cp ∧ 0 < delta0 ∧
      2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3 ∧
      (CubeFractionalInterpolationInput d hd →
        aux_thm_prop_local_relative_input d I C0 p delta0 Cp aexp) := by
  obtain ⟨aexp, haexp, hsupplier⟩ := hinput
  let A : ℝ := 2 * Real.log 2 + 1 + (48 / theta) *
    (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)
  let p : ℝ := max 2 (2 * A / (aexp * Real.log 3))
  have hp : 2 ≤ p := le_max_left _ _
  have ha : 0 < aexp * Real.log 3 := mul_pos haexp (Real.log_pos (by norm_num))
  have hrate : 2 * A ≤ p * aexp * Real.log 3 := by
    have h := (div_le_iff₀ ha).mp (le_max_right 2 (2 * A / (aexp * Real.log 3)))
    exact h.trans_eq (mul_assoc p aexp (Real.log 3)).symm
  obtain ⟨delta0, Cp, hdelta0, hCp, hconc⟩ := hsupplier C0 hC0 p hp
  exact ⟨p, aexp, Cp, delta0, hp, haexp, hCp, hdelta0, hrate, hconc⟩

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_local_relative_specialize
    (d : ℕ) (_hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (C0 p delta0 Cp aexp : ℝ) (_hC0 : 1 ≤ C0) (_hp : 2 ≤ p)
    (hsupplier : aux_thm_prop_local_relative_input d I C0 p delta0 Cp aexp)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (hmodel : model.delta ≤ delta0)
    (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
    (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (zc : SpatialCoordinates d) (k jC jP : ℕ)
    (hzc : z jC = zc) (hrc : r jC = (3 : ℝ) ^ (-(k : ℝ)))
    (hzp : z jP = zc) (hrp : r jP = 3 * (3 : ℝ) ^ (-(k : ℝ)))
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube zc ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
      ‖(u : SobolevData (centeredCube zc ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube zc ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymE : ∀ om, (AE om).transpose = AE om)
    (hsymF : ∀ om, (AF om).transpose = AF om)
    (hE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zc
      ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) NE hPk (AE om))
    (hF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zc
      ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) NF hPk (AF om))
    :
    ∀ c ∈ Icc m M, ∀ v : Fin d → ℝ, aux_thm_prop_lc_slope v →
      eLpNorm (fun om => aux_thm_prop_lc_rel (AE om) (AF om) c v -
        ∫ om', aux_thm_prop_lc_rel (AE om') (AF om') c v ∂P) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * model.delta * (M - m)) ∧
      ∀ Hb : ℕ,
        eLpNorm (fun om => aux_thm_prop_lc_rel (AE om) (AF om) c v -
          (P[fun om' => aux_thm_prop_lc_rel (AE om') (AF om') c v |
            aux_thm_prop_scale_band field k Hb]) om)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal
            (Cp * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (Hb : ℝ))) := by
  exact hsupplier model hmodel Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF
    hJoint m M hm hmM hM horder zc k jC ⟨hzc, hrc⟩ jP ⟨hzp, hrp⟩ hPk
    AE AF hsymE hsymF hE hF

end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_local_relative_one_cell
    (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (C0 p delta0 Cp aexp : ℝ) (hC0 : 1 ≤ C0) (hp : 2 ≤ p)
    (hsupplier : aux_thm_prop_local_relative_input d I C0 p delta0 Cp aexp)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (hmodel : model.delta ≤ delta0)
    (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
    (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (zc : SpatialCoordinates d) (k jC jP : ℕ)
    (hzc : z jC = zc) (hrc : r jC = (3 : ℝ) ^ (-(k : ℝ)))
    (hzp : z jP = zc) (hrp : r jP = 3 * (3 : ℝ) ^ (-(k : ℝ)))
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube zc ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
      ‖(u : SobolevData (centeredCube zc ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube zc ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymE : ∀ om, (AE om).transpose = AE om)
    (hsymF : ∀ om, (AF om).transpose = AF om)
    (hE : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zc
      ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) NE hPk (AE om))
    (hF : ∀ᵐ om ∂P, aux_thm_prop_affine_converges model H (field om) zc
      ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) NF hPk (AF om))
    (hmatrixOrder : ∀ᵐ om ∂P, 0 < Matrix.trace (AE om) ∧
      ∀ pvec : Fin d → ℝ,
        m * (pvec ⬝ᵥ (AE om).mulVec pvec) ≤ pvec ⬝ᵥ (AF om).mulVec pvec ∧
        pvec ⬝ᵥ (AF om).mulVec pvec ≤ M * (pvec ⬝ᵥ (AE om).mulVec pvec))
    (ck : ℝ) (hexp : (∫ om, Matrix.trace (AF om) / Matrix.trace (AE om) ∂P) = ck) :
    let B : Ω → Matrix (Fin d) (Fin d) ℝ := fun om =>
      (Matrix.trace (AE om))⁻¹ • (AF om - ck • AE om)
    (eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d, |B om i j|)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal ((3 * ((d : ℝ) * d) * Cp) * model.delta * (M - m))) ∧
    (∀ Hb : ℕ,
      eLpNorm (fun om => ∑ i : Fin d, ∑ j : Fin d,
        |B om i j - (P[fun om' => B om' i j | aux_thm_prop_scale_band field k Hb]) om|)
        (ENNReal.ofReal p) P ≤ ENNReal.ofReal
          ((3 * ((d : ℝ) * d) * Cp) * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (Hb : ℝ)))) := by
  have : IsProbabilityMeasure P := hJoint.1
  have hscalar := aux_thm_prop_local_relative_specialize d hd I C0 p delta0 Cp aexp hC0 hp
    hsupplier model hmodel Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF
    hJoint m M hm hmM hM horder zc k jC jP hzc hrc hzp hrp hPk AE AF hsymE hsymF hE hF
  have hm0 : 0 ≤ m := (inv_nonneg.mpr (zero_le_one.trans hC0)).trans hm
  have hIR : InfraredCharacterization model H := hJoint.2.2.2.1
  have hmeas : Measurable field := hJoint.2.1
  have hlaw : P.map field = (chaosSampleLaw model).toMeasure := hJoint.2.2.1
  clear hsupplier hJoint horder hmodel Rm It Sreg GN GE GF Sspace hzc hrc hzp hrp z r hr
  clear jC jP hm hM hC0 delta0 C0 I
  -- Pin the radius positivity before the dependent Poincaré argument.
  -- An inline positivity proof forces expensive cube/Lp unification here.
  have hpos : 0 < (3 : ℝ) ^ (-(k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hdpos : 0 < d := Nat.lt_of_lt_of_le (by decide : 0 < 2) hd
  have hbase := aux_thm_prop_one_cell_scalar_moments (d := d) (Ω := Ω)
    (r := (3 : ℝ) ^ (-(k : ℝ)))
    hdpos model H hIR zc hpos hPk
  have hmat := hbase P field hmeas hlaw NE NF AE AF hsymE hsymF hE hF
  have hbound := hmat m M hm0 hmM hmatrixOrder (aux_thm_prop_scale_band field k) p
    (le_trans one_le_two hp) Cp model.delta (M - m) aexp
  have hout := hbound (fun c hc v hv => hscalar c hc v hv) ck hexp
  exact hout


end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Specialize a one-cell concentration supplier to the actual measurable
matrix bank and the deterministic catalogue selection. No outside-root index
and no artificial matrix is used on an eligible cell. -/
theorem aux_thm_prop_cell_moments_of_local_relative
    (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (C0 p delta0 Cp aexp : ℝ) (hC0 : 1 ≤ C0) (hp : 2 ≤ p)
    (hsupplier : aux_thm_prop_local_relative_input d I C0 p delta0 Cp aexp)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (hmodel : model.delta ≤ delta0)
    (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
    (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (m M : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (prepared : aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF m M)
    (H1 : ℕ) :
    aux_thm_prop_cell_matrix_moments P field z r prepared.AE prepared.AF prepared.ck H1 p
      ((3 * ((d : ℝ) * d) * Cp) * model.delta * (M - m)) aexp := by
  have : IsProbabilityMeasure P := hJoint.1
  apply aux_thm_prop_cell_moments_mask
  intro n zc havail
  let jC := (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).1
  let jP := (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side H1 n)).2
  have hspec := aux_thm_prop_cell_index_spec z r zc (aux_thm_prop_mass_side H1 n) havail
  have hzc : z jC = zc := hspec.1
  have hzp : z jP = zc := hspec.2.2.1
  have hrc : r jC = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) :=
    hspec.2.1.trans (aux_thm_prop_mass_side_rpow H1 n)
  have hrp : r jP = 3 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) :=
    hspec.2.2.2.trans (congrArg (3 * ·) (aux_thm_prop_mass_side_rpow H1 n))
  have hQ : centeredCube (z jC) (r jC) (hr jC) =
      centeredCube zc ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity) := by
    apply TopologicalSpace.Opens.ext
    change Metric.ball (z jC) (r jC / 2) =
      Metric.ball zc (((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) / 2)
    rw [hzc, hrc]
  have hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube zc ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity)),
      ‖(u : SobolevData (centeredCube zc ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube zc ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity))) u‖ := by
    have hp := prepared.hP jC
    rw [hQ] at hp
    exact hp
  have hE : ∀ᵐ om ∂P,
      aux_thm_prop_affine_converges model H (field om) zc
        ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity) NE hPk (prepared.AE jC om) := by
    filter_upwards [prepared.converges] with om h
    simpa only [hzc, hrc] using (h jC).1
  have hF : ∀ᵐ om ∂P,
      aux_thm_prop_affine_converges model H (field om) zc
        ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (by positivity) NF hPk (prepared.AF jC om) := by
    filter_upwards [prepared.converges] with om h
    simpa only [hzc, hrc] using (h jC).2
  have hpc : r jP = 3 * r jC := by rw [hrp, hrc]
  have hmatrixOrder : ∀ᵐ om ∂P, 0 < Matrix.trace (prepared.AE jC om) ∧
      ∀ pvec : Fin d → ℝ,
        m * (pvec ⬝ᵥ (prepared.AE jC om).mulVec pvec) ≤
          pvec ⬝ᵥ (prepared.AF jC om).mulVec pvec ∧
        pvec ⬝ᵥ (prepared.AF jC om).mulVec pvec ≤
          M * (pvec ⬝ᵥ (prepared.AE jC om).mulVec pvec) := by
    filter_upwards [prepared.trace_positive, prepared.order] with om ht ho
    exact ⟨(ht jC).1, ho jP jC (hzc.trans hzp.symm) hpc⟩
  exact aux_thm_prop_local_relative_one_cell d hd I C0 p delta0 Cp aexp hC0 hp hsupplier
    model hmodel Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF hJoint m M hm hmM hM horder
    zc (H1 * n) jC jP hzc hrc hzp hrp hPk
    (prepared.AE jC) (prepared.AF jC) (prepared.symmetricE jC) (prepared.symmetricF jC)
    hE hF hmatrixOrder (prepared.ck (r jC)) (prepared.expected jC)


end SubdiffusiveProcess.Paper


end

noncomputable section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Full fine-cell selection from the two exact local upstream suppliers.
The actual matrices, minima, floors, both density branches, all-chain counts,
and every parameter-order constraint are assembled in the proof. -/
theorem aux_thm_prop_select_from_local_relative
    (d : ℕ) (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (C0 : ℝ) (hC0 : 1 ≤ C0) (Cresp : ℝ)
    (hUniformAffine : aux_thm_prop_uniform_local_affine_input d hd I Cresp)
    (hUniformConcentration : aux_thm_prop_uniform_local_relative_input d hd I) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) →
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) →
        (hRm : Rm.C ≤ Cresp) →
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) →
        (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg) →
        (hBounds : _root_.SubdiffusiveProcess.Paper.aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF) →
        (hEnum : _root_.SubdiffusiveProcess.Paper.in_represented_enum d z r hr) →
        ∀ {beta t : ℝ}, (@aux_thm_prop_catalogue d hd _ _ model H Ω _ P hJoint.1 field z r hr Sspace NE NF
          (aux_thm_prop_alpha d hd) (1 / 128) beta t) →
        (∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega) →
        (∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) →
        ∀ cL cU : ℝ,
          (∀ᵐ omega ∂P, sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = cL ∧
            sInf (aux_thm_prop_upperSet z r hr GE GF omega) = cU) →
          cL < cU →
          aux_thm_prop_selection_data d hd model H Ω P field z r hr Sspace GE GF NE NF cL cU →
          aux_thm_prop_fine_candidates (model := model) (H := H) (P := P)
            (field := field) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
            (GE := GE) (GF := GF) (NE := NE) (NF := NF) hd cL cU ∨
          aux_thm_prop_fine_candidates (model := model) (H := H) (P := P)
            (field := field) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
            (GE := GF) (GF := GE) (NE := NF) (NF := NE) hd cU⁻¹ cL⁻¹ := by
  obtain ⟨g, c0, deltaA, hc0, hdeltaA, hAffine⟩ := hUniformAffine
  obtain ⟨p, aexp, Cp, deltaC, hp, haexp, hCp, hdeltaC, hRate, hConc⟩ :=
    aux_thm_prop_local_relative_parameters d hd I hUniformConcentration
      C0 hC0 g.H1 (1 / 32)
  have hp0 : 0 < p := (by norm_num : (0 : ℝ) < 2).trans_le hp
  let Cmat : ℝ := 3 * ((d : ℝ) * d) * Cp
  have hCmat : 0 < Cmat := by
    have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    exact mul_pos (mul_pos (by norm_num) (mul_pos hd0 hd0)) hCp
  obtain ⟨deltaCount, hdeltaCount, hCount⟩ := aux_thm_prop_matrix_mass_counts
    d hd g c0 hc0 p hp0 Cmat hCmat aexp haexp hRate
  refine ⟨min deltaA (min deltaC deltaCount), lt_min hdeltaA (lt_min hdeltaC hdeltaCount), ?_⟩
  intro _ _ model hmodel H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint
    Rm hRm Sreg It hBounds hEnum beta t hCat hcomp hnz m M hdet hlt prepared
  have : IsProbabilityMeasure P := hJoint.1
  have hmodelA : model.delta ≤ deltaA := hmodel.trans (min_le_left _ _)
  have hmodelC : model.delta ≤ deltaC :=
    hmodel.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmodelCount : model.delta ≤ deltaCount :=
    hmodel.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨affine⟩ := hAffine model hmodelA H Ω P field z r hr Sspace GN GE GF NE NF hJoint
    Rm hRm Sreg It hBounds hEnum hCat m M prepared
  have hopt := aux_thm_prop_endpoint_order hd C0 hC0 m M hcomp hnz hdet
  obtain ⟨om, hb⟩ := hopt.exists
  have hm : 0 < m := (inv_pos.mpr (zero_lt_one.trans_le hC0)).trans_le hb.1
  have hM : 0 < M := hm.trans hlt
  have horder := hopt.mono fun _ h => h.2.2.2
  have hInterp := aux_thm_prop_interpolation_of_joint_bounds hd hJoint hBounds
  have hmom := aux_thm_prop_cell_moments_of_local_relative d hd I C0 p deltaC Cp aexp hC0 hp
    (hConc hInterp) model hmodelC Rm Sreg It H Ω P field z r hr Sspace GN GE GF NE NF hJoint
    m M hb.1 hlt.le hb.2.2.1 horder prepared g.H1
  have hbad := hCount model hmodelCount Ω P field hJoint.2.1 hJoint.2.2.1 z r hr
    prepared.AE prepared.AF prepared.ck prepared.measurableE prepared.measurableF
    m M hlt.le affine.Good affine.chain hmom
  exact aux_thm_prop_fine_dichotomy_from_local_estimates prepared g c0 hc0 hlt.le affine
    hm hM horder hbad

end SubdiffusiveProcess.Paper


end


end
