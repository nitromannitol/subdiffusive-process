module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Analysis.Matrix.Normed
public import SubdiffusiveProcess.ResponseMoments.RelativeConcentration
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import Mathlib.Probability.ProductMeasure
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import SubdiffusiveProcess.EllipticRegularity.Scaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import SubdiffusiveProcess.Sobolev.DomainPoincare

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise ContDiff Distributions

noncomputable section
namespace SubdiffusiveProcess
namespace CellSymmetry

theorem cs_matrix_polarization {d : ℕ}
    (A : Fin d → Fin d → ℝ) (hA : ∀ i j, A i j = A j i) (i j : Fin d) :
    ((∑ k : Fin d, ∑ l : Fin d,
        A k l * ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) k * ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) l) -
      (∑ k : Fin d, ∑ l : Fin d, A k l * (Pi.single i (1 : ℝ) : Fin d → ℝ) k * (Pi.single i (1 : ℝ) : Fin d → ℝ) l) -
      (∑ k : Fin d, ∑ l : Fin d, A k l * (Pi.single j (1 : ℝ) : Fin d → ℝ) k * (Pi.single j (1 : ℝ) : Fin d → ℝ) l)) / 2 = A i j := by
  classical
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hA j i]
  ring

/-- The normalized affine response limit on one actual represented cube. -/
def cs_affine_converges
    {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ → ℕ)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ p : Fin d → ℝ, Tendsto (fun n =>
    affineDirichletResponse (centeredCube_isBounded z hr) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) p /
      (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
    atTop (𝓝 (p ⬝ᵥ A.mulVec p))

/-- The logarithm of the cutoff coefficient as one global continuous function. -/
def cs_affine_logpot {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) -
      ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) + H om +
    ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i))

theorem cs_affine_logpot_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) :
    Measurable (cs_affine_logpot model H N) :=
  (measurable_const.add hH).add
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i)))

theorem cs_affine_log_eq {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    continuousPositiveLog (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM model H om N z hr)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos model H om N z hr) -
      ContinuousMap.const _ (Real.log 1) =
    (cs_affine_logpot model H N om).restrict
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  rw [Real.log_one, ContinuousMap.const_zero, sub_zero]
  ext x
  show Real.log (cutoffCoefficient model H om N (x : SpatialCoordinates d)) =
    cs_affine_logpot model H N om (x : SpatialCoordinates d)
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N).ne')
    (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  simp only [cs_affine_logpot, cutoffPotential, ContinuousMap.add_apply,
    ContinuousMap.const_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  ring

/-- Measurability of the cutoff affine response in the field. -/
theorem cs_affine_response_measurable {d : ℕ}
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
    (cs_affine_logpot_measurable model H hH N)
  convert hD using 1
  funext om
  simp only [Function.comp_apply]
  unfold affineDirichletResponse _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
    normalizedContinuousPositiveCoefficient
  rw [cs_affine_log_eq]

theorem cs_matrix_quadratic_eq {d : ℕ}
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
theorem cs_matrix_limit_aemeasurable
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
    simp only [cs_matrix_quadratic_eq]
    exact cs_matrix_polarization (A om)
      (fun k l => (congrFun (congrFun (hsym om) k) l).symm) i j
  rwa [heq] at h

section
variable {d : ℕ}

/-- The affine map `y ↦ R y + w`. -/
def cs_affineMap (R : Homogenization.Mat d) (w : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun y => matVecMul R y + w, by
    refine Continuous.add ?_ continuous_const
    exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_apply j)⟩

theorem cs_affineMap_apply (R : Homogenization.Mat d) (w y : SpatialCoordinates d) :
    cs_affineMap R w y = matVecMul R y + w := rfl

/-- Precomposition of a continuous field by the affine map. -/
def cs_precomp (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (g : C(SpatialCoordinates d, ℝ)) : C(SpatialCoordinates d, ℝ) :=
  g.comp (cs_affineMap R w)

theorem cs_precomp_continuous (R : Homogenization.Mat d) (w : SpatialCoordinates d) :
    Continuous (cs_precomp R w) :=
  ContinuousMap.continuous_precomp (cs_affineMap R w)

theorem cs_matVecMul_smul (R : Homogenization.Mat d) (c : ℝ) (y : SpatialCoordinates d) :
    matVecMul R (c • y) = c • matVecMul R y := by
  funext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end

section
variable {d : ℕ}
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem cs_precomp_measurable (R : Homogenization.Mat d) (w : SpatialCoordinates d) :
    Measurable (cs_precomp R w) :=
  (cs_precomp_continuous R w).measurable

/-- The root field law is invariant under every affine signed coordinate permutation. -/
theorem cs_root_invariant (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R) (w : SpatialCoordinates d) :
    ((chaosRootFieldLaw M : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
        Measure C(SpatialCoordinates d, ℝ)).map (cs_precomp R w) =
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
  have hcomm : cs_precomp R w ∘ forget =
      forget ∘ (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR ∘
        _root_.SubdiffusiveProcess.Model.PotentialField.translate w) := by
    funext g
    ext y
    rfl
  have hforget : Measurable forget := forget.continuous.measurable
  rw [hroot, Measure.map_map (cs_precomp_measurable R w) hforget, hcomm,
    ← Measure.map_map hforget
      ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR).comp
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate w)),
    ← Measure.map_map (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR)
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate w), hstat, hrot]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Layer scaling intertwines the affine map with the rescaled translation part. -/
theorem cs_precomp_layerScaling (R : Homogenization.Mat d) (w : SpatialCoordinates d) (j : ℤ) :
    cs_precomp R w ∘ layerScaling d j =
      layerScaling d j ∘ cs_precomp R (((3 : ℝ) ^ (-j)) • w) := by
  funext g
  ext y
  simp only [Function.comp_apply, cs_precomp, ContinuousMap.comp_apply,
    cs_affineMap_apply, layerScaling, ContinuousMap.compRightContinuousMap_apply,
    ContinuousMap.coe_mk]
  congr 1
  rw [smul_add, cs_matVecMul_smul]

theorem cs_layer_invariant (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R) (w : SpatialCoordinates d) (j : ℤ) :
    ((scaledLayerLaw d (chaosRootFieldLaw M) j : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
        Measure C(SpatialCoordinates d, ℝ)).map (cs_precomp R w) =
      (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ)) := by
  have hS : Measurable (layerScaling d j) := (layerScaling d j).continuous.measurable
  simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (cs_precomp_measurable R w) hS,
    cs_precomp_layerScaling,
    ← Measure.map_map hS (cs_precomp_measurable R _),
    cs_root_invariant M R hR]

/-- The chaos sample law is invariant under composing every layer with the affine map. -/
theorem cs_chaos_invariant (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R) (w : SpatialCoordinates d) :
    ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)).map
        (fun x : BilateralField d => fun j => cs_precomp R w (x j)) =
      (chaosSampleLaw M : Measure (BilateralField d)) := by
  change (Measure.infinitePi (fun j : ℤ =>
      ((scaledLayerLaw d (chaosRootFieldLaw M) j : ProbabilityMeasure _) :
        Measure C(SpatialCoordinates d, ℝ)))).map
      (fun x : BilateralField d => fun j => cs_precomp R w (x j)) =
    Measure.infinitePi (fun j : ℤ =>
      ((scaledLayerLaw d (chaosRootFieldLaw M) j : ProbabilityMeasure _) :
        Measure C(SpatialCoordinates d, ℝ)))
  rw [Measure.infinitePi_map_pi _ (fun _ => cs_precomp_measurable R w)]
  congr 1
  funext j
  exact cs_layer_invariant M R hR w j

end

section
variable {d : ℕ}

def cs_T (R : Homogenization.Mat d) (w : SpatialCoordinates d) (x : BilateralField d) :
    BilateralField d :=
  fun j => cs_precomp R w (x j)

/-- The anchored-gauge transform of the infrared field. -/
def cs_gauge (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (h : C(SpatialCoordinates d, ℝ)) : C(SpatialCoordinates d, ℝ) :=
  cs_precomp R w h - ContinuousMap.const _ (h (cs_affineMap R w 0))

theorem cs_gauge_continuous (R : Homogenization.Mat d) (w : SpatialCoordinates d) :
    Continuous (cs_gauge R w) := by
  refine (cs_precomp_continuous R w).sub ?_
  exact ContinuousMap.const'.continuous.comp (continuous_eval_const _)

theorem cs_infraredPartialSum_T (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (x : BilateralField d) (L : ℕ) :
    infraredPartialSum (cs_T R w x) L =
      cs_gauge R w (infraredPartialSum x L) := by
  ext y
  simp only [infraredPartialSum, cs_gauge, cs_T, cs_precomp,
    ContinuousMap.sub_apply, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.coe_sub, Pi.sub_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- The infrared field transforms with the anchored gauge wherever both partial-sum
limits exist. -/
theorem cs_H_T (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x : BilateralField d)
    (hx : Tendsto (infraredPartialSum x) atTop (𝓝 (H x)))
    (hTx : Tendsto (infraredPartialSum (cs_T R w x)) atTop
      (𝓝 (H (cs_T R w x)))) :
    H (cs_T R w x) = cs_gauge R w (H x) := by
  have h2 : Tendsto (infraredPartialSum (cs_T R w x)) atTop
      (𝓝 (cs_gauge R w (H x))) := by
    have := ((cs_gauge_continuous R w).tendsto (H x)).comp hx
    refine this.congr fun L => ?_
    simp only [Function.comp_apply, cs_infraredPartialSum_T]
  exact tendsto_nhds_unique hTx h2

/-- The cutoff coefficient transforms by the gauge constant. -/
theorem cs_cutoffCoefficient_T (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Homogenization.Mat d) (w : SpatialCoordinates d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x : BilateralField d)
    (hH : H (cs_T R w x) = cs_gauge R w (H x)) (N : ℕ)
    (y : SpatialCoordinates d) :
    cutoffCoefficient model H (cs_T R w x) N y =
      Real.exp (-(H x (cs_affineMap R w 0))) *
        cutoffCoefficient model H x N (cs_affineMap R w y) := by
  simp only [cutoffCoefficient, cutoffPotential, hH, cs_gauge, cs_T,
    cs_precomp, ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end
end CellSymmetry
end SubdiffusiveProcess
