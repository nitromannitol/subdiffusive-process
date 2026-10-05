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
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
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

public import SubdiffusiveProcess.Paper.Support.ThmPropBasePart01

@[expose] public section

/-!
Proof support for SubdiffusiveProcess.Paper.thm_prop_base, part 2.
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

namespace SubdiffusiveProcess.Paper

/-- The three variational facts needed for local coefficient comparison. -/
structure aux_thm_prop_mosco_data
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) : Prop where
  symmetric : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y)
  lower : ∀ (wN : ℕ → S.space) (w : DomainL2 Q),
    (∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
    limitFormEnergy G w ≤
      liminf (fun n => (responseForm S (a n) (wN n) (wN n) : EReal)) atTop
  recovery : ∀ u ∈ limitFormDomain G, ∃ w : ℕ → S.space,
    Tendsto (fun n => ((w n).val.1,
      (responseForm S (a n) (w n) (w n) : EReal))) atTop
      (𝓝 (u, limitFormEnergy G u))

/-- The established killed-inverse theorem applies to each weighted norm limit. -/
theorem aux_thm_prop_controlled_mosco
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G)) :
    aux_thm_prop_mosco_data (centeredCube z r hr) S a G := by
  let EN : ℕ → DomainL2 (centeredCube z r hr) → EReal := fun n u =>
    sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧ e = (responseForm S (a n) w w : EReal)}
  have hResult := killed_inverse_mosco d hd z r hr S hS a GN hGN A.interpolation
    A.K A.K_pos A.coercive A.sources A.sources_countable A.sources_dense A.sources_smooth
    (fun f => aux_thm_prop_response_cauchy GN G hConv f.val) EN (fun _ _ => rfl)
  have hG := aux_thm_prop_property_of_limit GN G hConv _ (fun _ h => h.1.1) hResult
  exact ⟨hG.1.2.2.1, aux_prop_killed_inverse_moscoS S a G EN (fun _ _ => rfl) hG.2.1,
    hG.2.2⟩

/-- Reindexing preserves all controls before any compactness extraction. -/
noncomputable def aux_thm_prop_controls_reindex
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a) (sigma : ℕ → ℕ) :
    aux_thm_prop_analytic_controls d hd z r hr S (fun n => a (sigma n)) :=
  aux_thm_prop_analytic_controls_reindex_weight A _ sigma 1 1 zero_lt_one zero_le_one
    (fun _ => Eventually.of_forall fun _ => by rw [one_mul])
    (fun _ => Eventually.of_forall fun _ => by rw [one_mul])

/-- Local recovery passes a coefficient inequality only where the core
representative is supported. Both coefficients may be weighted. -/
theorem aux_thm_prop_controlled_local_form_le
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_thm_prop_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_thm_prop_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) (K : ℝ)
    (hCoeff : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      x ∈ q → (b n).val x ≤ K * (a n).val x) :
    ∀ u, E.MemCoreOn q u → u ∈ EF.domain ∧ EF.form u u ≤ K * E.form u u := by
  intro u hu
  have huG : u ∈ limitFormDomain G :=
    (aux_thm_prop_domain_eq_of_energy E G hE) ▸ hu.mem_domain
  obtain ⟨_huE, uc, huc, hucs, hucq, huae⟩ := hu
  obtain ⟨Y, hY, hYgrad⟩ := aux_thm_prop_localized_recovery_base d hd z r hr S hS a G
    hA.lower hA.recovery (fun _ => A.K) (fun _ => A.K_pos.le) A.K (fun _ => le_rfl)
    (fun w => (A.coercive 0 w).1) (fun n w => (A.coercive n w).2)
    A.interpolation A.t A.t_lower A.t_upper A.cutoffs q hq hqQ u huG uc huc hucs hucq huae
  rw [aux_thm_prop_energy_coe G u huG] at hY
  have hle := aux_thm_prop_energy_order_of_recovery S a b F hB.lower u
    (limitFormEnergy G u).toReal K Y hY (Eventually.of_forall fun n =>
      aux_thm_prop_responseForm_le_local S (a n) (b n) K q (Y n) (hCoeff n) (hYgrad n))
  have huF : u ∈ EF.domain := EF.mem_domain_of_energy_lt_top (by
    rw [hF]
    exact hle.trans_lt (EReal.coe_lt_top _))
  refine ⟨huF, ?_⟩
  rw [← hF, EF.energy_of_mem huF,
    ← aux_thm_prop_form_eq_toReal_energy E G hE u _huE] at hle
  exact EReal.coe_le_coe_iff.mp hle

/-- The actual cutoff argument proves the cube-relative core locality of a
controlled limit, which is the antecedent consumed by stated BD/BDQ. -/
theorem aux_thm_prop_controlled_core_locality
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_thm_prop_mosco_data (centeredCube z r hr) S a G)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∀ u v : DomainL2 (centeredCube z r hr),
      E.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
      E.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → E.form u v = 0 := by
  have hSym : ∀ f g, inner ℝ f (G g) = inner ℝ g (G f) := by
    intro f g
    rw [← hA.symmetric, real_inner_comm]
  exact aux_lem_weighted_cluster_strongly_local d hd z r hr S hS a G hSym
    hA.lower hA.recovery (fun _ => A.K) (fun _ => A.K_pos.le) A.K (fun _ => le_rfl)
    (fun w => (A.coercive 0 w).1) (fun n w => (A.coercive n w).2)
    A.interpolation A.t A.t_lower A.t_upper A.cutoffs E hE

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Compactness gives uniform positive bounds for a weight only assumed
continuous and positive on the closed cube. -/
theorem aux_thm_prop_weight_bounds_on
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        lo ≤ rho x ∧ rho x ≤ hi := by
  have hcompact := lane2_isCompact_closure_centeredCube z hr
  have hne : (closure (centeredCube z r hr : Set (SpatialCoordinates d))).Nonempty :=
    ⟨z, subset_closure (Metric.mem_ball_self (half_pos hr))⟩
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hne hcont
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  exact ⟨rho xmin, rho xmax, hpos xmin hxmin, hpos xmax hxmax, fun x hx => ⟨hmin hx, hmax hx⟩⟩

/-- Global weighted comparison identifies the real form domains and transfers
the actual core to the weighted limit. -/
theorem aux_thm_prop_controlled_weight_core
    {d : ℕ} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_thm_prop_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_thm_prop_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hbounds : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lo ≤ rho x ∧ rho x ≤ hi) :
    E.domain = EF.domain ∧
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF (centeredCube z r hr : Set (SpatialCoordinates d)) C) := by
  have hcmp := aux_lem_weighted_cluster_limit_comparison S a b G F lo hi hlo hhi
    (fun n u => aux_lem_weighted_cluster_rho_form_bounds S (a n) (b n) (a n).val rho
      (EventuallyEq.refl _ _) (hweight n) lo hi hlo hbounds u)
    hA.lower hA.recovery hB.lower hB.recovery
  have hforms := aux_lem_weighted_cluster_forms_of_limit E EF G F hE hF lo hi hcmp.1 hcmp.2
  have hm : (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
      (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
    rw [Measure.restrict_apply' (centeredCube z r hr).isOpen.measurableSet]
    simp
  have hcores := aux_lem_weighted_cluster_core_transfer E EF
    (centeredCube z r hr : Set (SpatialCoordinates d)) (centeredCube z r hr).isOpen hm
    hforms.1 hi (fun u hu => (hforms.2 u hu).2) hcore
  exact ⟨Submodule.ext (fun u => (hforms.1 u).symm), hcores.1⟩

/-- The local coefficient bounds give bounds between the actual energy
measures of the two controlled limits. -/
theorem aux_thm_prop_controlled_weight_local_bounds
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (B : aux_thm_prop_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_thm_prop_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_thm_prop_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hfcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = EF.domain)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EF.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hb : ∀ x ∈ q, lo ≤ rho x ∧ rho x ≤ hi)
    (u : DomainL2 (centeredCube z r hr)) (hu : E.toClosedForm.MemCore u)
    (T : Set (SpatialCoordinates d)) (hTq : T ⊆ q) :
    lo * (Gamma.measure u T).toReal ≤ (GammaF.measure u T).toReal ∧
      (GammaF.measure u T).toReal ≤ hi * (Gamma.measure u T).toReal := by
  apply aux_thm_prop_local_measure_bounds (centeredCube z r hr) E EF hcore hfcore
    hdom Gamma GammaF q hq hqQ lo hi hlo hhi _ _ u hu T hTq
  · intro v hv
    exact (aux_thm_prop_controlled_local_form_le hS A hA hB E.toClosedForm EF.toClosedForm
      hE hF q hq hqQ hi
      (fun n => aux_thm_prop_coefficient_weight_upper _ _ rho (hweight n) q hi
        (fun x hx => (hb x hx).2)) v hv).2
  · intro v hv
    exact (aux_thm_prop_controlled_local_form_le hS B hB hA EF.toClosedForm E.toClosedForm
      hF hE q hq hqQ lo⁻¹
      (fun n => aux_thm_prop_coefficient_weight_lower _ _ rho (hweight n) q lo hlo
        (fun x hx => (hb x hx).1)) v hv).2

/-- The weighted limit energy is identified for every element of the
unweighted domain by the proved catalogue energy-measure theorem. -/
theorem aux_thm_prop_controlled_weight_energy
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (B : aux_thm_prop_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_thm_prop_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_thm_prop_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hfcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = EF.domain)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EF.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    ∀ u ∈ limitFormDomain G, limitFormEnergy F u = (∫ x, rho x ∂(Gamma.measure u) : ℝ) := by
  have hdomA := aux_thm_prop_domain_eq_of_energy E.toClosedForm G hE
  have hdomB := aux_thm_prop_domain_eq_of_energy EF.toClosedForm F hF
  obtain ⟨lo, hi, hlo, _hhi, hb⟩ := aux_thm_prop_weight_bounds_on z r hr rho hcont hpos
  have hmeasure : ∀ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
      (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) → (∃ k : ℤ, rq = (3 : ℝ) ^ k) →
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ u : DomainL2 (centeredCube z r hr), MemFormCore G u →
      ∀ T : Set (SpatialCoordinates d), MeasurableSet T →
        T ⊆ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) →
        sInf (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
            (Gamma.measure u T).toReal ≤ (GammaF.measure u T).toReal ∧
          (GammaF.measure u T).toReal ≤
            sSup (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
              (Gamma.measure u T).toReal := by
    intro zq rq hrq _hRat _hTri hqQ u hu T _hT hTq
    let q : Set (SpatialCoordinates d) := centeredCube zq rq hrq
    have hne : (rho '' q).Nonempty := ⟨rho zq, ⟨zq, Metric.mem_ball_self (half_pos hrq), rfl⟩⟩
    have hbelow : BddBelow (rho '' q) :=
      ⟨lo, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact (hb x (subset_closure (hqQ hx))).1⟩
    have habove : BddAbove (rho '' q) :=
      ⟨hi, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact (hb x (subset_closure (hqQ hx))).2⟩
    have hmin : 0 < sInf (rho '' q) :=
      hlo.trans_le (le_csInf hne (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact (hb x (subset_closure (hqQ hx))).1))
    have hmax : 0 ≤ sSup (rho '' q) :=
      (hpos zq (subset_closure (hqQ (Metric.mem_ball_self (half_pos hrq))))).le.trans
        (le_csSup habove ⟨zq, Metric.mem_ball_self (half_pos hrq), rfl⟩)
    have hucore : E.toClosedForm.MemCore u := by
      obtain ⟨huG, uc, huc, hucs, _hucQ, huae⟩ := hu
      exact ⟨aux_thm_prop_domain_mem_of_energy E.toClosedForm G hE huG,
        uc, huc, hucs, subset_univ _, huae⟩
    exact aux_thm_prop_controlled_weight_local_bounds hS A B hA hB E EF hE hF
      hcore hfcore hdom Gamma GammaF rho hweight q (centeredCube zq rq hrq).isOpen hqQ
      _ _ hmin hmax (fun x hx => ⟨csInf_le hbelow ⟨x, hx, rfl⟩,
        le_csSup habove ⟨x, hx, rfl⟩⟩) u hucore T hTq
  have hid := prop_21_catalog_global_weighted_energy z r hr rfl E.toClosedForm
    EF.toClosedForm G F hE hF Gamma GammaF rho hcont hpos
    (by rw [← hdomA, ← hdomB, hdom])
    (fun u hu => hdom ▸ (aux_thm_prop_domain_mem_of_energy E.toClosedForm G hE hu.1))
    hmeasure (aux_thm_prop_core_dense_of_isCoreOn (centeredCube z r hr) E.toClosedForm G hE hcore)
  intro u hu
  have h := hid u hu
  obtain ⟨C, hC⟩ := hcore
  have hsupp := aux_thm_prop_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC
    (aux_thm_prop_domain_mem_of_energy E.toClosedForm G hE hu)
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)] at h

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- A continuous positive weight on the closed cube gives an actual bounded
positive coefficient when multiplied by any positive coefficient. -/
theorem aux_thm_prop_positive_weight_coefficient
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) :
    ∃ b : PositiveCoefficient (centeredCube z r hr),
      b.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * a.val x := by
  obtain ⟨lo, hi, hlo, _hhi, hb⟩ := aux_thm_prop_weight_bounds_on z r hr rho hcont hpos
  have hm : MemLp rho ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    apply memLp_top_of_bound
      ((hcont.mono subset_closure).aestronglyMeasurable (centeredCube z r hr).isOpen.measurableSet) hi
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (hpos x (subset_closure hx))]
    exact (hb x (subset_closure hx)).2
  have hmprod : MemLp (fun x => rho x * a.val x) ∞
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    hm.fun_mul (Lp.memLp a.val)
  let bval := hmprod.toLp (fun x => rho x * a.val x)
  have hba : (bval : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * a.val x := hmprod.coeFn_toLp
  have hbpos : ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)), c ≤ bval x := by
    obtain ⟨c, hc, hca⟩ := a.property
    refine ⟨lo * c, mul_pos hlo hc, ?_⟩
    filter_upwards [hba, hca,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hbx hax hx
    rw [hbx]
    exact mul_le_mul (hb x (subset_closure hx)).1 hax hc.le
      (hpos x (subset_closure hx)).le
  exact ⟨⟨bval, hbpos⟩, hba⟩

/-- Pointwise weighting identifies the finite-cutoff integral exactly. -/
theorem aux_thm_prop_weighted_response_integral
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : PositiveCoefficient Q) (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x) (w : S.space) :
    responseForm S b w w =
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        (a.val x * ∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2) := by
  rw [← aux_cor_energy_measures_energy_integral S (fun _ => b) 0 w]
  apply integral_congr_ae
  filter_upwards [hweight] with x hx
  rw [hx, mul_assoc]

/-- A lower bound available on a further subsequence of every subsequence
is a lower bound for the full liminf. -/
theorem aux_thm_prop_le_liminf_of_subsubsequence (f : ℕ → EReal) (L : EReal)
    (hsub : ∀ tau : ℕ → ℕ, StrictMono tau → ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      L ≤ liminf (fun n => f (tau (sigma n))) atTop) :
    L ≤ liminf f atTop := by
  apply (le_liminf_iff).mpr
  intro y hy
  by_contra hn
  have hf : ∃ᶠ n in atTop, f n ≤ y := by simpa only [Filter.Frequently, not_le] using hn
  obtain ⟨tau, htau, hftau⟩ := extraction_of_frequently_atTop hf
  obtain ⟨sigma, _hsigma, hL⟩ := hsub tau htau
  have hupper : liminf (fun n => f (tau (sigma n))) atTop ≤ y :=
    liminf_le_of_frequently_le (Frequently.of_forall fun n => hftau (sigma n))
  exact (not_le_of_gt hy) (hL.trans hupper)

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

omit hcontract in
theorem aux_thm_prop_controlled_weighted_identify
    (_hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (B : aux_thm_prop_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_thm_prop_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_thm_prop_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    ∀ u ∈ limitFormDomain G, limitFormEnergy F u = (∫ x, rho x ∂(Gamma.measure u) : ℝ) := by
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := aux_thm_prop_weight_bounds_on z r hr rho hcont hpos
  obtain ⟨hdom, hfcore⟩ := aux_thm_prop_controlled_weight_core hA hB E.toClosedForm EF.toClosedForm
    hE hF hcore rho hweight lo hi hlo hhi.le (fun x hx => hb x (subset_closure hx))
  have hlocal := aux_thm_prop_controlled_core_locality hS B hB EF.toClosedForm hF
  have hstrong := (BD z r hr EF).isStronglyLocal_of_onCore
    (aux_thm_prop_isRegular_of_core (centeredCube z r hr) EF.toClosedForm hfcore)
    (BDQ z r hr EF hfcore hlocal)
  obtain ⟨GammaF, _hsupp⟩ := aux_thm_prop_energy_measure_of_locality z r hr EF
    (EM z r hr EF) hfcore hstrong
  exact aux_thm_prop_controlled_weight_energy hS A B hA hB E EF hE hF
    hcore hfcore hdom Gamma GammaF rho hcont hpos hweight

/-- Weighted compactness and the actual local energy identification prove the
weighted weak lower bound on the full sequence. The three stated standing
inputs produce each cluster's energy measure. -/
theorem aux_thm_prop_controlled_weighted_cluster_lower
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (B : aux_thm_prop_analytic_controls d hd z r hr S b)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)) (hw : w ∈ limitFormDomain G)
    (hWeak : ∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      (∫ x, rho x ∂(Gamma.measure w) : ℝ) ≤
        liminf (fun n => (responseForm S (b (sigma n))
          (wN (sigma n)) (wN (sigma n)) : EReal)) atTop := by
  obtain ⟨F⟩ := aux_thm_prop_form_cluster_exists hS B
    (fun n => hcontract z r hr S hS (b n))
  let A' : aux_thm_prop_analytic_controls d hd z r hr S (fun n => a (F.sigma n)) :=
    aux_thm_prop_controls_reindex A F.sigma
  let B' : aux_thm_prop_analytic_controls d hd z r hr S (fun n => b (F.sigma n)) :=
    aux_thm_prop_controls_reindex B F.sigma
  have hA' := aux_thm_prop_controlled_mosco hS A' (fun n => GN (F.sigma n)) G
    (fun n => hGN (F.sigma n)) (hConv.comp F.sigma_strict.tendsto_atTop)
  have hB' : aux_thm_prop_mosco_data (centeredCube z r hr) S
      (fun n => b (F.sigma n)) F.operator := ⟨F.symmetric, F.lower, F.recovery⟩
  have hid := aux_thm_prop_controlled_weighted_identify BD BDQ EM hcontract hS A' B'
    hA' hB' E F.form hE F.energy_eq hcore Gamma rho hcont hpos
    (fun n => hweight (F.sigma n)) w hw
  refine ⟨F.sigma, F.sigma_strict, ?_⟩
  rw [← hid]
  exact F.lower (fun n => wN (F.sigma n)) w
    (fun f => (hWeak f).comp F.sigma_strict.tendsto_atTop)

theorem aux_thm_prop_controlled_weighted_lower
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)) (hw : w ∈ limitFormDomain G)
    (hWeak : ∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) :
    (∫ x, rho x ∂(Gamma.measure w) : ℝ) ≤
      liminf (fun n => (responseForm S (b n) (wN n) (wN n) : EReal)) atTop := by
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := aux_thm_prop_weight_bounds_on z r hr rho hcont hpos
  have hLower : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo * (a n).val x ≤ (b n).val x := by
    intro n
    filter_upwards [hweight n, aux_prop_locality_recovery_coeff_nonneg (a n),
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hax hxQ
    rw [hx]
    exact mul_le_mul_of_nonneg_right (hb x (subset_closure hxQ)).1 hax
  have hUpper : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (b n).val x ≤ hi * (a n).val x := by
    intro n
    have h := aux_thm_prop_coefficient_weight_upper (a n) (b n) rho (hweight n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) hi
      (fun x hx => (hb x (subset_closure hx)).2)
    filter_upwards [h, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxQ
    exact hx hxQ
  obtain ⟨B⟩ : Nonempty (aux_thm_prop_analytic_controls d hd z r hr S b) :=
    ⟨aux_thm_prop_analytic_controls_reindex_weight A b id lo hi hlo hhi.le hLower hUpper⟩
  apply aux_thm_prop_le_liminf_of_subsubsequence
  intro tau htau
  exact aux_thm_prop_controlled_weighted_cluster_lower BD BDQ EM hcontract hS
    (aux_thm_prop_controls_reindex A tau) (aux_thm_prop_controls_reindex B tau)
    (fun n => GN (tau n)) G (fun n => hGN (tau n)) (hConv.comp htau.tendsto_atTop)
    E hE hcore Gamma rho hcont hpos (fun n => hweight (tau n))
    (fun n => wN (tau n)) w hw (fun f => (hWeak f).comp htau.tendsto_atTop)

/-- The precise weighted lower-cluster input used by cor_energy_measures is
now derived for a controlled operator limit, including arbitrary subsequences. -/
theorem aux_thm_prop_controlled_weighted_input
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm) :
    ∀ rho : SpatialCoordinates d → ℝ,
      ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) →
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)), w ∈ limitFormDomain G →
      (∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x ∂(Gamma.measure w)) : ℝ) : EReal) ≤
        liminf (fun n =>
          (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x *
            ((a (sigma n)).val x * ∑ i : Fin d,
              ((wN (sigma n) : SobolevData (centeredCube z r hr)).2 i x) ^ 2)) : ℝ) : EReal)) atTop := by
  intro rho hcont hpos sigma hsigma wN w hw hweak
  choose b hb using fun n => aux_thm_prop_positive_weight_coefficient z r hr (a n) rho hcont hpos
  have h := aux_thm_prop_controlled_weighted_lower BD BDQ EM hcontract hS
    (aux_thm_prop_controls_reindex A sigma) (fun n => GN (sigma n)) G
    (fun n => hGN (sigma n)) (hConv.comp hsigma.tendsto_atTop) E hE hcore Gamma
    rho hcont hpos (fun n => hb (sigma n)) (fun n => wN (sigma n)) w hw
    (fun f => (hweak f).comp hsigma.tendsto_atTop)
  have hfun : (fun n => (responseForm S (b (sigma n)) (wN (sigma n)) (wN (sigma n)) : EReal)) =
      (fun n => (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x *
        ((a (sigma n)).val x * ∑ i : Fin d,
          ((wN (sigma n) : SobolevData (centeredCube z r hr)).2 i x) ^ 2)) : ℝ) : EReal)) := by
    funext n
    rw [aux_thm_prop_weighted_response_integral S (a (sigma n)) (b (sigma n)) rho (hb (sigma n))]
  rw [hfun] at h
  obtain ⟨C, hC⟩ := hcore
  have hsupp := aux_thm_prop_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC
    (aux_thm_prop_domain_mem_of_energy E.toClosedForm G hE hw)
  simpa only [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)] using h

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The source range is dense in the form norm for the actual controlled
limit. This supplies the density premises used to extend source nullity. -/
theorem aux_thm_prop_controlled_source_dense
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (hcontract : ∀ n (T : ℝ → ℝ), _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T →
      ∀ u : S.space, ∃ v : S.space,
        ((v.val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧ responseForm S (a n) v v ≤ responseForm S (a n) u u)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    (∀ f, G f ∈ E.domain) ∧
      (∀ v ∈ E.domain, ∀ eps : ℝ, 0 < eps →
        ∃ f0, E.energyNormSq (v - G f0) < eps) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ f, E.energyNormSq (G f) ≤ C * ‖f‖ ^ 2) := by
  obtain ⟨_E0, R, _hE0, hSym, hRsym, hRcomp, hRdom, hRinj, _hLow⟩ :=
    aux_thm_prop_inverse_limit_form d hd z r hr S hS a hcontract GN hGN A.interpolation
      A.K A.K_pos A.coercive A.sources A.sources_countable A.sources_dense A.sources_smooth
      (fun f => aux_thm_prop_response_cauchy GN G hConv f.val) A.mesh G hConv
  have hdom : ∀ v, v ∈ E.domain ↔ v ∈ limitFormDomain G := by
    intro v
    rw [← E.toClosedForm.energy_lt_top_iff, hE]
    rfl
  have hGmem : ∀ f, G f ∈ E.domain := by
    intro f
    apply (hdom _).mpr
    rw [hRdom]
    exact ⟨R f, by rw [← ContinuousLinearMap.comp_apply, hRcomp]⟩
  exact ⟨hGmem,
    aux_thm_prop_hregularity_hRange_of_root G R E hE hSym hRsym hRcomp hRinj hRdom hGmem hdom,
    aux_thm_prop_hregularity_hGbound_of_root G R E hE hSym hRsym hRcomp hRinj hGmem⟩

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

/-- Actual finite source growth, the proved weighted lower bound and source
range density imply coordinate-plane nullity on the entire form domain. -/
theorem aux_thm_prop_domain_planes_null_of_source_growth
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hD : Dense (D : Set (DomainL2 (centeredCube z r hr))))
    (uN : D → ℕ → S.space)
    (huN : ∀ f n, uN f n = responseSolution S (a n) ((sobolevVolumeLoad f.val).comp S.space.subtypeL))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hGrowth : ∀ f : D,
      let muN : ℕ → Measure (SpatialCoordinates d) := fun n =>
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((uN f n).val.2 i y) ^ 2))
      ∃ E0 Kg : ℝ, 0 ≤ E0 ∧ 0 ≤ Kg ∧
        (∀ n, muN n Set.univ ≤ ENNReal.ofReal E0) ∧
        (∀ n, muN n (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0) ∧
        (∀ n (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 / 2 →
          muN n (Metric.ball x s) ≤ ENNReal.ofReal (Kg * s ^ t))) :
    ∀ u ∈ E.domain, ∀ (i : Fin d) (c : ℝ),
      Gamma.measure u {x : SpatialCoordinates d | x i = c} = 0 := by
  have hMosco := aux_thm_prop_controlled_mosco hS A GN G hGN hConv
  have hWeighted := aux_thm_prop_controlled_weighted_input BD BDQ EM hcontract hS
    A GN G hGN hConv E hE hcore Gamma
  have hSupp : ∀ u ∈ E.domain,
      Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
    obtain ⟨C, hC⟩ := hcore
    exact fun u hu => aux_thm_prop_energy_measure_support Gamma
      (centeredCube z r hr).isOpen.measurableSet hC hu
  have hNull : ∀ f : D, ∀ (i : Fin d) (c : ℝ),
      Gamma.measure (G f.val) {x : SpatialCoordinates d | x i = c} = 0 := by
    intro f
    obtain ⟨E0, Kg, hE0, hKg, hmass, hsupp, hgrowth⟩ := hGrowth f
    have hEnergy : ∀ n, responseForm S (a n) (uN f n) (uN f n) ≤ E0 := by
      intro n
      have h := hmass n
      rw [aux_prop_boundary_mass_univ] at h
      exact (ENNReal.ofReal_le_ofReal_iff hE0).mp h
    have huConv : Tendsto (fun n => (uN f n).val.1) atTop (𝓝 (G f.val)) := by
      have h := ((ContinuousLinearMap.apply ℝ _ f.val).continuous.tendsto G).comp hConv
      exact h.congr' (Eventually.of_forall fun n => by
        change GN n f.val = (uN f n).val.1
        rw [hGN, huN])
    apply aux_thm_prop_planes_null_of_energy_clusters hd
      (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
      (lane2_isCompact_closure_centeredCube z hr) _ E0 Kg t ht htd hKg hmass hsupp hgrowth
      (Gamma.measure (G f.val))
    intro nu sigma hnu hnuQ hsigma hcluster
    exact (aux_cor_energy_measures_clause_b z r hr rfl S a E.toClosedForm G hE Gamma
      hSupp hWeighted hMosco.lower (G f.val) (uN f) E0 nu sigma hnu hnuQ hsigma
      huConv hEnergy hcluster).2
  obtain ⟨hGmem, hRange, hGbound⟩ := aux_thm_prop_controlled_source_dense hS A
    (fun n => hcontract z r hr S hS (a n)) GN G hGN hConv E hE
  intro u hu i c
  exact aux_thm_prop_source_null_to_domain z r hr G E Gamma hGmem hRange hGbound D hD
    {x : SpatialCoordinates d | x i = c}
    (isClosed_eq (continuous_apply i) continuous_const).measurableSet
    (fun f => hNull f i c) u hu

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The represented source catalogue directly supplies plane nullity for the
actual controlled limiting form; no lower-cluster premise remains. -/
theorem aux_thm_prop_represented_domain_planes_null
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
    (A : aux_thm_prop_analytic_controls d hd (z j) (r j) (hr j) (S j)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)))
    (GN : ℕ → DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
      DomainL2 (centeredCube (z j) (r j) (hr j)))
    (Glim : DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
      DomainL2 (centeredCube (z j) (r j) (hr j)))
    (hGN : ∀ n f, GN n f =
      (responseSolution (S j)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 Glim))
    (EForm : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))))
    (hE : ∀ u, EForm.energy u = limitFormEnergy Glim u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EForm.toClosedForm
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EForm.toClosedForm) :
    ∀ u ∈ EForm.domain, ∀ (i : Fin d) (c : ℝ),
      Gamma.measure u {x : SpatialCoordinates d | x i = c} = 0 := by
  have hGrowth := fun g => aux_thm_prop_represented_source_measure_data d hd M H Ω P cutoff env
    J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
    Index resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
    Grid origin gridRoot gridKey hRep om hom j g
  rcases hRep with ⟨hA, _hAlpha, _hBeta, _hC, _hOrders, _hN, _hIR, _hMeas, _hLaw, _hSeq,
    _hcontain, _hrat, _htri, _hcomplete, _hgrat, _hcover, hS, hDense, _hSrc, _hSrcDense,
    _hTrace, _hSt, _hParent, _hTDense, _hPlateau, _hMeasc, _hMom, _hNonneg, hSol, _hCoeff,
    _hCoerc, _hExt, _hGrid, _hSrcEst, _hCellEst⟩
  exact aux_thm_prop_domain_planes_null_of_source_growth BD BDQ EM hcontract
    (hS j) A GN Glim hGN hConv EForm hE hcore Gamma (D j) (hDense j)
    (fun g n => usrc j g n om) (fun g n => ((hSol j n om hom).1 g).1)
    t hA.1 hA.2 hGrowth

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Both represented sides have null coordinate planes on one common event.
This is obtained from their actual catalogue source energies and the stated
standing inputs, before any choice of a source or a mass-grid shift. -/
theorem aux_thm_prop_catalogue_planes_joint
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
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t) :
    ∀ᵐ om ∂P, ∀ j,
      (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
          (Sspace j) (GE j om) NE,
        ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
          A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0) ∧
      (∀ A : aux_thm_prop_limit_side d hd model H (field om) (z j) (r j) (hr j)
          (Sspace j) (GF j om) NF,
        ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
          A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0) := by
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
  filter_upwards [he, hf] with om home homf j
  constructor
  · intro A
    obtain ⟨controls⟩ := aux_thm_prop_controls_of_bounds hd model H (field om)
      (z j) (r j) (hr j) (Sspace j) (GE j om) NE A.bounds
    exact aux_thm_prop_represented_domain_planes_null d hd BD BDQ EM hcontract model H Ω P
      NE (fun _ om => field om) ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NE n) (field om)) responseE
      (fun i n om => catalogConstant i (NE n) (field om)) eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepE
      om home j controls A.response (GE j om) A.response_eq A.response_tendsto A.form A.energy_eq
      A.core A.gamma
  · intro A
    obtain ⟨controls⟩ := aux_thm_prop_controls_of_bounds hd model H (field om)
      (z j) (r j) (hr j) (Sspace j) (GF j om) NF A.bounds
    exact aux_thm_prop_represented_domain_planes_null d hd BD BDQ EM hcontract model H Ω P
      NF (fun _ om => field om) ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NF n) (field om)) responseF
      (fun i n om => catalogConstant i (NF n) (field om)) eventF
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepF
      om homf j controls A.response (GF j om) A.response_eq A.response_tendsto A.form A.energy_eq
      A.core A.gamma

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

/-- The complete energy-measure convergence package for a controlled actual
limit, in the form-domain formulation consumed by prop_boundary. -/
theorem aux_thm_prop_energy_measure_convergence
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm) :
    -- (a) a recovery sequence carries its energy measures weakly to `Gamma_E(u)`
    (∀ (u : DomainL2 (centeredCube z r hr)) (uN : ℕ → S.space), u ∈ E.domain →
      Tendsto (fun n => ((uN n).val.1,
        ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal))) atTop
        (𝓝 (u, E.energy u)) →
      ∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y *
            ∑ i : Fin d, ((uN n : SobolevData (centeredCube z r hr)).2 i y) ^ 2)))) atTop
          (𝓝 (∫ x, φ x ∂(Gamma.measure u)))) ∧
    -- (b) every weak cluster of the energy measures dominates `Gamma_E(u)`
    (∀ (u : DomainL2 (centeredCube z r hr)) (uN : ℕ → S.space) (E0 : ℝ)
        (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
      nu Set.univ < (⊤ : ENNReal) →
      nu ((closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ) = 0 →
      StrictMono sigma →
      Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
      (∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0) →
      (∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a (sigma n)).val y *
            ∑ i : Fin d, ((uN (sigma n) : SobolevData (centeredCube z r hr)).2 i y) ^ 2))))
          atTop (𝓝 (∫ x, φ x ∂nu))) →
      u ∈ E.domain ∧
        ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
          Gamma.measure u B ≤ nu B) ∧
    -- (c) the cross measures converge weakly to `Gamma_E(u,v)`
    (∀ (u v : DomainL2 (centeredCube z r hr)) (uN vN : ℕ → S.space) (E0 : ℝ),
      Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
      (∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0) →
      v ∈ E.domain →
      Tendsto (fun n => ((vN n).val.1,
        ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (v, E.energy v)) →
      ∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), φ x *
          ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData (centeredCube z r hr)).2 i x) * ((vN n : SobolevData (centeredCube z r hr)).2 i x)))
          atTop
          (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))) := by
  have hMosco := aux_thm_prop_controlled_mosco hS A GN G hGN hConv
  have hWeighted := aux_thm_prop_controlled_weighted_input BD BDQ EM hcontract hS
    A GN G hGN hConv E hE hcore Gamma
  have hSupp : ∀ u ∈ E.domain,
      Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
    obtain ⟨C, hC⟩ := hcore
    exact fun u hu => aux_thm_prop_energy_measure_support Gamma
      (centeredCube z r hr).isOpen.measurableSet hC hu
  have h := cor_energy_measures z r hr rfl S hS a E.toClosedForm G hE Gamma hSupp hWeighted hMosco.lower
  have hdom := aux_thm_prop_domain_eq_of_energy E.toClosedForm G hE
  simpa only [← hdom, ← hE] using! h

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_boundary_class_neg
    {d : ℕ} {beta : ℝ} {z : SpatialCoordinates d} {r : ℝ}
    {g : SpatialCoordinates d → ℝ} (hg : IsCellBoundaryClass beta z r g) :
    IsCellBoundaryClass beta z r (-g) := by
  refine ⟨aux_prop_gluing_isHolderOn_neg beta _ _ hg.1, ?_⟩
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨M, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  simpa only [rescaledDatum, Pi.neg_apply, abs_neg] using hM ⟨x, hx, rfl⟩

theorem aux_thm_prop_boundary_norm_neg
    {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    (g : SpatialCoordinates d → ℝ) :
    cellBoundaryQuotientNorm beta z r (-g) = cellBoundaryQuotientNorm beta z r g := by
  unfold cellBoundaryQuotientNorm quotientCBetaNorm
  congr 1
  ext v
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [← aux_prop_gluing_cAlphaNorm_neg beta _ (fun x => rescaledDatum z r g x - -c)]
    congr 1
    funext x
    simp only [rescaledDatum, Pi.neg_apply]
    ring
  · rintro ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [← aux_prop_gluing_cAlphaNorm_neg beta _ (fun x => rescaledDatum z r g x - c)]
    congr 1
    funext x
    simp only [rescaledDatum, Pi.neg_apply]
    ring

/-- The boundary response is uniformly continuous in the genuine boundary
quotient seminorm, with the represented extension bound as its constant. -/
theorem aux_thm_prop_boundary_response_close
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (beta : ℝ)
    (a : SpatialCoordinates d → ℝ) (Lam K : ℝ) (hK : 0 ≤ K)
    (ha0 : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ a x)
    (haLam : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), a x ≤ Lam)
    (hameas : AEStronglyMeasurable a
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hExt : ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta z r e.toFun →
      cellDirichletInfimum a (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
        K * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
    (u v : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hu : ContinuousOn u.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hv : ContinuousOn v.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hclass : IsCellBoundaryClass beta z r (u.toFun - v.toFun)) :
    |Real.sqrt (cellDirichletInfimum a (centeredCube z r hr : Set (SpatialCoordinates d)) u) -
      Real.sqrt (cellDirichletInfimum a (centeredCube z r hr : Set (SpatialCoordinates d)) v)| ≤
      Real.sqrt K * cellBoundaryQuotientNorm beta z r (u.toFun - v.toFun) := by
  have hsub : (u - v).toFun = u.toFun - v.toFun := H1Function.sub_toFun u v
  have hrev : (v - u).toFun = -(u.toFun - v.toFun) := by
    rw [H1Function.sub_toFun]
    exact neg_sub u.toFun v.toFun |>.symm
  have he1 := hExt (u - v) (by rw [hsub]; exact hu.sub hv) (by rwa [hsub])
  have he2 := hExt (v - u) (by rw [H1Function.sub_toFun]; exact hv.sub hu)
    (by rw [hrev]; exact aux_thm_prop_boundary_class_neg hclass)
  rw [hsub] at he1
  rw [hrev, aux_thm_prop_boundary_norm_neg] at he2
  have hn := aux_prop_gluing_quotientNorm_nonneg beta z r (u.toFun - v.toFun)
  have hsqrt : Real.sqrt (K * cellBoundaryQuotientNorm beta z r (u.toFun - v.toFun) ^ 2) =
      Real.sqrt K * cellBoundaryQuotientNorm beta z r (u.toFun - v.toFun) := by
    rw [Real.sqrt_mul hK, Real.sqrt_sq hn]
  have hs1 := aux_prop_gluing_sqrt_infimum_sub_le _
    (centeredCube z r hr).isOpen.measurableSet a Lam ha0 haLam hameas u v
  have hs2 := aux_prop_gluing_sqrt_infimum_sub_le _
    (centeredCube z r hr).isOpen.measurableSet a Lam ha0 haLam hameas v u
  have h1 := Real.sqrt_le_sqrt he1
  have h2 := Real.sqrt_le_sqrt he2
  rw [hsqrt] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Response convergence on a countable dense trace bank determines every
continuous boundary datum approximated in its boundary quotient seminorm. -/
theorem aux_thm_prop_boundary_response_limit
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (beta : ℝ)
    (a : ℕ → SpatialCoordinates d → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ n, ∃ Lam : ℝ,
      (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ a n x ∧ a n x ≤ Lam) ∧
      AEStronglyMeasurable (a n)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hExt : ∀ n, ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta z r e.toFun →
      cellDirichletInfimum (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
        K * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
    (u : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (v : ℕ → H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hu : ContinuousOn u.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hv : ∀ k, ContinuousOn (v k).toFun
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hclass : ∀ k, IsCellBoundaryClass beta z r ((v k).toFun - u.toFun))
    (happrox : Tendsto (fun k => cellBoundaryQuotientNorm beta z r ((v k).toFun - u.toFun))
      atTop (𝓝 0))
    (l : ℕ → ℝ)
    (hl : ∀ k, Tendsto (fun n => cellDirichletInfimum (a n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) (v k)) atTop (𝓝 (l k))) :
    ∃ L : ℝ, Tendsto (fun n => cellDirichletInfimum (a n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) u) atTop (𝓝 L) ∧
      Tendsto l atTop (𝓝 L) := by
  have hnonneg (n : ℕ) (w : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    aux_prop_gluing_infimum_nonneg _ (centeredCube z r hr).isOpen.measurableSet (a n)
      (fun x hx => ((ha n).choose_spec.1 x hx).1) w
  obtain ⟨L, hL, hlL, -⟩ := aux_prop_gluing_response_three_eps _ _ l
    (fun n => hnonneg n u) (fun k n => hnonneg n (v k)) hl
    (fun k => Real.sqrt K * cellBoundaryQuotientNorm beta z r ((v k).toFun - u.toFun))
    (by simpa only [mul_zero] using happrox.const_mul (Real.sqrt K)) (by
      intro k n
      obtain ⟨Lam, hbounds, hmeas⟩ := ha n
      rw [abs_sub_comm]
      exact aux_thm_prop_boundary_response_close z r hr beta (a n) Lam K hK
        (fun x hx => (hbounds x hx).1) (fun x hx => (hbounds x hx).2) hmeas
        (hExt n) (v k) u (hv k) hu (hclass k))
  exact ⟨L, hL, hlL⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- The actual represented trace bank determines the finite-cutoff boundary
response of each continuous admissible datum, on its original good event. -/
theorem aux_thm_prop_represented_boundary_response
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
    (u : H1Function (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (hu : ContinuousOn u.toFun
      (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))))
    (hHolder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) u.toFun)
    (hClass : IsCellBoundaryClass beta (z j) (r j) u.toFun) :
    ∃ L : ℝ, Tendsto (fun n => cellDirichletInfimum
      (cutoffCoefficient M H (env n om) (cutoff n))
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) u) atTop (𝓝 L) := by
  rcases hRep with ⟨hA, hAlpha, hBeta, hC, hOrders, hN, hIR, hMeas, hLaw, hSeq,
    hcontain, hrat, htri, hcomplete, hgrat, hcover, hS, hDense, hSrc, hSrcDense,
    hTrace, hSt, hParent, hTDense, hPlateau, hMeasc, hMom, hNonneg, hSol, hCoeff,
    hCoerc, hExt, hGrid, hSrcEst, hCellEst⟩
  obtain ⟨B, hB⟩ := hSeq.2.2.2.2 (extensionKey j) om hom
  obtain ⟨h, hclass, hnorm, hUniform⟩ := hTDense j u.toFun hHolder hClass
  have hbound (n : ℕ) : constants (extensionKey j) n om ≤ max B 0 :=
    (le_abs_self _).trans ((hB n).trans (le_max_left _ _))
  obtain ⟨L, hL, -⟩ := aux_thm_prop_boundary_response_limit (z j) (r j) (hr j) beta
    (fun n => cutoffCoefficient M H (env n om) (cutoff n))
    (Cext * max B 0 * (r j) ^ ((d : ℝ) - 2))
    (mul_nonneg (mul_nonneg hC.le (le_max_right _ _)) (Real.rpow_nonneg (hr j).le _))
    (by
      intro n
      have hc := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (env n om) (cutoff n)
      obtain ⟨Lam, hLam⟩ := ((lane2_isCompact_closure_centeredCube (z j) (hr j)).image
        hc).bddAbove
      refine ⟨Lam, ?_, hc.aestronglyMeasurable⟩
      intro x hx
      exact ⟨(_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (env n om) (cutoff n) x).le,
        hLam ⟨x, subset_closure hx, rfl⟩⟩)
    (by
      intro n e he hc
      refine (hExt j n om hom e he hc).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound n) hC.le)
          (Real.rpow_nonneg (hr j).le _)) (sq_nonneg _))
    u (fun k => thetaH1 j (h k)) hu
    (fun k => by rw [(hTrace j (h k)).2]; exact (hTrace j (h k)).1.continuous.continuousOn)
    (fun k => by rw [(hTrace j (h k)).2]; exact hclass k)
    (by simpa only [fun k => (hTrace j (h k)).2] using hnorm)
    (fun k => respLim (cellResponseKey j (h k)) om)
    (by
      intro k
      have hc := hSeq.2.2.2.1 (cellResponseKey j (h k)) om hom
      convert hc using 1
      funext n
      exact ((hSol j n om hom).2 (h k)).2.2.2.2.symm)
  exact ⟨L, hL⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- The native and Hilbert-space boundary minimizations are the same actual
variational problem. Both directions use genuine zero-trace competitors. -/
theorem aux_thm_prop_cell_response_eq_dirichlet
    {d : ℕ} [NeZero d] {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖)
    (aC : PositiveCoefficient Q) (a : SpatialCoordinates d → ℝ)
    (haC : aC.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a)
    (Lam : ℝ) (ha0 : ∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ a x)
    (haLam : ∀ x ∈ (Q : Set (SpatialCoordinates d)), a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict (Q : Set (SpatialCoordinates d))))
    (e : H1Function (Q : Set (SpatialCoordinates d))) :
    cellDirichletInfimum a (Q : Set (SpatialCoordinates d)) e =
      dirichletResponse (killedResponseSpace hP) aC
        (⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩ : weakSobolevGraph Q) := by
  apply le_antisymm
  · exact aux_lem_skeleton_cellDirichletInfimum_le_dirichletResponse
      hP aC a haC Lam ha0 haLam hameas e
  · apply le_csInf (aux_prop_gluing_infimum_set_bdd _ Q.isOpen.measurableSet a ha0 e).2
    rintro _ ⟨u, ⟨v, hvf, hvg⟩, rfl⟩
    have hsum : sobolevDataOfH1 u = sobolevDataOfH1 e + sobolevDataOfH1 v.toH1Function := by
      refine Prod.ext ?_ ?_
      · apply Lp.ext
        filter_upwards [sobolevDataOfH1_fst_coeFn u, sobolevDataOfH1_fst_coeFn e,
          sobolevDataOfH1_fst_coeFn v.toH1Function,
          Lp.coeFn_add (sobolevDataOfH1 e).1 (sobolevDataOfH1 v.toH1Function).1]
            with x hu he hv hadd
        change _ = ((sobolevDataOfH1 e).1 + (sobolevDataOfH1 v.toH1Function).1) x
        rw [hadd, Pi.add_apply, hu, he, hv]
        exact hvf x
      · funext i
        apply Lp.ext
        filter_upwards [sobolevDataOfH1_snd_coeFn u i, sobolevDataOfH1_snd_coeFn e i,
          sobolevDataOfH1_snd_coeFn v.toH1Function i,
          Lp.coeFn_add ((sobolevDataOfH1 e).2 i) ((sobolevDataOfH1 v.toH1Function).2 i)]
            with x hu he hv hadd
        change _ = ((sobolevDataOfH1 e).2 i + (sobolevDataOfH1 v.toH1Function).2 i) x
        rw [hadd, Pi.add_apply, hu, he, hv]
        exact congrFun (hvg x) i
    rw [← aux_lem_skeleton_sobolevCoefficientForm_eq_energy aC a haC Lam ha0 haLam hameas u,
      hsum]
    exact (dirichletResponse_isLeast (killedResponseSpace hP) aC
      ⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩).2
        ⟨⟨sobolevDataOfH1 v.toH1Function, sobolevDataOfH1_mem_killed v⟩, rfl⟩

/-- The literal affine function and its constant gradient, in the native H1
carrier used by the represented boundary-response catalogue. -/
noncomputable def aux_thm_prop_affine_H1
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) : H1Function (Q : Set (SpatialCoordinates d)) where
  toFun := affineSlope p
  grad := fun _ => p
  memL2 := by simpa only [add_zero] using affine_memLp hQ p 0
  gradMemL2 := fun i => memLp_const (p i)
  hasWeakGradient := by
    intro i
    have hpart := HasWeakPartialDerivOn.of_contDiff
      (U := (Q : Set (SpatialCoordinates d))) (i := i)
      (f := fun x => affineSlope p x) (hf := (affineSlope p).contDiff)
    have hbasis : affineSlope p (basisVec i) = p i := by
      simp [affineSlope_apply, basisVec, Pi.single_apply]
    intro phi hphi hsupp hsub
    simpa only [ContinuousLinearMap.fderiv, hbasis] using hpart phi hphi hsupp hsub

theorem aux_thm_prop_affine_H1_data
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d))) (p : Fin d → ℝ) :
    sobolevDataOfH1 (aux_thm_prop_affine_H1 hQ p) = affineSobolevData hQ p 0 := by
  refine Prod.ext ?_ ?_
  · apply Lp.ext
    filter_upwards [sobolevDataOfH1_fst_coeFn (aux_thm_prop_affine_H1 hQ p),
      affineL2_coeFn hQ p 0] with x h1 h2
    change _ = affineL2 hQ p 0 x
    rw [h1, h2, add_zero]
    rfl
  · funext i
    apply Lp.ext
    filter_upwards [sobolevDataOfH1_snd_coeFn (aux_thm_prop_affine_H1 hQ p) i,
      domainConstantL2_coeFn (Ω := Q) (p i)] with x h1 h2
    change _ = domainConstantL2 (Ω := Q) (p i) x
    rw [h1, h2]
    rfl

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_matrix_polarization {d : ℕ}
    (A : Fin d → Fin d → ℝ) (hA : ∀ i j, A i j = A j i) (i j : Fin d) :
    ((∑ k : Fin d, ∑ l : Fin d,
        A k l * ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) k * ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) l) -
      (∑ k : Fin d, ∑ l : Fin d, A k l * (Pi.single i (1 : ℝ) : Fin d → ℝ) k * (Pi.single i (1 : ℝ) : Fin d → ℝ) l) -
      (∑ k : Fin d, ∑ l : Fin d, A k l * (Pi.single j (1 : ℝ) : Fin d → ℝ) k * (Pi.single j (1 : ℝ) : Fin d → ℝ) l)) / 2 = A i j := by
  classical
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hA j i]
  ring

/-- Limits of genuine symmetric finite-dimensional response quadratics produce
a symmetric matrix limit. Its entries are fixed by polarization of the responses. -/
theorem aux_thm_prop_quadratic_matrix_limit {d : ℕ}
    (R : ℕ → (Fin d → ℝ) → ℝ)
    (hR : ∀ n, ∃ A : Fin d → Fin d → ℝ,
      (∀ i j, A i j = A j i) ∧ ∀ p, R n p = ∑ i : Fin d, ∑ j : Fin d, A i j * p i * p j)
    (hlimit : ∀ p, ∃ L : ℝ, Tendsto (fun n => R n p) atTop (𝓝 L)) :
    ∃ (AN : ℕ → Fin d → Fin d → ℝ) (A : Fin d → Fin d → ℝ),
      (∀ n i j, AN n i j = AN n j i) ∧
      (∀ n p, R n p = ∑ i : Fin d, ∑ j : Fin d, AN n i j * p i * p j) ∧
      Tendsto AN atTop (𝓝 A) ∧ (∀ i j, A i j = A j i) ∧
      ∀ p, Tendsto (fun n => R n p) atTop
        (𝓝 (∑ i : Fin d, ∑ j : Fin d, A i j * p i * p j)) := by
  classical
  choose AN hsym hquad using hR
  choose L hL using hlimit
  let A : Fin d → Fin d → ℝ := fun i j =>
    (L ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) - L ((Pi.single i (1 : ℝ) : Fin d → ℝ)) - L ((Pi.single j (1 : ℝ) : Fin d → ℝ))) / 2
  have hentry (i j : Fin d) : Tendsto (fun n => AN n i j) atTop (𝓝 (A i j)) := by
    have h := (((hL ((Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ))).sub
      (hL ((Pi.single i (1 : ℝ) : Fin d → ℝ)))).sub (hL ((Pi.single j (1 : ℝ) : Fin d → ℝ)))).div_const 2
    apply h.congr
    intro n
    simp only [hquad]
    exact aux_thm_prop_matrix_polarization (AN n) (hsym n) i j
  refine ⟨AN, A, hsym, hquad,
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => hentry i j)), ?_, ?_⟩
  · intro i j
    exact tendsto_nhds_unique (hentry i j)
      ((hentry j i).congr (fun n => hsym n j i))
  · intro p
    have h := tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => ((hentry i j).mul_const (p i)).mul_const (p j)))
    exact h.congr (fun n => (hquad n p).symm)



theorem aux_thm_prop_affine_matrix_limit
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖)
    (a : ℕ → PositiveCoefficient Q)
    (hlimit : ∀ p, ∃ L : ℝ,
      Tendsto (fun n => affineDirichletResponse hQ hP (a n) p) atTop (𝓝 L)) :
    ∃ (AN : ℕ → Fin d → Fin d → ℝ) (A : Fin d → Fin d → ℝ),
      (∀ n i j, AN n i j = AN n j i) ∧
      (∀ n p, affineDirichletResponse hQ hP (a n) p =
        ∑ i : Fin d, ∑ j : Fin d, AN n i j * p i * p j) ∧
      Tendsto AN atTop (𝓝 A) ∧ (∀ i j, A i j = A j i) ∧
      ∀ p, Tendsto (fun n => affineDirichletResponse hQ hP (a n) p) atTop
        (𝓝 (∑ i : Fin d, ∑ j : Fin d, A i j * p i * p j)) :=
  aux_thm_prop_quadratic_matrix_limit _
    (fun n => aux_lem_band_rcJ_bridge_B2_dirichlet_quadratic hQ hP (a n)) hlimit

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_holder_of_lipschitz_bounded
    {d : ℕ} {beta : ℝ} (hbeta : beta ≤ 1)
    {f : SpatialCoordinates d → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {S : Set (SpatialCoordinates d)} (hS : Bornology.IsBounded S) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f := by
  obtain ⟨R, hR, hbound⟩ := hS.exists_pos_norm_le
  apply aux_lem_skeleton_isHolderOn_of_dist_bound
    (C := (L : ℝ) * ((d : ℝ) * (2 * R)) ^ (1 - beta)) (by positivity)
  intro x hx y hy hxy
  have he := aux_prop_gluing_euclid_pos x y hxy
  let E : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)
  have hEpos : 0 < E := he
  have hdistE : dist x y ≤ E := by
    simpa [E, Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
      (Homogenization.norm_le_euclideanNorm (x - y))
  have hEdim : E ≤ (d : ℝ) * dist x y := by
    simpa [E, Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
      (Homogenization.euclideanNorm_le_dimension_mul_norm (x - y))
  have hdxy : dist x y ≤ 2 * R := by
    calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
      _ ≤ R + R := add_le_add (hbound x hx) (hbound y hy)
      _ = 2 * R := by ring
  have hEbound := hEdim.trans (mul_le_mul_of_nonneg_left hdxy (Nat.cast_nonneg d))
  have hexp : E = E ^ (1 - beta) * E ^ beta := by
    rw [← Real.rpow_add hEpos]
    norm_num
  have hmono : E ^ (1 - beta) ≤ ((d : ℝ) * (2 * R)) ^ (1 - beta) :=
    Real.rpow_le_rpow hEpos.le hEbound (sub_nonneg.mpr hbeta)
  have hlip : |f x - f y| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using hf.dist_le_mul x y
  calc |f x - f y| ≤ (L : ℝ) * dist x y := hlip
    _ ≤ (L : ℝ) * E := mul_le_mul_of_nonneg_left hdistE L.coe_nonneg
    _ = ((L : ℝ) * E ^ (1 - beta)) * E ^ beta := by rw [mul_assoc, ← hexp]
    _ ≤ ((L : ℝ) * ((d : ℝ) * (2 * R)) ^ (1 - beta)) * E ^ beta :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono L.coe_nonneg)
        (Real.rpow_nonneg hEpos.le _)

/-- Literal affine data meet every sub-Lipschitz boundary class used by the
represented catalogue; no catalogue enlargement or stronger exponent is used. -/
theorem aux_thm_prop_affine_boundary_data
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (alpha beta : ℝ) (ha : alpha ≤ 1) (hb : beta ≤ 1) (p : Fin d → ℝ) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (frontier (centeredCube z r hr : Set (SpatialCoordinates d)))
      (affineSlope p) ∧
    IsCellBoundaryClass beta z r (affineSlope p) := by
  have hc := lane2_isCompact_closure_centeredCube z hr
  have hc0 := lane2_isCompact_closure_centeredCube (0 : SpatialCoordinates d) one_pos
  have hfront := hc0.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hrescale : rescaledDatum z r (affineSlope p) =
      fun y => (r • affineSlope p) y + affineSlope p z := by
    funext y
    change affineSlope p (z + r • y) = _
    rw [map_add, map_smul]
    simp only [smul_apply, smul_eq_mul]
    ring
  refine ⟨aux_thm_prop_holder_of_lipschitz_bounded ha (affineSlope p).lipschitzWith
    (hc.isBounded.subset frontier_subset_closure), ?_⟩
  unfold IsCellBoundaryClass
  rw [hrescale]
  have hlip : LipschitzWith ‖r • affineSlope p‖₊
      (fun y => (r • affineSlope p) y + affineSlope p z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using (r • affineSlope p).lipschitzWith.dist_le_mul x y
  refine ⟨aux_thm_prop_holder_of_lipschitz_bounded hb hlip hfront.isBounded, ?_⟩
  obtain ⟨B, hB⟩ := (hfront.image
    (((r • affineSlope p).continuous.add continuous_const).abs)).bddAbove
  refine ⟨B, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  exact hB ⟨x, hx, rfl⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- Every represented cube has actual affine response matrix limits. The
scalar convergence comes from the existing trace bank; the finite matrices
are the coefficient minimization quadratics, and the limit is normalized by
this cube's actual volume. -/
theorem aux_thm_prop_represented_affine_matrix
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
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖) :
    ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.transpose = A ∧ ∀ p : Fin d → ℝ,
        Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) hP
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)) p /
          (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ A.mulVec p)) := by
  have : NeZero d := ⟨by omega⟩
  have halpha : alpha < 1 := hRep.2.1.1
  have hbeta : beta < alpha := hRep.2.2.1.2
  have hscalar (p : Fin d → ℝ) : ∃ L : ℝ,
      Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)) p)
        atTop (𝓝 L) := by
    let u := aux_thm_prop_affine_H1 (centeredCube_isBounded (z j) (hr j)) p
    have hu : u.toFun = affineSlope p := rfl
    have hdata := aux_thm_prop_affine_boundary_data (z j) (r j) (hr j)
      alpha beta halpha.le (hbeta.trans halpha).le p
    obtain ⟨L, hL⟩ := aux_thm_prop_represented_boundary_response
      d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell
      Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRep om hom j u
      (by rw [hu]; exact (affineSlope p).continuous.continuousOn)
      (by rw [hu]; exact hdata.1) (by rw [hu]; exact hdata.2)
    refine ⟨L, hL.congr (fun n => ?_)⟩
    have hc := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (env n om) (cutoff n)
    obtain ⟨Lam, hLam⟩ := ((lane2_isCompact_closure_centeredCube (z j) (hr j)).image hc).bddAbove
    have heq := aux_thm_prop_cell_response_eq_dirichlet hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
      (cutoffCoefficient M H (env n om) (cutoff n))
      (aux_lem_replace_large_cube_cutoff_positive_coe M H (env n om) (cutoff n) (z j) (hr j))
      Lam (fun x _ => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (env n om) (cutoff n) x).le)
      (fun x hx => hLam ⟨x, subset_closure hx, rfl⟩) hc.aestronglyMeasurable u
    have hb : (⟨sobolevDataOfH1 u, sobolevDataOfH1_mem_weak u⟩ :
        weakSobolevGraph (centeredCube (z j) (r j) (hr j))) =
        affineSobolev (centeredCube_isBounded (z j) (hr j)) p 0 := by
      apply Subtype.ext
      exact aux_thm_prop_affine_H1_data _ p
    rw [hb] at heq
    exact heq
  obtain ⟨AN, A, hANsym, hAN, hconv, hsym, hlim⟩ :=
    aux_thm_prop_affine_matrix_limit (centeredCube_isBounded (z j) (hr j)) hP _ hscalar
  let v : ℝ := (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal
  refine ⟨fun i j => A i j / v, ?_, ?_⟩
  · ext i k
    exact congrArg (fun x => x / v) (hsym k i)
  · intro p
    convert (hlim p).div_const v using 1
    congr 1
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_thm_prop_choose_symmetric_matrices
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ → Prop)
    (h : ∀ᵐ om ∂P, ∀ j, ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.transpose = A ∧ R j om A) :
    ∃ A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ,
      (∀ j om, (A j om).transpose = A j om) ∧ ∀ᵐ om ∂P, ∀ j, R j om (A j om) := by
  classical
  let A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ := fun j om =>
    if hex : ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = A ∧ R j om A then
      hex.choose else 0
  refine ⟨A, ?_, ?_⟩
  · intro j om
    dsimp only [A]
    split
    · rename_i hex
      exact hex.choose_spec.1
    · simp only [Matrix.transpose_zero]
  · filter_upwards [h] with om hom j
    dsimp only [A]
    rw [dite_eq_left (hom j)]
    exact (Classical.choose_spec (hom j)).2

/-- The normalized affine response limit on one actual represented cube. -/
def aux_thm_prop_affine_converges
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

/-- Both affine matrix banks are constructed from the original represented
catalogues on one common event, with symmetry at every sample. -/
theorem aux_thm_prop_catalogue_affine_matrices
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
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖) :
    ∃ AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ,
      (∀ j om, (AE j om).transpose = AE j om) ∧
      (∀ j om, (AF j om).transpose = AF j om) ∧
      ∀ᵐ om ∂P, ∀ j,
        aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) (AE j om) ∧
        aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) (AF j om) := by
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
  have heA : ∀ᵐ om ∂P, ∀ j, ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.transpose = A ∧
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NE (hP j) A := by
    filter_upwards [he] with om hom j
    exact aux_thm_prop_represented_affine_matrix d hd model H Ω P
      NE (fun _ om => field om) ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NE n) (field om)) responseE
      (fun i n om => catalogConstant i (NE n) (field om)) eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepE
      om hom j (hP j)
  have hfA : ∀ᵐ om ∂P, ∀ j, ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.transpose = A ∧
      aux_thm_prop_affine_converges model H (field om) (z j) (r j) (hr j) NF (hP j) A := by
    filter_upwards [hf] with om hom j
    exact aux_thm_prop_represented_affine_matrix d hd model H Ω P
      NF (fun _ om => field om) ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NF n) (field om)) responseF
      (fun i n om => catalogConstant i (NF n) (field om)) eventF
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepF
      om hom j (hP j)
  obtain ⟨AE, hEsym, hEconv⟩ := aux_thm_prop_choose_symmetric_matrices P _ heA
  obtain ⟨AF, hFsym, hFconv⟩ := aux_thm_prop_choose_symmetric_matrices P _ hfA
  refine ⟨AE, AF, hEsym, hFsym, ?_⟩
  filter_upwards [hEconv, hFconv] with om hE hF j
  exact ⟨hE j, hF j⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- A bounded nonnegative quadratic energy controls both terms of the
volume-normalized fractional norm. -/
theorem aux_thm_prop_fractional_norm_bound (x q V B c : ℝ)
    (_hx : 0 ≤ x) (hq : 0 ≤ q) (hV : 0 < V) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (h : x ^ 2 + V * q ^ 2 ≤ B) :
    q + c * (x / Real.sqrt V) ≤
      Real.sqrt B / Real.sqrt V + c * (Real.sqrt B / Real.sqrt V) := by
  have hsqV : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hsqB : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB
  have hrootV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hrootB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hxB : x ≤ Real.sqrt B := by
    nlinarith [mul_nonneg hV.le (sq_nonneg q)]
  have hqB : q ≤ Real.sqrt B / Real.sqrt V := by
    apply (le_div_iff₀ hrootV).mpr
    have hprod : 0 ≤ q * Real.sqrt V := mul_nonneg hq hrootV.le
    have hs : (q * Real.sqrt V) ^ 2 ≤ (Real.sqrt B) ^ 2 := by
      rw [mul_pow, hsqV, hsqB]
      nlinarith [sq_nonneg x]
    exact (sq_le_sq₀ hprod hrootB).mp hs
  exact add_le_add hqB (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hxB hrootV.le) hc)

/-- Actual finite-energy patches have an L²-convergent subsequence. The limit
is constructed by the standing fractional compact embedding. -/
theorem aux_thm_prop_patch_compactness
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (uN : ℕ → S.space) (E0 : ℝ)
    (hEnergy : ∀ n, responseForm S (a n) (uN n) (uN n) ≤ E0) :
    ∃ (sigma : ℕ → ℕ) (u : DomainL2 (centeredCube z r hr)),
      StrictMono sigma ∧ Tendsto (fun n => (uN (sigma n)).val.1) atTop (𝓝 u) := by
  let V : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  have hV : 0 < V := centeredCube_volume_pos z hr
  let B : ℝ := A.K * max E0 0
  have hB : 0 ≤ B := mul_nonneg A.K_pos.le (le_max_right _ _)
  let c : ℝ := r ^ (-(_root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder : ℝ))
  have hc : 0 ≤ c := Real.rpow_nonneg hr.le _
  let w : ℕ → CubeFractionalL2 (k := 1) hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder :=
    fun n => ⟨fun _ : Fin 1 => (uN n).val.1, (A.coercive n (uN n)).1⟩
  have hBound (n : ℕ) :
      cubeFractionalL2Norm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (w n) ≤
        Real.sqrt B / Real.sqrt V + c * (Real.sqrt B / Real.sqrt V) := by
    have h := (A.coercive n (uN n)).2.trans
      (mul_le_mul_of_nonneg_left ((hEnergy n).trans (le_max_left E0 0)) A.K_pos.le)
    have hn := aux_thm_prop_fractional_norm_bound ‖(uN n).val.1‖
      (cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => (uN n).val.1)).toReal V B c
      (norm_nonneg _) ENNReal.toReal_nonneg hV hB hc h
    simpa only [cubeFractionalL2Norm, w, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
      using hn
  obtain ⟨sigma, hsigma, u, hu⟩ := A.interpolation.compact_embedding z r hr
    _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (by norm_num [_root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder]) w
    (Real.sqrt B / Real.sqrt V + c * (Real.sqrt B / Real.sqrt V)) hBound
  refine ⟨sigma, u, hsigma, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hu

/-- Lowering a growth exponent on radii at most one preserves the estimate. -/
theorem aux_thm_prop_growth_lower_exponent {d : ℕ} {mu : Measure (SpatialCoordinates d)} {C t s rr : ℝ} {x : SpatialCoordinates d}
    (hC : 0 ≤ C) (hrr : 0 < rr) (hrr1 : rr ≤ 1) (hst : s ≤ t)
    (h : mu (Metric.ball x rr) ≤ ENNReal.ofReal (C * rr ^ t)) :
    mu (Metric.ball x rr) ≤ ENNReal.ofReal (C * rr ^ s) :=
  h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hrr hrr1 hst) hC))

/-- The cutoff exponent can be reduced to match a cell-estimate exponent. -/
noncomputable def aux_thm_prop_controls_lower_exponent
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (s : ℝ) (hs : (d : ℝ) - 1 < s) (hst : s ≤ A.t) :
    aux_thm_prop_analytic_controls d hd z r hr S a :=
  { A with
    t := s
    t_lower := hs
    t_upper := hst.trans_lt A.t_upper
    cutoffs := by
      intro K O hK hO hKO hOQ
      obtain ⟨V, chi, chic, B, hV, hKV, hVO, hB, hChi⟩ := A.cutoffs K O hK hO hKO hOQ
      refine ⟨V, chi, chic, B, hV, hKV, hVO, hB, fun n => ?_⟩
      obtain ⟨hcont, hrep, hb, hone, hzero, hE, hgrowth⟩ := hChi n
      refine ⟨hcont, hrep, hb, hone, hzero, hE, ?_⟩
      intro x hx rr hrr hrr1
      exact aux_thm_prop_growth_lower_exponent hB hrr hrr1 hst (hgrowth x hx rr hrr hrr1) }

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


/-- The limiting scalar boundary response is the true minimum of the energy
measure. Its L² cluster is constructed; no solution-convergence premise is used. -/
theorem aux_thm_prop_boundary_glb_of_patches
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (q : Set (SpatialCoordinates d))
    (hqcell : q = (centeredCube z r hr : Set (SpatialCoordinates d)))
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (hkilled : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm q Dq)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ a n x ∧ a n x ≤ Lam)
    (b beta : SpatialCoordinates d → ℝ)
    (hbeta : ContDiff ℝ ∞ beta)
    (hbetasupp : HasCompactSupport beta)
    (hbetaQ : tsupport beta ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetab : ∀ x ∈ frontier q, beta x = b x)
    (betaQ : H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetaQfun : betaQ.toFun = beta)
    (betaq : H1Function q)
    (hbetaqfun : betaq.toFun = beta)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNtrace : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      HasZeroTraceDifferenceOn
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k))
        (betaQ.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNcellcont : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ContinuousOn (UN n).toFun
        (closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d))))
    (hUNcellb : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ frontier (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
        (UN n).toFun x = beta x)
    (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hHcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Hcell k)
    (hCellEnergy : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      energy (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) ≤ Bcell k)
    (hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (hCellHolder : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        ∀ y ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k))
    (A : aux_thm_prop_analytic_controls d hd z (3 * r) h3r S aC)
    (GN : ℕ → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (aC n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (hE : ∀ v, EQ.energy v = limitFormEnergy G v)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EQ.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (L : ℝ)
    (hResponse : Tendsto (fun n => cellDirichletInfimum (a n) q betaq) atTop (𝓝 L)) :
    IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      EQ.toClosedForm Gamma q b) L ∧
    (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      EQ.toClosedForm Gamma q b).Nonempty := by
  subst hqcell
  obtain ⟨E0, hE0⟩ := aux_prop_boundary_energy_bound z r h3r S a aC hacont haC
    UN UNS hUNrep hcellsub Bcell hCellEnergy
  obtain ⟨sigma, uBar, hsigma, huBar⟩ := aux_thm_prop_patch_compactness A UNS E0 hE0
  let A' := aux_thm_prop_controls_reindex
    (aux_thm_prop_controls_lower_exponent A (min A.t t)
      (lt_min A.t_lower ht) (min_le_left _ _)) sigma
  have hG' : Tendsto (fun n => GN (sigma n)) atTop (𝓝 G) :=
    hConv.comp hsigma.tendsto_atTop
  have hMosco := aux_thm_prop_controlled_mosco hS A' _ G
    (fun n => hGN (sigma n)) hG'
  have hMeasures := aux_thm_prop_energy_measure_convergence BD BDQ EM hcontract hS A'
    _ G (fun n => hGN (sigma n)) hG' EQ hE hcore Gamma
  have hdom := aux_thm_prop_domain_eq_of_energy EQ.toClosedForm G hE
  have hKilled (k : OddGridIndex d (triadicHalf 1)) :
      ∃ D, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) D :=
    ⟨_, aux_thm_prop_isKilledDomain _ _⟩
  obtain ⟨U, Uc, hUdom, hUc, hUrep, _hUunif, hUb, _hUface, _hUorth, hUlim, hUmin⟩ :=
    prop_boundary d hd z r hr h3r EQ Gamma _ rfl Dq hkilled S hS
      (fun n => a (sigma n)) (fun n => aC (sigma n))
      (fun n => hacont (sigma n)) (fun n => haC (sigma n)) (fun n => hell (sigma n))
      b beta hbeta hbetasupp hbetaQ hbetab betaQ hbetaQfun betaq hbetaqfun
      (fun n => UN (sigma n)) (fun n => UNS (sigma n)) (fun n => hUNrep (sigma n))
      uBar huBar hcellsub (fun n => hUNharm (sigma n)) (fun n => hUNtrace (sigma n))
      (fun n => hUNcellcont (sigma n)) (fun n => hUNcellb (sigma n))
      (min A.t t) alpha (lt_min A.t_lower ht) ((min_le_right _ _).trans_lt htd)
      halpha halpha1 Bcell Hcell hBcell hHcell (fun n => hCellEnergy (sigma n))
      (fun n k x hx rr hrr hrr1 => aux_thm_prop_growth_lower_exponent (hBcell k)
        hrr hrr1 (min_le_right A.t t) (hCellGrowth (sigma n) k x hx rr hrr hrr1))
      (fun n => hCellHolder (sigma n))
      (by simpa only [hE] using hMosco.lower)
      (by simpa only [← hdom, ← hE] using! hMosco.recovery)
      (fun _ => A'.K) (fun _ => A'.K_pos.le) A'.K (fun _ => le_rfl)
      (fun w => (A'.coercive 0 w).1) (fun n w => (A'.coercive n w).2)
      A'.interpolation A'.cutoffs hMeasures
      (fun zc rc hrc hsub D hD w hw wc hwc hrep hzero wq hwq =>
        aux_thm_prop_boundary_truncation d hd z zc (3 * r) rc h3r hrc hsub
          EQ Gamma hcore D hD w hw wc hwc hrep hzero wq hwq)
      hKilled
  have hL : (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal = L :=
    tendsto_nhds_unique hUlim (hResponse.comp hsigma.tendsto_atTop)
  have hmem : (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ∈
      aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) EQ.toClosedForm Gamma
        (centeredCube z r hr : Set (SpatialCoordinates d)) b :=
    ⟨U, Uc, hUdom, hUc, hUrep, hUb, rfl⟩
  have hleast : IsLeast (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      EQ.toClosedForm Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) b)
      (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    refine ⟨hmem, ?_⟩
    rintro e ⟨V, Vc, hV, hVc, hVrep, hVb, rfl⟩
    exact hUmin V hV Vc hVc hVrep hVb
  exact ⟨hL ▸ hleast.isGLB, ⟨_, hmem⟩⟩

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- Turn the genuine Euclidean Hölder norm into explicit ambient metric bounds.
The dimension factor is fixed before the cutoff index. -/
theorem aux_thm_prop_holder_metric_bounds
    {d : ℕ} (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (f : SpatialCoordinates d → ℝ) (hf : ContinuousOn f K)
    (alpha : ℝ) (halpha : 0 ≤ alpha) (hholder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha K f)
    (C : ℝ) (hC : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha K f ≤ C) :
    (∀ x ∈ K, |f x| ≤ C) ∧
    (∀ x ∈ K, ∀ y ∈ K,
      |f x - f y| ≤ C * (d : ℝ) ^ alpha * dist x y ^ alpha) := by
  have hSup : BddAbove {v : ℝ | ∃ x ∈ K, v = |f x|} := by
    have h := (hK.image_of_continuousOn hf.abs).bddAbove
    convert h using 1
    ext v
    simp only [mem_ofPred_eq, mem_image]
    constructor <;> rintro ⟨x, hx, he⟩ <;> exact ⟨x, hx, he.symm⟩
  have h0 : 0 ≤ C := (aux_prop_gluing_cAlphaNorm_nonneg alpha K f).trans hC
  have hs : _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha K f ≤ C :=
    (aux_lem_skeleton_cAlphaNorm_ge_holderSeminorm alpha K f).trans hC
  constructor
  · intro x hx
    have hv : |f x| ≤ sSup {v : ℝ | ∃ x ∈ K, v = |f x|} :=
      le_csSup hSup ⟨x, hx, rfl⟩
    exact hv.trans ((le_add_of_nonneg_right
      (aux_prop_gluing_holderSeminorm_nonneg alpha K f)).trans hC)
  · intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg h0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg dist_nonneg _)
    have hepos := aux_prop_gluing_euclid_pos x y hxy
    have hratio : |f x - f y| /
        (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha ≤ C :=
      (le_csSup hholder ⟨x, hx, y, hy, hxy, rfl⟩).trans hs
    have hbound := (div_le_iff₀ (Real.rpow_pos_of_pos hepos alpha)).mp hratio
    have heuclid : Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ (d : ℝ) * dist x y := by
      simpa only [euclideanNorm, vecNormSq, vecDot, Pi.sub_apply, ← pow_two, dist_eq_norm]
        using euclideanNorm_le_dimension_mul_norm (x - y)
    calc
      |f x - f y| ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha := hbound
      _ ≤ C * ((d : ℝ) * dist x y) ^ alpha :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.sqrt_nonneg _) heuclid halpha) h0
      _ = C * (d : ℝ) ^ alpha * dist x y ^ alpha := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) dist_nonneg, mul_assoc]

/-- The literal scalar elliptic cell problem has the same value and gradient
for any two solutions of its boundary datum. -/
theorem aux_thm_prop_harmonic_cell_unique
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ)
    (ha : ContinuousOn a (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < a x)
    (u v b : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hu : IsWeaklyHarmonicOn a (centeredCube z r hr : Set (SpatialCoordinates d)) u)
    (hub : HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d)) u b)
    (hv : IsWeaklyHarmonicOn a (centeredCube z r hr : Set (SpatialCoordinates d)) v)
    (hvb : HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d)) v b) :
    (u.toFun =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] v.toFun) ∧
    (u.grad =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] v.grad) := by
  obtain ⟨lo, hi, hlo, _hhi, hbounds⟩ := aux_thm_prop_weight_bounds_on z r hr a ha hpos
  exact ae_eq_of_isWeaklyHarmonicOn_of_hasZeroTraceDifferenceOn
    (isOpenBoundedConvexDomain_ball z (half_pos hr))
    ⟨z, Metric.mem_ball_self (half_pos hr)⟩
    (aux_prop_boundary_elliptic _ _ (centeredCube z r hr).isOpen.measurableSet
      subset_closure a ha lo hi hlo hbounds) hu hub hv hvb

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- The represented finite-cutoff cell solutions supply all estimates for any
harmonic solution of the same trace. Constants are fixed before the cutoff. -/
theorem aux_thm_prop_represented_cell_bounds
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
    (h : T j) :
    ∃ B Hc : ℝ, 0 ≤ B ∧ 0 ≤ Hc ∧
      ∀ (n : ℕ) (w : H1Function (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))),
        IsWeaklyHarmonicOn (cutoffCoefficient M H (env n om) (cutoff n))
          (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) w →
        HasZeroTraceDifferenceOn (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))
          w (thetaH1 j h) →
        energy (cutoffCoefficient M H (env n om) (cutoff n))
          (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) w ≤ B ∧
        (∀ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
          ((volume.restrict (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (cutoffCoefficient M H (env n om) (cutoff n) y *
              ∑ i : Fin d, (w.grad y i) ^ 2))) (Metric.ball x rr) ≤
              ENNReal.ofReal (B * rr ^ t)) ∧
        ∃ wc : SpatialCoordinates d → ℝ,
          ContinuousOn wc (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ∧
          (w.toFun =ᵐ[volume.restrict (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))] wc) ∧
          (∀ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
              |wc x - wc y| ≤ Hc * dist x y ^ alpha) ∧
          (∀ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)), |wc x| ≤ Hc) := by
  let : NeZero d := ⟨by omega⟩
  rcases hRep with ⟨hA, hAlpha, hBeta, hC, hOrders, hN, hIR, hMeas, hLaw, hSeq,
    hcontain, hrat, htri, hcomplete, hgrat, hcover, hS, hDense, hSrc, hSrcDense,
    hTrace, hSt, hParent, hTDense, hPlateau, hMeasc, hMom, hNonneg, hSol, hCoeff,
    hCoerc, hExt, hGrid, hSrcEst, hCellEst⟩
  obtain ⟨Bresp, hResp⟩ := (hSeq.2.2.2.1 (cellResponseKey j h) om hom).bddAbove_range
  obtain ⟨Bgrow, hGrow⟩ := hSeq.2.2.2.2 (cellGrowthKey j h) om hom
  obtain ⟨Bhold, hHold⟩ := hSeq.2.2.2.2 (cellHolderKey j h) om hom
  let cn : ℝ := _root_.SubdiffusiveProcess.EllipticRegularity.c2Norm
    (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) (theta j h)
  let B : ℝ := max Bresp 0 + max Bgrow 0 * cn ^ 2
  let C : ℝ := max Bhold 0 * |cn|
  let Hc : ℝ := C * ((d : ℝ) ^ alpha + 1)
  have hB : 0 ≤ B := add_nonneg (le_max_right _ _)
    (mul_nonneg (le_max_right _ _) (sq_nonneg _))
  have hC0 : 0 ≤ C := mul_nonneg (le_max_right _ _) (abs_nonneg _)
  have hHc : 0 ≤ Hc := mul_nonneg hC0
    (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) zero_le_one)
  refine ⟨B, Hc, hB, hHc, ?_⟩
  intro n w hw hwb
  have hacont : ContinuousOn (cutoffCoefficient M H (env n om) (cutoff n))
      (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) :=
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (env n om) (cutoff n)).continuousOn
  have hapos (x : SpatialCoordinates d) :
      0 < cutoffCoefficient M H (env n om) (cutoff n) x :=
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (env n om) (cutoff n) x
  obtain ⟨lo, hi, hlo, _, hell⟩ := aux_thm_prop_weight_bounds_on (z j) (r j) (hr j)
    _ hacont (fun x _ => hapos x)
  have hEll := aux_prop_boundary_elliptic _ _ (centeredCube (z j) (r j) (hr j)).isOpen.measurableSet
    subset_closure _ hacont lo hi hlo hell
  have hActual := (hSol j n om hom).2 h
  have hUnique := aux_thm_prop_harmonic_cell_unique (z j) (r j) (hr j) _ hacont
    (fun x _ => hapos x) w (ucell j h n om) (thetaH1 j h)
    hw hwb hActual.1 hActual.2.1
  have hEnergy : energy (cutoffCoefficient M H (env n om) (cutoff n))
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) w =
        resp (cellResponseKey j h) n om := by
    rw [hActual.2.2.2.2]
    exact energy_eq_sInf_sameTrace_of_isWeaklyHarmonicOn
      (isOpenBoundedConvexDomain_ball (z j) (half_pos (hr j)))
      ⟨z j, Metric.mem_ball_self (half_pos (hr j))⟩ hEll hw hwb
  refine ⟨?_, ?_, (ucell j h n om).toFun, hActual.2.2.1, hUnique.1, ?_, ?_⟩
  · rw [hEnergy]
    exact (hResp (Set.mem_range_self n)).trans
      ((le_max_left _ _).trans (le_add_of_nonneg_right
        (mul_nonneg (le_max_right _ _) (sq_nonneg _))))
  · intro x hx rr hrr hrr1
    have hDensity :
        (fun y => ENNReal.ofReal (cutoffCoefficient M H (env n om) (cutoff n) y *
          ∑ i : Fin d, (w.grad y i) ^ 2)) =ᵐ[volume.restrict
          (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))]
        (fun y => ENNReal.ofReal ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n)
          (z j) (hr j)).val y *
            ∑ i : Fin d, ((sobolevDataOfH1 (ucell j h n om)).2 i y) ^ 2)) := by
      filter_upwards [hUnique.2,
        aux_lem_replace_large_cube_cutoff_positive_coe M H (env n om) (cutoff n) (z j) (hr j),
        ae_all_iff.mpr (fun i => sobolevDataOfH1_snd_coeFn (ucell j h n om) i)]
          with y hgrad hcoeff hData
      rw [hcoeff, hgrad]
      congr 2
      exact Finset.sum_congr rfl fun i _ => by rw [hData i]
    rw [withDensity_congr_ae hDensity]
    refine ((hCellEst j h n om hom).1 x hx rr hrr hrr1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hgrow : constants (cellGrowthKey j h) n om ≤ max Bgrow 0 :=
      (le_abs_self _).trans ((hGrow n).trans (le_max_left _ _))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hrr.le _)
    exact (mul_le_mul_of_nonneg_right hgrow (sq_nonneg cn)).trans
      (le_add_of_nonneg_left (le_max_right Bresp 0))
  · have hNorm : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (ucell j h n om).toFun ≤ C := by
      refine (hCellEst j h n om hom).2.2.trans ?_
      exact (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_right ((hHold n).trans (le_max_left _ _)) (abs_nonneg cn)))
    have hb := (aux_thm_prop_holder_metric_bounds _ (lane2_isCompact_closure_centeredCube (z j) (hr j))
      _ hActual.2.2.1 alpha (by linarith [hBeta.1, hBeta.2])
      (hCellEst j h n om hom).2.1 C hNorm).2
    intro x hx y hy
    refine (hb x hx y hy).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _))
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hC0
  · have hNorm : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (ucell j h n om).toFun ≤ C := by
      refine (hCellEst j h n om hom).2.2.trans ?_
      exact (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_right ((hHold n).trans (le_max_left _ _)) (abs_nonneg cn)))
    have hb := (aux_thm_prop_holder_metric_bounds _ (lane2_isCompact_closure_centeredCube (z j) (hr j))
      _ hActual.2.2.1 alpha (by linarith [hBeta.1, hBeta.2])
      (hCellEst j h n om hom).2.1 C hNorm).1
    intro x hx
    exact (hb x hx).trans (by
      dsimp only [Hc]
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg d) alpha])

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The energy bound makes the full patch range relatively compact. -/
theorem aux_thm_prop_patch_range_compact
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    (uN : ℕ → S.space) (E0 : ℝ)
    (hEnergy : ∀ n, responseForm S (a n) (uN n) (uN n) ≤ E0) :
    IsCompact (closure (Set.range fun n => (uN n).val.1)) := by
  apply isCompact_closure_of_subseq_tendsto
  intro v hv
  choose ns hns using hv
  obtain ⟨sigma, u, hsigma, hu⟩ := aux_thm_prop_patch_compactness
    (aux_thm_prop_controls_reindex A ns) (fun n => uN (ns n)) E0 (fun n => hEnergy (ns n))
  refine ⟨u, sigma, hsigma, ?_⟩
  exact hu.congr fun n => hns (sigma n)

/-- One subsequence works for the countable smooth catalogue of actual patches.
This is extraction, not a full-sequence convergence assumption. -/
theorem aux_thm_prop_patch_family_cluster
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_thm_prop_analytic_controls d hd z r hr S a)
    {J : Type} [Countable J] (uN : J → ℕ → S.space) (E0 : J → ℝ)
    (hEnergy : ∀ j n, responseForm S (a n) (uN j n) (uN j n) ≤ E0 j) :
    ∃ (sigma : ℕ → ℕ) (u : J → DomainL2 (centeredCube z r hr)), StrictMono sigma ∧
      ∀ j, Tendsto (fun n => (uN j (sigma n)).val.1) atTop (𝓝 (u j)) := by
  have hProd : IsCompact {v : J → DomainL2 (centeredCube z r hr) |
      ∀ j, v j ∈ closure (Set.range fun n => (uN j n).val.1)} :=
    isCompact_pi_infinite fun j => aux_thm_prop_patch_range_compact A (uN j) (E0 j) (hEnergy j)
  obtain ⟨u, _hu, sigma, hsigma, hconv⟩ := hProd.tendsto_subseq
    (fun n j => subset_closure (Set.mem_range_self n))
  exact ⟨sigma, u, hsigma, fun j => ((continuous_apply j).tendsto u).comp hconv⟩

/-- The actual finite mesh has one harmonic patch in L² for a fixed trace.
Null grid faces are handled by the proved open-cell partition. -/
theorem aux_thm_prop_patch_unique
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (m : ℕ)
    (a : SpatialCoordinates d → ℝ)
    (ha : ContinuousOn a (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < a x)
    (u v b : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hu : ∀ k : OddGridIndex d m,
      IsWeaklyHarmonicOn a (oddGridCell z r hr m k : Set (SpatialCoordinates d))
        (u.restrict (oddGridCell z r hr m k).isOpen (oddGridCell_subset z hr m k)) ∧
      HasZeroTraceDifferenceOn (oddGridCell z r hr m k : Set (SpatialCoordinates d))
        (u.restrict (oddGridCell z r hr m k).isOpen (oddGridCell_subset z hr m k))
        (b.restrict (oddGridCell z r hr m k).isOpen (oddGridCell_subset z hr m k)))
    (hv : ∀ k : OddGridIndex d m,
      IsWeaklyHarmonicOn a (oddGridCell z r hr m k : Set (SpatialCoordinates d))
        (v.restrict (oddGridCell z r hr m k).isOpen (oddGridCell_subset z hr m k)) ∧
      HasZeroTraceDifferenceOn (oddGridCell z r hr m k : Set (SpatialCoordinates d))
        (v.restrict (oddGridCell z r hr m k).isOpen (oddGridCell_subset z hr m k))
        (b.restrict (oddGridCell z r hr m k).isOpen (oddGridCell_subset z hr m k))) :
    (sobolevDataOfH1 u).1 = (sobolevDataOfH1 v).1 := by
  have heq (k : OddGridIndex d m) :
      ∀ᵐ x ∂volume, x ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d)) →
        u.toFun x = v.toFun x := by
    apply (ae_restrict_iff' (oddGridCell z r hr m k).isOpen.measurableSet).mp
    exact (aux_thm_prop_harmonic_cell_unique _ _ _ a
      (ha.mono (closure_mono (oddGridCell_subset z hr m k)))
      (fun x hx => hpos x ((closure_mono (oddGridCell_subset z hr m k)) hx))
      _ _ _ (hu k).1 (hu k).2 (hv k).1 (hv k).2).1
  apply Lp.ext
  filter_upwards [sobolevDataOfH1_fst_coeFn u, sobolevDataOfH1_fst_coeFn v,
    ae_restrict_of_ae (ae_all_iff.mpr heq),
    ae_restrict_of_ae (oddGrid_union_ae_eq z hr m),
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hux hvx hcells hcover hx
  rw [hux, hvx]
  have hxU : x ∈ ⋃ k : OddGridIndex d m, (oddGridCell z r hr m k : Set (SpatialCoordinates d)) := by
    exact Eq.mp hcover.symm hx
  obtain ⟨k, hk⟩ := mem_iUnion.mp hxU
  exact hcells k hk

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- Construct the common smooth-catalogue L² subsequence from actual finite
mesh solutions and controls. Uniqueness transfers it to every representative
of the same finite-cutoff patch problem. -/
theorem aux_thm_prop_smooth_catalogue_cluster
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
          Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (alpha t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (Catalog : Set (SpatialCoordinates d → ℝ))
    (hCatalog : ∀ Phi ∈ Catalog,
      ContDiff ℝ ∞ Phi ∧ HasCompactSupport Phi ∧
        tsupport Phi ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hCatalogBounds : ∀ Phi, Phi ∈ Catalog →
      ∀ PhiH : H1Function
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        PhiH.toFun = Phi →
        ∃ Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ,
          (∀ k : OddGridIndex d (triadicHalf 1),
            0 ≤ Bcell k ∧ 0 ≤ Hcell k) ∧
          ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1))
            (w : H1Function
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))),
            IsWeaklyHarmonicOn (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w →
            HasZeroTraceDifferenceOn
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w
              (PhiH.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)) →
            energy (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w ≤
              Bcell k ∧
            (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
                ((volume.restrict
                  ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))).withDensity
                  (fun y => ENNReal.ofReal ((A n) y *
                    ∑ i : Fin d, (w.grad y i) ^ 2)))
                  (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t)) ∧
            ∃ wc : SpatialCoordinates d → ℝ,
              ContinuousOn wc
                (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) ∧
              w.toFun =ᵐ[volume.restrict
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))] wc ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                ∀ y ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                  |wc x - wc y| ≤ Hcell k * dist x y ^ alpha) ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                |wc x| ≤ Hcell k))
    (hCountable : Catalog.Countable)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (haC : ∀ n : ℕ, (aC n).val =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] A n)
    (Controls : aux_thm_prop_analytic_controls d hd z (3 * r) h3r S aC) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
    ∀ Phi, Phi ∈ Catalog →
      ∀ PhiH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        PhiH.toFun = Phi →
        ∀ (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
          (UNS : ℕ → S.space),
          (∀ n : ℕ, (UNS n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (UN n)) →
          (∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
            IsWeaklyHarmonicOn (A (sigma n))
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
            HasZeroTraceDifferenceOn
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
              (PhiH.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))) →
          ∃ uBar : DomainL2 (centeredCube z (3 * r) h3r),
            Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let : Countable Catalog := Set.countable_coe_iff.mpr hCountable
  have hmesh := prop_gluing_smooth_mesh d hd z r hr h3r hcellsub alpha t ht htd S hS A hAcont hell
    Catalog hCatalog hCatalogBounds
  choose PhiH Phiq UN UNS Bcell Hcell hPhiH hPhiq hBH hUN hEn hGr hHo using
    fun p : Catalog => hmesh p.val p.property
  have hEnergy (p : Catalog) : ∃ E0 : ℝ,
      ∀ n, responseForm S (aC n) (UNS p n) (UNS p n) ≤ E0 :=
    aux_prop_boundary_energy_bound z r h3r S A aC hAcont haC (UN p) (UNS p)
      (fun n => (hUN p n).1) hcellsub (Bcell p) (hEn p)
  choose E0 hE0 using hEnergy
  obtain ⟨sigma, u, hsigma, hlim⟩ := aux_thm_prop_patch_family_cluster Controls UNS E0 hE0
  refine ⟨sigma, hsigma, ?_⟩
  intro Phi hPhi PhiH' hPhiH' UN' UNS' hUNrep' hUNcell'
  let p : Catalog := ⟨Phi, hPhi⟩
  have heq (n : ℕ) : (UNS' n).val.1 = (UNS p (sigma n)).val.1 := by
    rw [hUNrep', (hUN p (sigma n)).1]
    apply aux_thm_prop_patch_unique z (3 * r) h3r (triadicHalf 1) (A (sigma n))
      (hAcont (sigma n)) (fun x hx => by obtain ⟨lo, hi, hlo, hb⟩ := hell (sigma n); exact hlo.trans_le (hb x hx).1)
      (UN' n) (UN p (sigma n)) (PhiH p)
    · intro k
      refine ⟨(hUNcell' n k).1, ?_⟩
      exact aux_prop_boundary_trace_rebase _ (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
        (centeredCube_isBounded _ _)
        _ _ _ (hPhiH'.trans (hPhiH p).symm) (hUNcell' n k).2
    · intro k
      exact ⟨((hUN p (sigma n)).2.2.2 k).1, ((hUN p (sigma n)).2.2.2 k).2.1⟩
  exact ⟨u p, (hlim p).congr fun n => (heq n).symm⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- Literal finite-cutoff estimates with a function-valued datum, so equality
of catalogue cubes and choices of the H1 carrier can be transported directly. -/
def aux_thm_prop_cell_control {d : ℕ}
    (a : ℕ → SpatialCoordinates d → ℝ) (q : Set (SpatialCoordinates d))
    (phi : SpatialCoordinates d → ℝ) (alpha t : ℝ) : Prop :=
  ∃ B Hc : ℝ, 0 ≤ B ∧ 0 ≤ Hc ∧
    ∀ (n : ℕ) (w b : H1Function q), b.toFun = phi →
      IsWeaklyHarmonicOn (a n) q w → HasZeroTraceDifferenceOn q w b →
      energy (a n) q w ≤ B ∧
      (∀ x ∈ closure q, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict q).withDensity
          (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, (w.grad y i) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)) ∧
      ∃ wc : SpatialCoordinates d → ℝ,
        ContinuousOn wc (closure q) ∧ (w.toFun =ᵐ[volume.restrict q] wc) ∧
        (∀ x ∈ closure q, ∀ y ∈ closure q,
          |wc x - wc y| ≤ Hc * dist x y ^ alpha) ∧
        (∀ x ∈ closure q, |wc x| ≤ Hc)

theorem aux_thm_prop_represented_cell_control
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
    (h : T j) :
    aux_thm_prop_cell_control
      (fun n => cutoffCoefficient M H (env n om) (cutoff n))
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))
      (theta j h) alpha t := by
  have hRepCopy := hRep
  rcases hRepCopy with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTrace, _⟩
  have hTraceFun : (thetaH1 j h).toFun = theta j h := (hTrace j h).2
  obtain ⟨B, Hc, hB, hHc, hbound⟩ := aux_thm_prop_represented_cell_bounds
    d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell
    Cext beta alpha eta t orders E Index resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRep om hom j h
  refine ⟨B, Hc, hB, hHc, ?_⟩
  intro n w b hb hw hwb
  exact hbound n w hw (aux_prop_boundary_trace_rebase _
    (centeredCube (z j) (r j) (hr j)).isOpen (centeredCube_isBounded _ _) w b (thetaH1 j h)
    (hb.trans hTraceFun.symm) hwb)

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Completeness of the actual bounded catalogue supplies all cells of the
one-step mesh inside a catalogue cube. No outside-root cube is requested. -/
theorem aux_thm_prop_catalogue_mesh_indices
    {d : ℕ} {J : Type} (j0 : J) (z : J → SpatialCoordinates d) (r : J → ℝ)
    (hr : ∀ j, 0 < r j)
    (hcontain : ∀ j, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)))
    (hrat : ∀ j i, ∃ q : ℚ, z j i = (q : ℝ))
    (htri : ∀ j, ∃ k : ℤ, r j = (3 : ℝ) ^ k)
    (hcomplete : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      (∀ i, ∃ q : ℚ, zc i = (q : ℝ)) → (∃ k : ℤ, rc = (3 : ℝ) ^ k) →
      (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) →
      ∃ j, z j = zc ∧ r j = rc)
    (jQ : J) (rq : ℝ) (hrq : 0 < rq) (h3rq : 0 < 3 * rq) (hrQ : r jQ = 3 * rq) :
    ∃ idx : OddGridIndex d (triadicHalf 1) → J,
      ∀ k, z (idx k) = oddGridCenter (z jQ) (3 * rq) (triadicHalf 1) k ∧
        r (idx k) = rq ∧
        (centeredCube (z (idx k)) (r (idx k)) (hr (idx k)) : Set (SpatialCoordinates d)) =
          (oddGridCell (z jQ) (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)) := by
  classical
  obtain ⟨exponent, hexponent⟩ := htri jQ
  have htriSmall : rq = (3 : ℝ) ^ (exponent - 1) := by
    have he : rq = r jQ / 3 := by rw [hrQ]; ring
    rw [he, hexponent, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hratLarge : ∃ q : ℚ, 3 * rq = (q : ℝ) := by
    refine ⟨(3 : ℚ) ^ exponent, ?_⟩
    rw [← hrQ, hexponent]
    simp only [Rat.cast_zpow, Rat.cast_ofNat]
  have hqRoot : (centeredCube (z jQ) (3 * rq) h3rq : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) := by
    simpa only [hrQ] using hcontain jQ
  have hindices (k : OddGridIndex d (triadicHalf 1)) :
      ∃ j, z j = oddGridCenter (z jQ) (3 * rq) (triadicHalf 1) k ∧ r j = rq := by
    apply hcomplete _ rq hrq
    · exact aux_in_represented_catalogue_ratCoord_oddGridCenter d (triadicHalf 1)
        (z jQ) (3 * rq) k (hrat jQ) hratLarge
    · exact ⟨exponent - 1, htriSmall⟩
    · rw [← aux_prop_gluing_cell_eq (z jQ) rq hrq h3rq k]
      exact (oddGridCell_subset (z jQ) h3rq (triadicHalf 1) k).trans hqRoot
  choose idx hzidx hridx using hindices
  refine ⟨idx, fun k => ⟨hzidx k, hridx k, ?_⟩⟩
  simpa only [hzidx k, hridx k] using
    (aux_prop_gluing_cell_eq (z jQ) rq hrq h3rq k).symm

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- Every smooth source in a represented parent catalogue has actual cell
controls on the complete one-step mesh inside that parent. -/
theorem aux_thm_prop_represented_mesh_control
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
    (om : Ω) (hom : om ∈ G) (jQ : J)
    (rq : ℝ) (hrq : 0 < rq) (h3rq : 0 < 3 * rq) (hrQ : r jQ = 3 * rq) :
    ∀ Phi ∈ Set.range (f jQ), ∀ k : OddGridIndex d (triadicHalf 1),
      aux_thm_prop_cell_control
        (fun n => cutoffCoefficient M H (env n om) (cutoff n))
        (oddGridCell (z jQ) (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))
        Phi alpha t := by
  have hRepCopy := hRep
  rcases hRepCopy with ⟨_, _, _, _, _, _, _, _, _, _,
    hcontain, hrat, htri, hcomplete, _, _, _, _, _, _, _, hSt, hParent, _⟩
  obtain ⟨idx, hidx⟩ := aux_thm_prop_catalogue_mesh_indices j0 z r hr
    hcontain hrat htri hcomplete jQ rq hrq h3rq hrQ
  rintro Phi ⟨g, rfl⟩ k
  obtain ⟨h, hh⟩ := hSt jQ g
  have hsub :
      (centeredCube (z (idx k)) (r (idx k)) (hr (idx k)) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) := by
    simpa only [(hidx k).2.2, hrQ] using
      oddGridCell_subset (z jQ) h3rq (triadicHalf 1) k
  obtain ⟨h', hh'⟩ := hParent jQ (idx k) hsub h
  have hcontrol := aux_thm_prop_represented_cell_control
    d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell
    Cext beta alpha eta t orders E Index resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRep om hom (idx k) h'
  simpa only [(hidx k).2.2, hh', hh] using hcontrol

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

def aux_thm_prop_mesh_controls
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (A : ℕ → SpatialCoordinates d → ℝ) (Catalog : Set (SpatialCoordinates d → ℝ))
    (alpha t : ℝ) : Prop :=
  ∀ Phi, Phi ∈ Catalog →
      ∀ PhiH : H1Function
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        PhiH.toFun = Phi →
        ∃ Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ,
          (∀ k : OddGridIndex d (triadicHalf 1),
            0 ≤ Bcell k ∧ 0 ≤ Hcell k) ∧
          ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1))
            (w : H1Function
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))),
            IsWeaklyHarmonicOn (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w →
            HasZeroTraceDifferenceOn
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w
              (PhiH.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)) →
            energy (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w ≤
              Bcell k ∧
            (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
                ((volume.restrict
                  ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))).withDensity
                  (fun y => ENNReal.ofReal ((A n) y *
                    ∑ i : Fin d, (w.grad y i) ^ 2)))
                  (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t)) ∧
            ∃ wc : SpatialCoordinates d → ℝ,
              ContinuousOn wc
                (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) ∧
              w.toFun =ᵐ[volume.restrict
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))] wc ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                ∀ y ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                  |wc x - wc y| ≤ Hcell k * dist x y ^ alpha) ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                |wc x| ≤ Hcell k)

/-- Function-valued cell controls supply the exact native smooth-mesh estimates. -/
theorem aux_thm_prop_mesh_controls_of_cells
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (A : ℕ → SpatialCoordinates d → ℝ) (Catalog : Set (SpatialCoordinates d → ℝ))
    (alpha t : ℝ)
    (hcontrol : ∀ Phi ∈ Catalog, ∀ k : OddGridIndex d (triadicHalf 1),
      aux_thm_prop_cell_control A
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) Phi alpha t) :
    aux_thm_prop_mesh_controls z r h3r hcellsub A Catalog alpha t := by
  intro Phi hPhi PhiH hPhiH
  choose Bcell Hcell hBcell hHcell hbound using hcontrol Phi hPhi
  refine ⟨Bcell, Hcell, fun k => ⟨hBcell k, hHcell k⟩, ?_⟩
  intro n k w hw htrace
  exact hbound k n w
    (PhiH.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
    hPhiH hw htrace

/-- All-radius growth remains valid when the exponent is lowered. -/
theorem aux_thm_prop_mesh_controls_lower_exponent
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (A : ℕ → SpatialCoordinates d → ℝ) (Catalog : Set (SpatialCoordinates d → ℝ))
    (alpha t : ℝ)
    (hcontrol : aux_thm_prop_mesh_controls z r h3r hcellsub A Catalog alpha t)
    (s : ℝ) (hst : s ≤ t) :
    aux_thm_prop_mesh_controls z r h3r hcellsub A Catalog alpha s := by
  intro Phi hPhi PhiH hPhiH
  obtain ⟨Bcell, Hcell, hBH, hbound⟩ := hcontrol Phi hPhi PhiH hPhiH
  refine ⟨Bcell, Hcell, hBH, ?_⟩
  intro n k w hw htrace
  obtain ⟨he, hg, hh⟩ := hbound n k w hw htrace
  exact ⟨he, fun x hx rr hrr hrr1 =>
    aux_thm_prop_growth_lower_exponent (hBH k).1 hrr hrr1 hst (hg x hx rr hrr hrr1), hh⟩

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


/-- The smooth boundary package supplied by actual response convergence and
controls, including its limiting representative, minimum and energy convergence. -/
theorem aux_thm_prop_controlled_catalogue_package
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
    (hCatalogL2 : ∀ Phi, Phi ∈ Catalog →
      ∀ PhiH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        PhiH.toFun = Phi →
        ∀ (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
          (UNS : ℕ → S.space),
          (∀ n : ℕ, (UNS n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (UN n)) →
          (∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
            IsWeaklyHarmonicOn (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
            HasZeroTraceDifferenceOn
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
              (PhiH.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))) →
          ∃ uBar : DomainL2 (centeredCube z (3 * r) h3r),
            Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (Phi : SpatialCoordinates d → ℝ) (hPhi : Phi ∈ Catalog) :
    ∃ (PhiH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (Phiq : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
      (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (UNS : ℕ → S.space)
      (U : DomainL2 (centeredCube z (3 * r) h3r)) (Uc : SpatialCoordinates d → ℝ),
      PhiH.toFun = Phi ∧ Phiq.toFun = Phi ∧
      (∀ n : ℕ,
        (UNS n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (UN n) ∧
        ContinuousOn (UN n).toFun
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          (UN n).toFun x = 0) ∧
        ∀ k : OddGridIndex d (triadicHalf 1),
          IsWeaklyHarmonicOn (A n)
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
            ((UN n).restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k)) ∧
          HasZeroTraceDifferenceOn
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
            ((UN n).restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k))
            (PhiH.restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k)) ∧
          ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
            (UN n).toFun x = Phi x) ∧
      U ∈ E.domain ∧
      ContinuousOn Uc
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (U : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Uc x = Phi x) ∧
      Gamma.measure U (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 ∧
      (∀ φ : DomainL2 (centeredCube z (3 * r) h3r), φ ∈ Dq → E.form U φ = 0) ∧
      Tendsto (fun n => cellDirichletInfimum (A n)
        (centeredCube z r hr : Set (SpatialCoordinates d)) Phiq) atTop
        (𝓝 ((Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) ∧
      (∀ V : DomainL2 (centeredCube z (3 * r) h3r),
        V ∈ E.domain →
        ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (V : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = Phi x) →
        (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  have hMosco := aux_thm_prop_controlled_mosco hS Controls GN G hGN hConv
  have hMeasures := aux_thm_prop_energy_measure_convergence BD BDQ EM hcontract hS Controls
    GN G hGN hConv E hE hcore Gamma
  have hdom := aux_thm_prop_domain_eq_of_energy E.toClosedForm G hE
  exact aux_prop_gluing_catalog_package d hd z r hr h3r hcellsub beta alpha hbeta hba ha1
    S hS A hAcont aC haC hell E.toClosedForm Gamma
    (by
      intro vN v hv
      rw [hE]
      apply hMosco.lower vN v
      intro w
      simpa only [aux_prop_gluing_inner_eq_integral] using hv w)
    (by simpa only [← hdom, ← hE] using! hMosco.recovery)
    Dq hDq ⟨E, rfl⟩ Controls.t Controls.t_lower Controls.t_upper
    (fun _ => Controls.K) (fun _ => Controls.K_pos.le) Controls.K (fun _ => le_rfl)
    (fun w => (Controls.coercive 0 w).1) (fun n w => (Controls.coercive n w).2)
    Controls.interpolation Controls.cutoffs hMeasures
    (fun zc rc hrc hsub D hD w hw wc hwc hrep hzero wq hwq =>
      aux_thm_prop_boundary_truncation d hd z zc (3 * r) rc h3r hrc hsub
        E Gamma hcore D hD w hw wc hwc hrep hzero wq hwq)
    (fun _ => ⟨_, aux_thm_prop_isKilledDomain _ _⟩)
    Catalog hCatalog
    (aux_thm_prop_mesh_controls_lower_exponent z r h3r hcellsub A Catalog alpha t
      hCatalogBounds Controls.t htControl)
    hCatalogL2 Phi hPhi

end Standing
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


/-- One common cutoff subsequence carries the complete boundary package for
every datum of a countable smooth catalogue. -/
theorem aux_thm_prop_countable_catalogue_package
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
    (hCountable : Catalog.Countable) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∀ Phi ∈ Catalog,
∃ (PhiH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (Phiq : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
      (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (UNS : ℕ → S.space)
      (U : DomainL2 (centeredCube z (3 * r) h3r)) (Uc : SpatialCoordinates d → ℝ),
      PhiH.toFun = Phi ∧ Phiq.toFun = Phi ∧
      (∀ n : ℕ,
        (UNS n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (UN n) ∧
        ContinuousOn (UN n).toFun
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          (UN n).toFun x = 0) ∧
        ∀ k : OddGridIndex d (triadicHalf 1),
          IsWeaklyHarmonicOn (A (sigma n))
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
            ((UN n).restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k)) ∧
          HasZeroTraceDifferenceOn
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
            ((UN n).restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k))
            (PhiH.restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k)) ∧
          ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
            (UN n).toFun x = Phi x) ∧
      U ∈ E.domain ∧
      ContinuousOn Uc
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (U : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Uc x = Phi x) ∧
      Gamma.measure U (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 ∧
      (∀ φ : DomainL2 (centeredCube z (3 * r) h3r), φ ∈ Dq → E.form U φ = 0) ∧
      Tendsto (fun n => cellDirichletInfimum (A (sigma n))
        (centeredCube z r hr : Set (SpatialCoordinates d)) Phiq) atTop
        (𝓝 ((Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) ∧
      (∀ V : DomainL2 (centeredCube z (3 * r) h3r),
        V ∈ E.domain →
        ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (V : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = Phi x) →
        (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  obtain ⟨sigma, hsigma, hL2⟩ := aux_thm_prop_smooth_catalogue_cluster d hd z r hr h3r
    hcellsub alpha Controls.t Controls.t_lower Controls.t_upper S hS A hAcont hell Catalog hCatalog
    (aux_thm_prop_mesh_controls_lower_exponent z r h3r hcellsub A Catalog alpha t
      hCatalogBounds Controls.t htControl) hCountable aC haC Controls
  refine ⟨sigma, hsigma, ?_⟩
  intro Phi hPhi
  apply aux_thm_prop_controlled_catalogue_package BD BDQ EM hcontract z r hr h3r hcellsub
    beta alpha hbeta hba ha1 S hS (fun n => A (sigma n)) (fun n => hAcont (sigma n))
    (fun n => aC (sigma n)) (fun n => haC (sigma n)) (fun n => hell (sigma n))
    E Gamma (aux_thm_prop_controls_reindex Controls sigma) (fun n => GN (sigma n)) G
    (fun n => hGN (sigma n)) (hConv.comp hsigma.tendsto_atTop) hE hcore Dq hDq t htControl
    Catalog hCatalog _ hL2 Phi hPhi
  intro Phi' hPhi' PhiH hPhiH
  obtain ⟨Bcell, Hcell, hBH, hbound⟩ := hCatalogBounds Phi' hPhi' PhiH hPhiH
  exact ⟨Bcell, Hcell, hBH, fun n => hbound (sigma n)⟩

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- Global value and derivative bounds give a genuine Hölder bound, with a
constant uniform over the domain of the norm. -/
theorem aux_thm_prop_c1_holder_bound
    {d : ℕ} (f : SpatialCoordinates d → ℝ) (hf : Differentiable ℝ f)
    (B : ℝ) (hB : 0 ≤ B) (hval : ∀ x, |f x| ≤ B)
    (hder : ∀ x, ‖fderiv ℝ f x‖ ≤ B)
    (beta : ℝ) (hb : 0 < beta) (hb1 : beta < 1)
    (K : Set (SpatialCoordinates d)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta K f ∧ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K f ≤ 3 * B := by
  have hpair (x y : SpatialCoordinates d) : |f x - f y| ≤ (2 * B) * dist x y ^ beta := by
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, abs_zero]
      positivity
    have hr : 0 < dist x y := dist_pos.mpr hxy
    by_cases hdist : dist x y ≤ 1
    · have hLip : |f x - f y| ≤ B * dist x y := by
        simpa only [Real.norm_eq_abs, dist_eq_norm] using
          Convex.norm_image_sub_le_of_norm_fderiv_le (fun u (_ : u ∈ (Set.univ : Set (SpatialCoordinates d))) => hf u)
            (fun u _ => hder u) convex_univ (Set.mem_univ y) (Set.mem_univ x)
      have hpow : dist x y ≤ dist x y ^ beta := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hdist hb1.le
      exact hLip.trans ((mul_le_mul_of_nonneg_left hpow hB).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _)))
    · have hpow : 1 ≤ dist x y ^ beta := Real.one_le_rpow (le_of_not_ge hdist) hb.le
      have habs : |f x - f y| ≤ |f x| + |f y| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (f x) (f y)
      have hv := habs.trans (add_le_add (hval x) (hval y))
      simpa only [sub_zero] using hv.trans (by nlinarith : B + B ≤ 2 * B * dist x y ^ beta)
  constructor
  · refine ⟨2 * B, ?_⟩
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    have hepos := aux_prop_gluing_euclid_pos x y hxy
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hepos beta)).mpr
    have he : dist x y ≤ Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) := by
      simpa only [euclideanNorm, vecNormSq, vecDot, Pi.sub_apply, ← pow_two, dist_eq_norm]
        using norm_le_euclideanNorm (x - y)
    exact (hpair x y).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg he hb.le) (by positivity))
  · calc
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K f ≤ B + 2 * B :=
        aux_lem_skeleton_smooth_approx_cAlpha_bound beta hb K f B (2 * B) hB
          (by positivity) (fun x _ => hval x) (fun x _ y _ => hpair x y)
      _ = 3 * B := by ring

/-- The source catalogue's uniform derivative convergence supplies the exact
Hölder-norm convergence needed by the boundary completion. -/
theorem aux_thm_prop_c1_uniform_holder_convergence
    {d : ℕ} (f : ℕ → SpatialCoordinates d → ℝ)
    (hf : ∀ n, Differentiable ℝ (f n))
    (h0 : TendstoUniformly f (fun _ => 0) atTop)
    (h1 : TendstoUniformly (fun n x => fderiv ℝ (f n) x) (fun _ => 0) atTop)
    (beta : ℝ) (hb : 0 < beta) (hb1 : beta < 1)
    (K : Set (SpatialCoordinates d)) :
    Tendsto (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K (f n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [Metric.tendstoUniformly_iff.mp h0 (eps / 4) (by positivity),
    Metric.tendstoUniformly_iff.mp h1 (eps / 4) (by positivity)] with n hn0 hn1
  have hbound := (aux_thm_prop_c1_holder_bound (f n) (hf n) (eps / 4) (by positivity)
    (fun x => by simpa only [dist_zero_left, Real.norm_eq_abs] using (hn0 x).le)
    (fun x => by simpa only [dist_zero_left] using (hn1 x).le)
    beta hb hb1 K).2
  have hnonneg := aux_prop_gluing_cAlphaNorm_nonneg beta K (f n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- A pointwise zero boundary function is in the genuine boundary class and
has zero quotient seminorm. -/
theorem aux_thm_prop_boundary_zero_class
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (beta : ℝ)
    (g : SpatialCoordinates d → ℝ)
    (hg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = 0) :
    IsCellBoundaryClass beta z r g ∧ cellBoundaryQuotientNorm beta z r g = 0 := by
  have hz : ∀ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), rescaledDatum z r g x = 0 :=
    fun x hx => hg _ (aux_prop_gluing_rescale_mem_frontier z r hr x hx)
  constructor
  · constructor
    · refine ⟨0, ?_⟩
      rintro v ⟨x, hx, y, hy, hxy, rfl⟩
      rw [hz x hx, hz y hy]
      simp
    · refine ⟨0, ?_⟩
      rintro v ⟨x, hx, rfl⟩
      rw [hz x hx]
      simp
  · apply le_antisymm _ (aux_prop_gluing_quotientNorm_nonneg beta z r g)
    have hc : cellBoundaryQuotientNorm beta z r g ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
        (rescaledDatum z r g) := by
      unfold cellBoundaryQuotientNorm quotientCBetaNorm
      apply csInf_le
      · exact ⟨0, by rintro v ⟨c, rfl⟩; exact aux_prop_gluing_cAlphaNorm_nonneg _ _ _⟩
      · exact ⟨0, by simp⟩
    apply hc.trans
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
    have hval : sSup {v : ℝ | ∃ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), v = |rescaledDatum z r g x|} ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro v ⟨x, hx, rfl⟩
      rw [hz x hx]
      simp
    have hratio : sSup (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
        (rescaledDatum z r g)) ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro v ⟨x, hx, y, hy, hxy, rfl⟩
      rw [hz x hx, hz y hy]
      simp
    linarith

/-- The actual extension estimate identifies scalar responses of continuous
H1 data that agree on the boundary. -/
theorem aux_thm_prop_boundary_response_eq
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (beta : ℝ)
    (a : SpatialCoordinates d → ℝ) (Lam K : ℝ) (hK : 0 ≤ K)
    (ha0 : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ a x)
    (haLam : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), a x ≤ Lam)
    (hameas : AEStronglyMeasurable a
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hExt : ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta z r e.toFun →
      cellDirichletInfimum a (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
        K * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
    (u v : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hu : ContinuousOn u.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hv : ContinuousOn v.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hboundary : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      u.toFun x = v.toFun x) :
    cellDirichletInfimum a (centeredCube z r hr : Set (SpatialCoordinates d)) u =
      cellDirichletInfimum a (centeredCube z r hr : Set (SpatialCoordinates d)) v := by
  obtain ⟨hclass, hnorm⟩ := aux_thm_prop_boundary_zero_class z r hr beta (u.toFun - v.toFun)
    (fun x hx => by simp only [Pi.sub_apply, hboundary x hx, sub_self])
  have hclose := aux_thm_prop_boundary_response_close z r hr beta a Lam K hK
    ha0 haLam hameas hExt u v hu hv hclass
  rw [hnorm, mul_zero] at hclose
  have hs := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hclose (abs_nonneg _)))
  have heq := congrArg (fun x : ℝ => x ^ 2) hs
  simpa only [Real.sq_sqrt (aux_prop_gluing_infimum_nonneg _
    (centeredCube z r hr).isOpen.measurableSet a ha0 u),
    Real.sq_sqrt (aux_prop_gluing_infimum_nonneg _
      (centeredCube z r hr).isOpen.measurableSet a ha0 v)] using heq

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


/-- Complete the actual countable smooth boundary catalogue and identify
any prescribed scalar response limit with its true boundary-energy minimum. -/
theorem aux_thm_prop_boundary_glb_completion
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
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBsU : TendstoUniformly Bs B atTop)
    (hBsHol : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x))
    (hBsBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), v = |Bs k x - B x|})
    (hBsNorm : Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs k x - B x)) atTop (𝓝 0))
    (b : SpatialCoordinates d → ℝ)
    (hBb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x)
    (hBsCat : ∀ k, Bs k ∈ Catalog)
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
  classical
  let : NeZero d := ⟨by omega⟩
  have hbeta0 : 0 ≤ beta := by linarith
  have hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith)
  obtain ⟨sigma, hsigma, hpkg⟩ := aux_thm_prop_countable_catalogue_package
    BD BDQ EM hcontract z r hr h3r hcellsub beta alpha hbeta hba ha1 S hS A hAcont aC haC hell
    E Gamma Controls GN G hGN hConv hE hcore Dq hDq t htControl Catalog hCatalog
    hCatalogBounds hCountable
  choose PhiH Phiq W WS Uk Uck hPhiH hPhiq hW hUk1 hUk2 hUk3 hUk4 hUk5 hUk6 hUk7 hUk8 hUk9
    using fun k => hpkg (Bs k) (hBsCat k)
  let A' := fun n => A (sigma n)
  let aC' := fun n => aC (sigma n)
  let C' := aux_thm_prop_controls_reindex Controls sigma
  have hAcont' := fun n => hAcont (sigma n)
  have haC' := fun n => haC (sigma n)
  have hell' := fun n => hell (sigma n)
  have hUg' := fun k n => hUg k (sigma n)
  have hGridBound' := fun k n => hGridBound k (sigma n)
  obtain ⟨UN, UNS, hpatch, hUNcomp⟩ := aux_prop_gluing_holder_patches hd z r hr h3r hcellsub
    beta hbeta0 S A' hAcont' aC' haC' hell' C hC (fun k n => Ugrid k (sigma n)) UgridStar
    hUg' hGridBound' Bs B hBsU hBsHol hBsBdd hBsNorm PhiH hPhiH W WS hW
  have hUNq : ∀ n, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (UN n).toFun x = b x :=
    fun n x hx => (aux_prop_gluing_face_values_central z r hr h3r hcellsub A' (LinearMap.id) B
      (fun _ _ _ => rfl) UN UNS hpatch n x hx).trans (hBb x hx)
  obtain ⟨L', hL', hlL'⟩ := aux_prop_gluing_response z r hr h3r hqQ beta A' hAcont' hell'
    C UStar hC (fun n => Uq (sigma n)) (fun n => hUq (sigma n)) (fun n => hBound (sigma n))
    Bs B (fun k => (hCatalog _ (hBsCat k)).1.continuous) hBsHol hBsBdd hBsNorm Phiq hPhiq
    _ hUk8 UN (fun n => (hpatch n).2.1) (fun n x hx => (hUNq n x hx).trans (hBb x hx).symm)
  have hRespEq (n : ℕ) :
      cellDirichletInfimum (A' n) (centeredCube z r hr : Set (SpatialCoordinates d))
        ((UN n).restrict (centeredCube z r hr).isOpen hqQ) =
      cellDirichletInfimum (A' n) (centeredCube z r hr : Set (SpatialCoordinates d)) bq := by
    obtain ⟨lo, hi, hlo, hb⟩ := hell' n
    exact aux_thm_prop_boundary_response_eq z r hr beta (A' n) hi
      (C * Uq (sigma n) * r ^ ((d : ℝ) - 2))
      (mul_nonneg (mul_nonneg hC (hUq (sigma n)).1) (Real.rpow_nonneg hr.le _))
      (fun x hx => hlo.le.trans (hb x (subset_closure (hqQ hx))).1)
      (fun x hx => (hb x (subset_closure (hqQ hx))).2)
      (((hAcont' n).mono (fun x hx => subset_closure (hqQ hx))).aestronglyMeasurable
        (centeredCube z r hr).isOpen.measurableSet)
      (hBound (sigma n)) _ bq ((hpatch n).2.1.mono (closure_mono hqQ)) hbq
      (fun x hx => (hUNq n x hx).trans (hbqb x hx).symm)
  have hL : L' = L := tendsto_nhds_unique (hL'.congr hRespEq)
    (hResponse.comp hsigma.tendsto_atTop)
  have hMosco := aux_thm_prop_controlled_mosco hS C' (fun n => GN (sigma n)) G
    (fun n => hGN (sigma n)) (hConv.comp hsigma.tendsto_atTop)
  obtain ⟨U, Uc, hU, hUc, hUrep, _hUuniform, hUb, _hUface, _hUorth, hUE, hUmin⟩ :=
    aux_prop_gluing_limit_object hd z r hr h3r hqQ hcellsub beta hbeta0 S A' hAcont' aC' haC'
      hell' E.toClosedForm Gamma
      (by
        intro vN v hv
        rw [hE]
        apply hMosco.lower vN v
        intro w
        simpa only [aux_prop_gluing_inner_eq_integral] using hv w)
      Dq hDq C hC (fun k n => Ugrid k (sigma n)) UgridStar hUg' hGridBound'
      Bs B hBsU hBsHol hBsBdd hBsNorm b hBb PhiH hPhiH W WS hW Uk Uck
      hUk1 hUk2 hUk3 hUk4 hUk5 hUk6 hUk7 hUk9 UN hUNcomp L' hlL'
  have hmem : (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ∈
      aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm Gamma
        (centeredCube z r hr : Set (SpatialCoordinates d)) b :=
    ⟨U, Uc, hU, hUc, hUrep, hUb, rfl⟩
  have hleast : IsLeast (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      E.toClosedForm Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) b)
      (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    refine ⟨hmem, ?_⟩
    rintro e ⟨V, Vc, hV, hVc, hVrep, hVb, rfl⟩
    exact hUmin V hV Vc hVc hVrep hVb
  exact ⟨(hUE.trans hL) ▸ hleast.isGLB, ⟨_, hmem⟩⟩

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- The actual source-catalogue topology supplies all boundary-completion
approximation clauses, including genuine Hölder membership at every index. -/
theorem aux_thm_prop_smooth_source_approximation
    {d : ℕ} (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBs : ∀ n, ContDiff ℝ ∞ (Bs n)) (hB : ContDiff ℝ ∞ B)
    (hBssupp : ∀ n, HasCompactSupport (Bs n)) (hBsupp : HasCompactSupport B)
    (hderivs : ∀ k : ℕ, TendstoUniformly
      (fun n x => iteratedFDeriv ℝ k (fun y => Bs n y - B y) x) (fun _ => 0) atTop)
    (beta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta < 1)
    (K : Set (SpatialCoordinates d)) :
    TendstoUniformly Bs B atTop ∧
    (∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta K (fun x => Bs n x - B x)) ∧
    (∀ n, BddAbove {v : ℝ | ∃ x ∈ K, v = |Bs n x - B x|}) ∧
    Tendsto (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta K (fun x => Bs n x - B x)) atTop (𝓝 0) := by
  have h0 : TendstoUniformly (fun n x => Bs n x - B x) (fun _ => 0) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro eps heps
    filter_upwards [Metric.tendstoUniformly_iff.mp (hderivs 0) eps heps] with n hn x
    simpa only [dist_zero_left, norm_iteratedFDeriv_zero] using hn x
  have h1 : TendstoUniformly (fun n x => fderiv ℝ (fun y => Bs n y - B y) x)
      (fun _ => 0) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro eps heps
    filter_upwards [Metric.tendstoUniformly_iff.mp (hderivs 1) eps heps] with n hn x
    have heq : ‖fderiv ℝ (fun y => Bs n y - B y) x‖ =
        ‖iteratedFDeriv ℝ 1 (fun y => Bs n y - B y) x‖ := by
      simpa only [norm_iteratedFDeriv_zero] using
        (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := fun y => Bs n y - B y) (x := x))
    simpa only [dist_zero_left, heq] using hn x
  have hBounds (n : ℕ) : ∃ E L : ℝ, 0 ≤ E ∧ 0 ≤ L ∧
      (∀ x, |Bs n x - B x| ≤ E) ∧
      (∀ x, ‖fderiv ℝ (fun y => Bs n y - B y) x‖ ≤ L) := by
    obtain ⟨E, hE, hEval⟩ := lane2_exists_bound_of_compactSupport
      ((hBs n).continuous.sub hB.continuous) ((hBssupp n).sub hBsupp)
    obtain ⟨L, hL, hLval⟩ := lane2_exists_fderiv_bound ((hBs n).sub hB) ((hBssupp n).sub hBsupp)
    exact ⟨E, L, hE, hL, hEval, hLval⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Metric.tendstoUniformly_iff.mpr
    intro eps heps
    filter_upwards [Metric.tendstoUniformly_iff.mp h0 eps heps] with n hn x
    simpa only [dist_zero_left, Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using hn x
  · intro n
    obtain ⟨E, L, hE, hL, hEval, hLval⟩ := hBounds n
    exact (aux_thm_prop_c1_holder_bound _ (((hBs n).sub hB).differentiable (by norm_num))
      (E + L) (add_nonneg hE hL)
      (fun x => (hEval x).trans (le_add_of_nonneg_right hL))
      (fun x => (hLval x).trans (le_add_of_nonneg_left hE)) beta hbeta hbeta1 K).1
  · intro n
    obtain ⟨E, L, hE, hL, hEval, hLval⟩ := hBounds n
    refine ⟨E, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact hEval x
  · exact aux_thm_prop_c1_uniform_holder_convergence _
      (fun n => ((hBs n).sub hB).differentiable (by norm_num)) h0 h1 beta hbeta hbeta1 K

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- The finite parent mesh has the literal represented extension estimate,
with its actual random constants bounded uniformly before the cutoff index. -/
theorem aux_thm_prop_represented_mesh_extension
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
    (om : Ω) (hom : om ∈ G) (jQ : J)
    (rq : ℝ) (hrq : 0 < rq) (h3rq : 0 < 3 * rq) (hrQ : r jQ = 3 * rq) :
    ∃ (Ugrid : OddGridIndex d (triadicHalf 1) → ℕ → ℝ)
      (UgridStar : OddGridIndex d (triadicHalf 1) → ℝ),
      (∀ k n, 0 ≤ Ugrid k n ∧ Ugrid k n ≤ UgridStar k) ∧
      (∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      ∀ e : H1Function
          ((oddGridCell (z jQ) (3 * rq) h3rq (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)),
      ContinuousOn e.toFun
          (closure ((oddGridCell (z jQ) (3 * rq) h3rq (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (oddGridCenter (z jQ) (3 * rq) (triadicHalf 1) k) rq e.toFun →
      cellDirichletInfimum (cutoffCoefficient M H (env n om) (cutoff n))
          ((oddGridCell (z jQ) (3 * rq) h3rq (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) e ≤
        Cext * Ugrid k n * rq ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta
            (oddGridCenter (z jQ) (3 * rq) (triadicHalf 1) k) rq e.toFun ^ 2) := by
  rcases hRep with ⟨hA, hAlpha, hBeta, hC, hOrders, hN, hIR, hMeas, hLaw, hSeq,
    hcontain, hrat, htri, hcomplete, hgrat, hcover, hS, hDense, hSrc, hSrcDense,
    hTrace, hSt, hParent, hTDense, hPlateau, hMeasc, hMom, hNonneg, hSol, hCoeff,
    hCoerc, hExt, hGrid, hSrcEst, hCellEst⟩
  obtain ⟨idx, hidx⟩ := aux_thm_prop_catalogue_mesh_indices j0 z r hr
    hcontain hrat htri hcomplete jQ rq hrq h3rq hrQ
  choose B hB using fun k => hSeq.2.2.2.2 (extensionKey (idx k)) om hom
  refine ⟨fun k n => constants (extensionKey (idx k)) n om, fun k => max (B k) 0, ?_, ?_⟩
  · intro k n
    exact ⟨hNonneg _ om hom n, (le_abs_self _).trans ((hB k n).trans (le_max_left _ _))⟩
  · intro k n
    have hext := hExt (idx k) n om hom
    rw [(hidx k).2.2] at hext
    simpa only [(hidx k).1, (hidx k).2.1] using hext

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


/-- Smooth source density supplies the boundary approximation used to identify
the actual scalar response minimum. -/
theorem aux_thm_prop_smooth_boundary_glb
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
    (B : SpatialCoordinates d → ℝ) (hB : ContDiff ℝ ∞ B)
    (hBsupp : HasCompactSupport B)
    (hBQ : tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
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
  obtain ⟨Bs, hBsCat, hDerivs⟩ := hDense B hB hBsupp hBQ
  obtain ⟨hBsU, hBsHol, hBsBdd, hBsNorm⟩ := aux_thm_prop_smooth_source_approximation Bs B
    (fun n => (hCatalog _ (hBsCat n)).1) hB (fun n => (hCatalog _ (hBsCat n)).2.1) hBsupp
    hDerivs beta (by linarith) (hba.trans ha1) _
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

/-- Every smooth datum has a smooth compactly supported extension agreeing on
the whole closed inner cube; no membership in the limiting form is assumed. -/
theorem aux_thm_prop_smooth_collar
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (b : SpatialCoordinates d → ℝ) (hb : ContDiff ℝ ∞ b) :
    ∃ B : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧
      tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x := by
  have hqQ : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith))
  obtain ⟨K, hKcompact, hKclosed, hqK, hKQ⟩ := exists_compact_closed_between
    (lane2_isCompact_closure_centeredCube z hr) (centeredCube z (3 * r) h3r).isOpen hqQ
  obtain ⟨chi, hchiOne, hchiZero, _hchiRange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, SpatialCoordinates d)) isClosed_closure hqK
  have hchiSmooth : ContDiff ℝ ∞ chi := chi.contMDiff.contDiff
  have hsupp : tsupport (chi : SpatialCoordinates d → ℝ) ⊆ K :=
    closure_minimal (Function.support_subset_iff'.mpr hchiZero) hKclosed
  refine ⟨fun x => chi x * b x, hchiSmooth.mul hb, ?_, ?_, ?_⟩
  · exact hKcompact.of_isClosed_subset isClosed_closure (tsupport_mul_subset_left.trans hsupp)
  · exact tsupport_mul_subset_left.trans (hsupp.trans hKQ)
  · intro x hx
    change chi x * b x = b x
    rw [hchiOne.self_of_nhdsSet x hx, one_mul]

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- The actual variational minimum depends only on the gradient of the H1
boundary extension when its gradient is unchanged everywhere. -/
theorem aux_thm_prop_dirichlet_response_gradient_congr
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a : PositiveCoefficient Q) (b b' : weakSobolevGraph Q)
    (hgrad : b.val.2 = b'.val.2) : dirichletResponse S a b = dirichletResponse S a b' := by
  have heq : (fun w : S.space => sobolevCoefficientForm a (b.val + w.val) (b.val + w.val)) =
      (fun w : S.space => sobolevCoefficientForm a (b'.val + w.val) (b'.val + w.val)) := by
    funext w
    rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
    congr 1
    funext i
    congr 1
    funext x
    change a.val x * (((b.val.2 + w.val.2) i) x * ((b.val.2 + w.val.2) i) x) =
      a.val x * (((b'.val.2 + w.val.2) i) x * ((b'.val.2 + w.val.2) i) x)
    rw [hgrad]
  have hleast := dirichletResponse_isLeast S a b
  rw [heq] at hleast
  exact hleast.unique (dirichletResponse_isLeast S a b')

noncomputable def aux_thm_prop_affine_constant_H1
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : H1Function (Q : Set (SpatialCoordinates d)) :=
  aux_thm_prop_affine_H1 hQ p + H1Function.const c

theorem aux_thm_prop_affine_constant_H1_gradient
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d))) (p : Fin d → ℝ) (c : ℝ) :
    (sobolevDataOfH1 (aux_thm_prop_affine_constant_H1 hQ p c)).2 =
      (affineSobolevData hQ p 0).2 := by
  funext i
  apply Lp.ext
  filter_upwards [sobolevDataOfH1_snd_coeFn (aux_thm_prop_affine_constant_H1 hQ p c) i,
    domainConstantL2_coeFn (Ω := Q) (p i)] with x hnative hconstant
  change _ = domainConstantL2 (Ω := Q) (p i) x
  rw [hnative, hconstant]
  simp only [aux_thm_prop_affine_constant_H1, H1Function.add_grad, H1Function.grad_const,
    add_zero, aux_thm_prop_affine_H1]

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


/-- Identify each actual normalized affine response matrix with all affine
boundary-energy minima, including arbitrary additive constants. -/
theorem aux_thm_prop_affine_boundary_glb
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
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (aq : ℕ → PositiveCoefficient (centeredCube z r hr))
    (haq : ∀ n, (aq n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] A n)
    (Amat : Matrix (Fin d) (Fin d) ℝ)
    (hAffine : ∀ p : Fin d → ℝ,
      Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded z hr) hP (aq n) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ Amat.mulVec p))) :
    ∀ (p : Fin d → ℝ) (c : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm Gamma
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => (∑ i, p i * x i) + c))
        ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ Amat.mulVec p)) ∧
      (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm Gamma
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => (∑ i, p i * x i) + c)).Nonempty := by
  let : NeZero d := ⟨by omega⟩
  intro p c
  let bq := aux_thm_prop_affine_constant_H1 (centeredCube_isBounded z hr) p c
  have hbqfun : bq.toFun = fun x => affineSlope p x + c := rfl
  have hbqcont : ContinuousOn bq.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [hbqfun]
    exact ((affineSlope p).continuous.add continuous_const).continuousOn
  obtain ⟨B, hB, hBsupp, hBQ, hBb⟩ := aux_thm_prop_smooth_collar z r hr h3r
    (fun x => affineSlope p x + c) ((affineSlope p).contDiff.add contDiff_const)
  have hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith)
  have hnative (n : ℕ) : cellDirichletInfimum (A n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) bq =
      affineDirichletResponse (centeredCube_isBounded z hr) hP (aq n) p := by
    obtain ⟨lo, hi, hlo, hb⟩ := hell n
    have heq := aux_thm_prop_cell_response_eq_dirichlet hP (aq n) (A n) (haq n) hi
      (fun x hx => hlo.le.trans (hb x (subset_closure (hqQ hx))).1)
      (fun x hx => (hb x (subset_closure (hqQ hx))).2)
      (((hAcont n).mono (fun x hx => subset_closure (hqQ hx))).aestronglyMeasurable
        (centeredCube z r hr).isOpen.measurableSet) bq
    refine heq.trans (aux_thm_prop_dirichlet_response_gradient_congr (killedResponseSpace hP)
      (aq n) _ (affineSobolev (centeredCube_isBounded z hr) p 0) ?_)
    exact aux_thm_prop_affine_constant_H1_gradient (centeredCube_isBounded z hr) p c
  have hv0 : (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≠ 0 := by
    rw [centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
    positivity
  have hScalar : Tendsto (fun n => cellDirichletInfimum (A n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) bq) atTop
      (𝓝 ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal *
        (p ⬝ᵥ Amat.mulVec p))) := by
    simpa only [hnative, div_mul_cancel₀ _ hv0, mul_comm] using
      (hAffine p).mul_const (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  have hmin := aux_thm_prop_smooth_boundary_glb BD BDQ EM hcontract z r hr h3r hcellsub
    beta alpha hbeta hba ha1 S hS A hAcont aC haC hell E Gamma Controls GN G hGN hConv hE hcore
    Dq hDq t htControl Catalog hCatalog hCatalogBounds hCountable C hC Ugrid UgridStar hUg
    hGridBound UStar Uq hUq hBound hDense B hB hBsupp hBQ (fun x => affineSlope p x + c)
    (fun x hx => hBb x (frontier_subset_closure hx)) bq hbqcont (fun _ _ => rfl) _ hScalar
  simpa only [affineSlope_apply] using hmin

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/-- The actual smooth source catalogue supplies a countable boundary-completion
catalogue with its recorded topology of uniform convergence of every derivative. -/
theorem aux_thm_prop_source_catalogue
    {d : ℕ} {D : Type} [Countable D] (Q : Set (SpatialCoordinates d))
    (f : D → SpatialCoordinates d → ℝ)
    (hf : ∀ g, ContDiff ℝ ∞ (f g) ∧ HasCompactSupport (f g) ∧ tsupport (f g) ⊆ Q)
    (hdense : ∀ B : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ B → HasCompactSupport B → tsupport B ⊆ Q →
      ∃ K : Set (SpatialCoordinates d), ∃ g : ℕ → D,
        IsCompact K ∧ K ⊆ Q ∧ tsupport B ⊆ K ∧ (∀ n, tsupport (f (g n)) ⊆ K) ∧
        (∀ m : ℕ, TendstoUniformly
          (fun n x => iteratedFDeriv ℝ m (fun y => f (g n) y - B y) x) (fun _ => 0) atTop)) :
    (Set.range f).Countable ∧
    (∀ Phi ∈ Set.range f, ContDiff ℝ ∞ Phi ∧ HasCompactSupport Phi ∧ tsupport Phi ⊆ Q) ∧
    (∀ B : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ B → HasCompactSupport B → tsupport B ⊆ Q →
      ∃ Bs : ℕ → SpatialCoordinates d → ℝ,
        (∀ k, Bs k ∈ Set.range f) ∧
        (∀ m : ℕ, TendstoUniformly
          (fun n x => iteratedFDeriv ℝ m (fun y => Bs n y - B y) x) (fun _ => 0) atTop)) := by
  refine ⟨Set.countable_range f, ?_, ?_⟩
  · rintro Phi ⟨g, rfl⟩
    exact hf g
  · intro B hB hBsupp hBQ
    obtain ⟨K, g, _, _, _, _, hDerivs⟩ := hdense B hB hBsupp hBQ
    exact ⟨fun n => f (g n), fun n => Set.mem_range_self (g n), hDerivs⟩

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper

/- Actual large- and small-cube response convergence supplies killed-form
consistency. The reverse inequality uses the proved cutoff localization with
no separate cutoff-product premise. -/
/-- Complete small-form energy isometry plus the compact-support reverse
inequality identifies the actual killed subspace. -/
theorem aux_thm_prop_killed_consistency_of_core
    {d : ℕ} (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Eq : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))))
    (C : Set (DomainL2 (centeredCube zq r hr0)))
    (hC : _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Eq (centeredCube zq r hr0 : Set (SpatialCoordinates d)) C)
    (hupper :
      ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ EQ.domain →
        (∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧
          HasCompactSupport wc ∧
          tsupport wc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∧
          (w : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] wc) →
        ∃ wq : DomainL2 (centeredCube zq r hr0),
          wq ∈ Eq.domain ∧ zeroExtensionLp hqQ wq = w ∧
          (Eq.energy wq : EReal) ≤ (EQ.energy w : EReal))
    (hclosure : ∀ u ∈ Eq.domain,
      zeroExtensionLp hqQ u ∈ EQ.domain ∧
      EQ.energy (zeroExtensionLp hqQ u) = Eq.energy u ∧
      ∀ v ∈ Eq.domain, EQ.form (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v) = Eq.form u v) :
    ∃ D : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)),
      _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) D ∧
      (∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ D ↔
        ∃ u : DomainL2 (centeredCube zq r hr0),
          u ∈ Eq.domain ∧ zeroExtensionLp hqQ u = w) ∧
      (∀ u ∈ Eq.domain, zeroExtensionLp hqQ u ∈ EQ.domain ∧
        EQ.energy (zeroExtensionLp hqQ u) = Eq.energy u) ∧
      (∀ u ∈ Eq.domain, ∀ v ∈ Eq.domain,
        EQ.form (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v) = Eq.form u v) := by
  let ext : DomainL2 (centeredCube zq r hr0) →ₗ[ℝ]
      DomainL2 (centeredCube zQ R hR0) :=
    { toFun := zeroExtensionLp hqQ
      map_add' := aux_prop_killed_consistency_zeroExtension_add hqQ
      map_smul' := aux_prop_killed_consistency_zeroExtension_smul hqQ }
  let D : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)) :=
    Submodule.map ext Eq.domain
  have hdom : ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ Eq.domain →
      ext u ∈ EQ.domain := by
    intro u hu
    exact (hclosure u hu).1
  have henergy : ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ Eq.domain →
      EQ.energy (ext u) = Eq.energy u := by
    intro u hu
    exact (hclosure u hu).2.1
  have hform : ∀ (u : DomainL2 (centeredCube zq r hr0)) (hu : u ∈ Eq.domain)
      (v : DomainL2 (centeredCube zq r hr0)) (hv : v ∈ Eq.domain),
      EQ.form (ext u) (ext v) = Eq.form u v := by
    intro u hu v hv
    exact (hclosure u hu).2.2 v hv
  have henergy_norm : ∀ (u : DomainL2 (centeredCube zq r hr0)) (hu : u ∈ Eq.domain),
      EQ.energyNormSq (ext u) = Eq.energyNormSq u := by
    intro u hu
    have hformself := hform u hu u hu
    rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq,
      _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq, hformself]
    change Eq.form u u + ‖zeroExtensionLp hqQ u‖ ^ 2 = Eq.form u u + ‖u‖ ^ 2
    have hn : ‖zeroExtensionLp hqQ u‖ = ‖u‖ := by
      simpa only using! lane2_norm_zeroExtensionLp hqQ u
    rw [hn]
  have henergy_norm_sub :
      ∀ (u v : DomainL2 (centeredCube zq r hr0)), u ∈ Eq.domain → v ∈ Eq.domain →
        EQ.energyNormSq (ext u - ext v) = Eq.energyNormSq (u - v) := by
    intro u v hu hv
    rw [← ext.map_sub, henergy_norm (u - v) (Eq.domain.sub_mem hu hv)]
  have hcore_ext : ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ C →
      EQ.MemCoreOn (centeredCube zq r hr0 : Set (SpatialCoordinates d)) (ext u) := by
    intro u hu
    have hcu := hC.memCoreOn u hu
    exact ⟨hdom u hcu.mem_domain,
      aux_prop_killed_consistency_zeroExtension_core_rep hqQ u hcu.hasCoreRep⟩
  have hle : D ≤ EQ.domain := by
    intro w hw
    change w ∈ Submodule.map ext Eq.domain at hw
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map.mp hw)
    exact hdom u hu
  have hmemcore : ∀ w : DomainL2 (centeredCube zQ R hR0),
      EQ.MemCoreOn (centeredCube zq r hr0 : Set (SpatialCoordinates d)) w → w ∈ D := by
    intro w hw
    obtain ⟨u, hu, hext, _⟩ := hupper w hw.mem_domain hw.hasCoreRep
    change w ∈ Submodule.map ext Eq.domain
    apply Submodule.mem_map.mpr
    refine ⟨u, hu, ?_⟩
    exact hext
  have happrox : ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ D →
      ∀ ε : ℝ, 0 < ε →
        ∃ w' : DomainL2 (centeredCube zQ R hR0),
          EQ.MemCoreOn (centeredCube zq r hr0 : Set (SpatialCoordinates d)) w' ∧
          EQ.energyNormSq (w - w') < ε := by
    intro w hw ε hε
    change w ∈ Submodule.map ext Eq.domain at hw
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map.mp hw)
    obtain ⟨c, hc, hlt⟩ := hC.denseEnergy u hu ε hε
    refine ⟨ext c, hcore_ext c hc, ?_⟩
    rw [← ext.map_sub, henergy_norm (u - c)
      (Eq.domain.sub_mem hu (hC.memCoreOn c hc).mem_domain)]
    exact hlt
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · refine
      { le_domain := hle
        memCoreOn_mem := hmemcore
        approx := happrox
        isClosed := ?_ }
    intro wN w hwN hwd hconv
    have hdomN : ∀ n, wN n ∈ EQ.domain := fun n => hle (hwN n)
    have hwN' : ∀ n, wN n ∈ Submodule.map ext Eq.domain := by
      intro n
      simpa only [D] using hwN n
    choose uN huN hwu using fun n => Submodule.mem_map.mp (hwN' n)
    have hEQcauchy : ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
          EQ.energyNormSq (wN p - wN q) < ε := by
      intro ε hε
      have hδ : 0 < ε / 4 := by linarith
      obtain ⟨N, hN⟩ := (eventually_atTop.1 ((tendsto_order.mp hconv).2 (ε / 4) hδ))
      refine ⟨N, ?_⟩
      intro p hp q hq
      have hEp := hN p hp
      have hEq := hN q hq
      have hsubp : wN p - w ∈ EQ.domain := EQ.domain.sub_mem (hdomN p) hwd
      have hsubq : wN q - w ∈ EQ.domain := EQ.domain.sub_mem (hdomN q) hwd
      have hsp : Real.sqrt (EQ.energyNormSq (wN p - w)) < Real.sqrt ε / 2 := by
        calc
          Real.sqrt (EQ.energyNormSq (wN p - w)) < Real.sqrt (ε / 4) :=
            Real.sqrt_lt_sqrt (EQ.energyNormSq_nonneg hsubp) hEp
          _ = Real.sqrt ε / 2 := by
            rw [Real.sqrt_div (le_of_lt hε)]
            norm_num
      have hsq : Real.sqrt (EQ.energyNormSq (w - wN q)) < Real.sqrt ε / 2 := by
        rw [EQ.energyNormSq_sub_comm hwd (hdomN q)]
        calc
          Real.sqrt (EQ.energyNormSq (wN q - w)) < Real.sqrt (ε / 4) :=
            Real.sqrt_lt_sqrt (EQ.energyNormSq_nonneg hsubq) hEq
          _ = Real.sqrt ε / 2 := by
            rw [Real.sqrt_div (le_of_lt hε)]
            norm_num
      have htri := EQ.sqrt_energyNormSq_sub_le (hdomN p) hwd (hdomN q)
      have hsqrt : Real.sqrt (EQ.energyNormSq (wN p - wN q)) < Real.sqrt ε := by
        exact lt_of_le_of_lt htri (by linarith)
      have hsquare := (Real.sqrt_lt (EQ.energyNormSq_nonneg
        (EQ.domain.sub_mem (hdomN p) (hdomN q))) (Real.sqrt_nonneg ε)).mp hsqrt
      nlinarith [Real.sq_sqrt (le_of_lt hε)]
    have hEqcauchy : ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
          Eq.energyNormSq (uN p - uN q) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hEQcauchy ε hε
      refine ⟨N, ?_⟩
      intro p hp q hq
      have heq := henergy_norm_sub (uN p) (uN q) (huN p) (huN q)
      have heq' : EQ.energyNormSq (wN p - wN q) =
          Eq.energyNormSq (uN p - uN q) := by
        rw [← hwu p, ← hwu q]
        exact heq
      rw [← heq']
      exact hN p hp q hq
    obtain ⟨u, hu, huconv⟩ := Eq.complete uN huN hEqcauchy
    have huconv' : Tendsto (fun n => Eq.energyNormSq (uN n - u)) atTop (𝓝 0) := by
      simpa only [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq] using huconv
    have hEQnorm : Tendsto (fun n => ‖wN n - w‖) atTop (𝓝 0) := by
      have hsqrt : Tendsto
          (fun n => Real.sqrt (EQ.energyNormSq (wN n - w))) atTop (𝓝 0) := by
        have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
          simpa using (Real.continuous_sqrt.tendsto 0)
        simpa only [Function.comp_apply] using! hc.comp hconv
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
      exact (Real.le_sqrt (norm_nonneg _) (EQ.energyNormSq_nonneg
        (EQ.domain.sub_mem (hdomN n) hwd))).mpr (EQ.sq_norm_le_energyNormSq
          (EQ.domain.sub_mem (hdomN n) hwd))
    have hEqnorm : Tendsto (fun n => ‖uN n - u‖) atTop (𝓝 0) := by
      have hsqrt : Tendsto
          (fun n => Real.sqrt (Eq.energyNormSq (uN n - u))) atTop (𝓝 0) := by
        have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
          simpa using (Real.continuous_sqrt.tendsto 0)
        simpa only [Function.comp_apply] using! hc.comp huconv'
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
      exact (Real.le_sqrt (norm_nonneg _) (Eq.energyNormSq_nonneg
        (Eq.domain.sub_mem (huN n) hu))).mpr (Eq.sq_norm_le_energyNormSq
          (Eq.domain.sub_mem (huN n) hu))
    have hExtnorm : Tendsto (fun n => ‖ext (uN n) - ext u‖) atTop (𝓝 0) := by
      apply hEqnorm.congr
      intro n
      rw [← ext.map_sub]
      change ‖uN n - u‖ = ‖zeroExtensionLp hqQ (uN n - u)‖
      symm
      simpa only using! lane2_norm_zeroExtensionLp hqQ (uN n - u)
    have hWExtnorm : Tendsto (fun n => ‖wN n - ext u‖) atTop (𝓝 0) := by
      apply hExtnorm.congr
      intro n
      rw [hwu n]
    have hWtoW : Tendsto wN atTop (𝓝 w) :=
      (tendsto_iff_norm_sub_tendsto_zero).2 hEQnorm
    have hWtoExt : Tendsto wN atTop (𝓝 (ext u)) :=
      (tendsto_iff_norm_sub_tendsto_zero).2 hWExtnorm
    have hext : ext u = w := tendsto_nhds_unique hWtoExt hWtoW
    change w ∈ Submodule.map ext Eq.domain
    apply Submodule.mem_map.mpr
    exact ⟨u, hu, hext⟩
  · intro w
    constructor
    · intro hw
      change w ∈ Submodule.map ext Eq.domain at hw
      obtain ⟨u, hu, hext⟩ := Submodule.mem_map.mp hw
      exact ⟨u, hu, hext⟩
    · rintro ⟨u, hu, hext⟩
      change w ∈ Submodule.map ext Eq.domain
      exact Submodule.mem_map.mpr ⟨u, hu, hext⟩
  · intro u hu
    exact ⟨hdom u hu, henergy u hu⟩
  · intro u hu v hv
    exact hform u hu v hv


theorem aux_thm_prop_controlled_killed_consistency
    (d : ℕ) (hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR0))
    (Sq : ResponseSpace (centeredCube zq r hr0))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR0))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr0))
    (aQ : ℕ → PositiveCoefficient (centeredCube zQ R hR0))
    (aq : ℕ → PositiveCoefficient (centeredCube zq r hr0))
    (hcoeff : ∀ n, ((aQ n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))]
        ((aq n).val : SpatialCoordinates d → ℝ))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Eq : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))))
    (AQ : aux_thm_prop_analytic_controls d hd zQ R hR0 SQ aQ)
    (Aq : aux_thm_prop_analytic_controls d hd zq r hr0 Sq aq)
    (GNQ : ℕ → DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (GNq : ℕ → DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (hGNQ : ∀ n f, GNQ n f = (responseSolution SQ (aQ n)
      ((sobolevVolumeLoad f).comp SQ.space.subtypeL)).val.1)
    (hGNq : ∀ n f, GNq n f = (responseSolution Sq (aq n)
      ((sobolevVolumeLoad f).comp Sq.space.subtypeL)).val.1)
    (hconvQ : Tendsto GNQ atTop (𝓝 GQ)) (hconvq : Tendsto GNq atTop (𝓝 Gq))
    (hEQ : ∀ v, EQ.energy v = limitFormEnergy GQ v)
    (hEq : ∀ v, Eq.energy v = limitFormEnergy Gq v)
    (hqRegular : ∃ C : Set (DomainL2 (centeredCube zq r hr0)),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Eq (centeredCube zq r hr0 : Set (SpatialCoordinates d)) C) :
    ∃ D : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)),
      _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) D ∧
      (∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ D ↔
        ∃ u : DomainL2 (centeredCube zq r hr0),
          u ∈ Eq.domain ∧ zeroExtensionLp hqQ u = w) ∧
      (∀ u ∈ Eq.domain, zeroExtensionLp hqQ u ∈ EQ.domain ∧
        EQ.energy (zeroExtensionLp hqQ u) = Eq.energy u) ∧
      (∀ u ∈ Eq.domain, ∀ v ∈ Eq.domain,
        EQ.form (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v) = Eq.form u v) := by
  have hMQ := aux_thm_prop_controlled_mosco hSQ AQ GNQ GQ hGNQ hconvQ
  have hMq := aux_thm_prop_controlled_mosco hSq Aq GNq Gq hGNq hconvq
  have hdomQ := aux_thm_prop_domain_eq_of_energy EQ GQ hEQ
  have hdomq := aux_thm_prop_domain_eq_of_energy Eq Gq hEq
  have hQlower : ∀ (vN : ℕ → SQ.space) (v : DomainL2 (centeredCube zQ R hR0)),
      (∀ f : DomainL2 (centeredCube zQ R hR0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      EQ.energy v ≤ liminf (fun n => (responseForm SQ (aQ n) (vN n) (vN n) : EReal)) atTop := by
    simpa only [hEQ] using hMQ.lower
  have hQrecovery : ∀ v ∈ EQ.domain, ∃ vN : ℕ → SQ.space,
      Tendsto (fun n => ((vN n).val.1, (responseForm SQ (aQ n) (vN n) (vN n) : EReal)))
        atTop (𝓝 (v, EQ.energy v)) := by
    simpa only [← hdomQ, ← hEQ] using! hMQ.recovery
  have hqlower : ∀ (vN : ℕ → Sq.space) (v : DomainL2 (centeredCube zq r hr0)),
      (∀ f : DomainL2 (centeredCube zq r hr0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      Eq.energy v ≤ liminf (fun n => (responseForm Sq (aq n) (vN n) (vN n) : EReal)) atTop := by
    simpa only [hEq] using hMq.lower
  have hqrecovery : ∀ v ∈ Eq.domain, ∃ vN : ℕ → Sq.space,
      Tendsto (fun n => ((vN n).val.1, (responseForm Sq (aq n) (vN n) (vN n) : EReal)))
        atTop (𝓝 (v, Eq.energy v)) := by
    simpa only [← hdomq, ← hEq] using! hMq.recovery
  have hzero : ∀ (u : DomainL2 (centeredCube zq r hr0)) (hu : u ∈ Eq.domain),
      ∃ uNQ : ℕ → SQ.space,
        (∀ n, (uNQ n).val.1 = zeroExtensionLp hqQ
          ((Classical.choose (hqrecovery u hu) n).val.1)) ∧
        (∀ n, responseForm SQ (aQ n) (uNQ n) (uNQ n) =
          responseForm Sq (aq n) (Classical.choose (hqrecovery u hu) n)
            (Classical.choose (hqrecovery u hu) n)) ∧
        Tendsto (fun n => ((uNQ n).val.1,
          (responseForm SQ (aQ n) (uNQ n) (uNQ n) : EReal))) atTop
          (𝓝 (zeroExtensionLp hqQ u, (Eq.energy u : EReal))) ∧
        (EQ.energy (zeroExtensionLp hqQ u) : EReal) ≤ (Eq.energy u : EReal) := by
    intro u hu
    exact prop_killed_consistency_zero_extension d hd zQ zq R r hR0 hr0 hqQ SQ Sq
      hSQ hSq aQ aq hcoeff EQ Eq hQlower hqrecovery u hu
  have hupper :
      ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ EQ.domain →
        (∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧
          HasCompactSupport wc ∧
          tsupport wc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∧
          (w : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] wc) →
        ∃ wq : DomainL2 (centeredCube zq r hr0),
          wq ∈ Eq.domain ∧ zeroExtensionLp hqQ wq = w ∧
          (Eq.energy wq : EReal) ≤ (EQ.energy w : EReal) := by
    intro w hw hwrep
    exact aux_lem_weighted_cluster_upper_localize d hd zQ zq R r hR0 hr0 hqQ SQ Sq
      hSQ hSq aQ aq hcoeff EQ Eq hQrecovery hqlower
      (fun _ => AQ.K) (fun _ => AQ.K_pos.le) AQ.K (fun _ => le_rfl)
      (fun w => (AQ.coercive 0 w).1) (fun n w => (AQ.coercive n w).2)
      AQ.interpolation AQ.t AQ.t_lower AQ.t_upper AQ.cutoffs w hw hwrep
  obtain ⟨C, hC⟩ := hqRegular
  have hclosure := prop_killed_consistency_core_closure d hd zQ zq R r hR0 hr0 hqQ EQ Eq
    ⟨C, hC⟩
    (fun u hu => by
      obtain ⟨uNQ, h1, h2, h3, h4⟩ := hzero u hu
      exact h4)
    hupper
  exact aux_thm_prop_killed_consistency_of_core zQ zq R r hR0 hr0 hqQ EQ Eq C hC
    hupper hclosure

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The finite-cutoff energy measure is unchanged by native zero extension
when the two coefficient carriers agree on the smaller domain. -/
theorem aux_thm_prop_zeroExtension_density
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U)
    (aU : PositiveCoefficient U) (aV : PositiveCoefficient V)
    (ha : (aU.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] aV.val)
    (v : SobolevData V) :
    (volume.restrict (U : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (aU.val x *
        ∑ i : Fin d, ((zeroExtensionSobolevData hVU v).2 i x) ^ 2)) =
    (volume.restrict (V : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (aV.val x * ∑ i : Fin d, (v.2 i x) ^ 2)) := by
  have ha' := (ae_restrict_iff' V.isOpen.measurableSet).mp ha
  have heq : (fun x => ENNReal.ofReal (aU.val x *
        ∑ i : Fin d, ((zeroExtensionSobolevData hVU v).2 i x) ^ 2))
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
        (V : Set (SpatialCoordinates d)).indicator
          (fun x => ENNReal.ofReal (aV.val x * ∑ i : Fin d, (v.2 i x) ^ 2)) := by
    filter_upwards [ae_restrict_of_ae ha',
      (ae_all_iff.mpr fun i : Fin d => zeroExtensionLp_coeFn hVU (v.2 i))] with x hx hg
    change ENNReal.ofReal (aU.val x * ∑ i : Fin d, (zeroExtensionLp hVU (v.2 i) x) ^ 2) = _
    by_cases hxV : x ∈ (V : Set (SpatialCoordinates d))
    · simp only [hg, Set.indicator_of_mem hxV, hx hxV]
    · simp only [hg, Set.indicator_of_notMem hxV, zero_pow (by omega : 2 ≠ 0),
        Finset.sum_const_zero, mul_zero, ENNReal.ofReal_zero]
  rw [withDensity_congr_ae heq, withDensity_indicator V.isOpen.measurableSet]
  rw [Measure.restrict_restrict_of_subset hVU]

/-- Native zero extension carries every actual small-domain recovery sequence
to a large-domain recovery sequence once the limiting energies agree. The
entire Sobolev datum is retained, including all gradient coordinates. -/
theorem aux_thm_prop_zeroExtension_recovery
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U)
    (SU : ResponseSpace U) (SV : ResponseSpace V)
    (hSU : SU.space = killedSobolevGraph U) (hSV : SV.space = killedSobolevGraph V)
    (aU : ℕ → PositiveCoefficient U) (aV : ℕ → PositiveCoefficient V)
    (ha : ∀ n, ((aU n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] (aV n).val)
    (u : DomainL2 V) (uN : ℕ → SV.space) (e : EReal)
    (hrec : Tendsto (fun n => ((uN n).val.1,
      (responseForm SV (aV n) (uN n) (uN n) : EReal))) atTop (𝓝 (u, e))) :
    ∃ vN : ℕ → SU.space,
      (∀ n, (vN n).val = zeroExtensionSobolevData hVU (uN n).val) ∧
      Tendsto (fun n => ((vN n).val.1,
        (responseForm SU (aU n) (vN n) (vN n) : EReal))) atTop
        (𝓝 (zeroExtensionLp hVU u, e)) := by
  let vN : ℕ → SU.space := fun n =>
    ⟨zeroExtensionSobolevData hVU (uN n).val, by
      rw [hSU]
      apply lane2_zeroExtensionSobolevData_mem_killed hVU
      rw [← hSV]
      exact (uN n).property⟩
  have henergy (n : ℕ) : responseForm SU (aU n) (vN n) (vN n) =
      responseForm SV (aV n) (uN n) (uN n) := by
    rw [aux_prop_killed_consistency_zero_extension_response,
      aux_prop_killed_consistency_zero_extension_response]
    change sobolevCoefficientForm (aU n) (zeroExtensionSobolevData hVU (uN n).val)
      (zeroExtensionSobolevData hVU (uN n).val) = _
    rw [sobolevCoefficientForm_zeroExtension hVU (aU n) (aV n) (ha n),
      aux_prop_killed_consistency_zero_extension_restrict]
  refine ⟨vN, fun _ => rfl, ?_⟩
  have hrec' : Tendsto (fun n => ((uN n).val.1,
      (responseForm SV (aV n) (uN n) (uN n) : EReal))) atTop (𝓝 u ×ˢ 𝓝 e) := by
    simpa only [nhds_prod_eq] using hrec
  have hfirst := (lane2_continuous_zeroExtensionLp hVU).tendsto u |>.comp hrec'.fst
  have hsecond : Tendsto
      (fun n => (responseForm SU (aU n) (vN n) (vN n) : EReal)) atTop (𝓝 e) := by
    simpa only [henergy] using hrec'.snd
  exact hfirst.prodMk_nhds hsecond

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

/-- Actual controlled limits agree at the energy-measure level under native
zero extension. The proof uses identical finite-cutoff energy measures along a
small-cube recovery sequence, followed by uniqueness of weak measure limits. -/
theorem aux_thm_prop_controlled_energy_restriction
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR0))
    (Sq : ResponseSpace (centeredCube zq r hr0))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR0))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr0))
    (aQ : ℕ → PositiveCoefficient (centeredCube zQ R hR0))
    (aq : ℕ → PositiveCoefficient (centeredCube zq r hr0))
    (hcoeff : ∀ n, ((aQ n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))]
        ((aq n).val : SpatialCoordinates d → ℝ))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Eq : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))))
    (AQ : aux_thm_prop_analytic_controls d hd zQ R hR0 SQ aQ)
    (Aq : aux_thm_prop_analytic_controls d hd zq r hr0 Sq aq)
    (GNQ : ℕ → DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (GNq : ℕ → DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (hGNQ : ∀ n f, GNQ n f = (responseSolution SQ (aQ n)
      ((sobolevVolumeLoad f).comp SQ.space.subtypeL)).val.1)
    (hGNq : ∀ n f, GNq n f = (responseSolution Sq (aq n)
      ((sobolevVolumeLoad f).comp Sq.space.subtypeL)).val.1)
    (hconvQ : Tendsto GNQ atTop (𝓝 GQ)) (hconvq : Tendsto GNq atTop (𝓝 Gq))
    (hEQ : ∀ v, EQ.energy v = limitFormEnergy GQ v)
    (hEq : ∀ v, Eq.energy v = limitFormEnergy Gq v)
    (hqRegular : ∃ C : Set (DomainL2 (centeredCube zq r hr0)),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Eq.toClosedForm (centeredCube zq r hr0 : Set (SpatialCoordinates d)) C)
    (hQRegular : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EQ.toClosedForm
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) C)
    (GammaQ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (Gammaq : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eq.toClosedForm) :
    ∀ u ∈ Eq.domain, GammaQ.measure (zeroExtensionLp hqQ u) = Gammaq.measure u := by
  obtain ⟨DK, hDK, hDKmem, hext, hform⟩ :=
    aux_thm_prop_controlled_killed_consistency d hd zQ zq R r hR0 hr0 hqQ SQ Sq hSQ hSq
      aQ aq hcoeff EQ.toClosedForm Eq.toClosedForm AQ Aq GNQ GNq GQ Gq hGNQ hGNq
      hconvQ hconvq hEQ hEq hqRegular
  have hCQ := (aux_thm_prop_energy_measure_convergence BD BDQ EM hcontract hSQ
    AQ GNQ GQ hGNQ hconvQ EQ hEQ hQRegular GammaQ).1
  have hCq := (aux_thm_prop_energy_measure_convergence BD BDQ EM hcontract hSq
    Aq GNq Gq hGNq hconvq Eq hEq hqRegular Gammaq).1
  have hMosco := aux_thm_prop_controlled_mosco hSq Aq GNq Gq hGNq hconvq
  have hdom := aux_thm_prop_domain_eq_of_energy Eq.toClosedForm Gq hEq
  intro u hu
  have huQ := (hext u hu).1
  have heQ := (hext u hu).2
  obtain ⟨uN, hrec⟩ := hMosco.recovery u (hdom ▸ hu)
  have hrec' : Tendsto (fun n => ((uN n).val.1,
      (responseForm Sq (aq n) (uN n) (uN n) : EReal))) atTop (𝓝 (u, Eq.energy u)) := by
    simpa only [hEq] using hrec
  obtain ⟨vN, hvN, hvrec⟩ := aux_thm_prop_zeroExtension_recovery hqQ SQ Sq hSQ hSq
    aQ aq hcoeff u uN (Eq.energy u) hrec'
  have hvrec' : Tendsto (fun n => ((vN n).val.1,
      (responseForm SQ (aQ n) (vN n) (vN n) : EReal))) atTop
      (𝓝 (zeroExtensionLp hqQ u, EQ.energy (zeroExtensionLp hqQ u))) := by
    simpa only [heQ] using hvrec
  let : IsFiniteMeasure (GammaQ.measure (zeroExtensionLp hqQ u)) :=
    ⟨GammaQ.measure_univ_lt_top _ huQ⟩
  let : IsFiniteMeasure (Gammaq.measure u) := ⟨Gammaq.measure_univ_lt_top u hu⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro phi
  have hQ := hCQ (zeroExtensionLp hqQ u) vN huQ hvrec' phi phi.continuous.continuousOn
  have hq := hCq u uN hu hrec' phi phi.continuous.continuousOn
  have hdensity (n : ℕ) :
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).withDensity
        (fun x => ENNReal.ofReal ((aQ n).val x * ∑ i : Fin d, ((vN n).val.2 i x) ^ 2)) =
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))).withDensity
        (fun x => ENNReal.ofReal ((aq n).val x * ∑ i : Fin d, ((uN n).val.2 i x) ^ 2)) := by
    rw [hvN n]
    exact aux_thm_prop_zeroExtension_density hqQ (aQ n) (aq n) (hcoeff n) (uN n).val
  simp only [hdensity] at hQ
  exact tendsto_nhds_unique hQ hq

end Standing
end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- Uniform core density and the proved Lipschitz calculus construct an actual
form-domain cutoff, equal to one on a prescribed compact set. -/
theorem aux_thm_prop_core_plateau
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (K O : Set (SpatialCoordinates d)) (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hOQ : O ⊆ (Q : Set (SpatialCoordinates d))) :
    ∃ (chi : DomainL2 Q) (chic : SpatialCoordinates d → ℝ),
      E.toClosedForm.MemCoreOn O chi ∧ Continuous chic ∧ HasCompactSupport chic ∧
      tsupport chic ⊆ O ∧ (⇑chi =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic) ∧
      (∀ x, 0 ≤ chic x ∧ chic x ≤ 1) ∧ (∀ x ∈ K, chic x = 1) := by
  obtain ⟨theta, htheta, hthetac, hthetas, _htheta0, _htheta1, hthetaK⟩ :=
    _root_.SubdiffusiveProcess.DirichletForm.exists_continuous_plateau hK hO hKO
  obtain ⟨C, hC⟩ := hcore
  obtain ⟨w, hw, g, hg, hgc, hgs, hwg, hclose⟩ := hC.denseUniform theta htheta
    hthetac (hthetas.trans hOQ) (1 / 4) (by norm_num)
  let T : ℝ → ℝ := fun s => _root_.SubdiffusiveProcess.DirichletForm.ramp 1 (2 * s - 1 / 2)
  have hT : LipschitzWith 2 T := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    have h := (_root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_ramp 1).dist_le_mul
      (2 * a - 1 / 2) (2 * b - 1 / 2)
    change dist (T a) (T b) ≤ (2 : ℝ≥0) * dist a b
    simpa only [T, NNReal.coe_one, NNReal.coe_ofNat, one_mul, Real.dist_eq,
      show 2 * a - 1 / 2 - (2 * b - 1 / 2) = 2 * (a - b) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h
  have hT0 : T 0 = 0 := by
    dsimp [T, _root_.SubdiffusiveProcess.DirichletForm.ramp]
    norm_num
  let chi : DomainL2 Q := hT.compLp hT0 w
  have hchirep0 : ⇑chi =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => T (w x) := LipschitzWith.coeFn_compLp _ _ _
  have hchidom := (_root_.SubdiffusiveProcess.DirichletForm.lipschitz_comp_mem E hT hT0
    (hC.memCoreOn w hw).mem_domain hchirep0).1
  have hchirep : ⇑chi =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => T (g x) := by
    filter_upwards [hchirep0, hwg] with x hx hwx
    rw [hx, hwx]
  have hsupp : tsupport (fun x => T (g x)) ⊆ tsupport theta := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hxt
    have hz := image_eq_zero_of_notMem_tsupport hxt
    have hbound := (abs_lt.mp (hclose x)).2
    rw [hz, sub_zero] at hbound
    have hzero : T (g x) = 0 := _root_.SubdiffusiveProcess.DirichletForm.ramp_of_nonpos (by linarith)
    exact hx hzero
  have hcont : Continuous (fun x => T (g x)) := hT.continuous.comp hg
  have hcompact : HasCompactSupport (fun x => T (g x)) :=
    hthetac.of_isClosed_subset isClosed_closure hsupp
  refine ⟨chi, fun x => T (g x), ⟨hchidom, _, hcont, hcompact, hsupp.trans hthetas,
    hchirep⟩, hcont, hcompact, hsupp.trans hthetas, hchirep, ?_, ?_⟩
  · intro x
    exact ⟨_root_.SubdiffusiveProcess.DirichletForm.ramp_nonneg _ _, _root_.SubdiffusiveProcess.DirichletForm.ramp_le (by norm_num)⟩
  · intro x hx
    have hbound := (abs_lt.mp (hclose x)).1
    rw [hthetaK x hx] at hbound
    exact _root_.SubdiffusiveProcess.DirichletForm.ramp_of_ge (by norm_num) (by linarith)

/-- Extend a closure-continuous representative to a bounded continuous function,
retaining exact values on the entire closed cube. -/
theorem aux_thm_prop_bounded_cube_extension
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (f : SpatialCoordinates d → ℝ)
    (hf : ContinuousOn f (closure (centeredCube z R hR : Set (SpatialCoordinates d)))) :
    ∃ F : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), F x = f x := by
  let K : Set (SpatialCoordinates d) := closure (centeredCube z R hR : Set (SpatialCoordinates d))
  let : CompactSpace K := isCompact_iff_compactSpace.mp (lane2_isCompact_closure_centeredCube z hR)
  let fK : C(K, ℝ) := ⟨fun x => f x, hf.domRestrict⟩
  let fKb : BoundedContinuousFunction K ℝ := BoundedContinuousFunction.mkOfCompact fK
  obtain ⟨F, _hFnorm, hF⟩ :=
    BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed fKb isClosed_closure
  refine ⟨F, ?_⟩
  intro x hx
  have h := congrArg (fun g : BoundedContinuousFunction K ℝ => g ⟨x, hx⟩) hF
  simpa [fKb, fK] using! h

/-- A continuous domain element can be localized to any interior open region
without changing its exact representative on the prescribed compact set. -/
theorem aux_thm_prop_core_localization
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z R hR : Set (SpatialCoordinates d)) C)
    (K O : Set (SpatialCoordinates d)) (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hOQ : O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (u : DomainL2 (centeredCube z R hR)) (hu : u ∈ E.domain)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] U) :
    ∃ (v : DomainL2 (centeredCube z R hR)) (V : SpatialCoordinates d → ℝ),
      E.toClosedForm.MemCoreOn O v ∧ Continuous V ∧ HasCompactSupport V ∧
      tsupport V ⊆ O ∧
      (⇑v =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] V) ∧
      (∀ x ∈ K, V x = U x) := by
  obtain ⟨F, hF⟩ := aux_thm_prop_bounded_cube_extension z R hR U hU
  have huF : ⇑u =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] F := by
    filter_upwards [hurep, ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hx hxQ
    exact hx.trans (hF x (subset_closure hxQ)).symm
  obtain ⟨chi, chic, hchi, hchic, hchics, hchicO, hchirep, _hbd, hchiK⟩ :=
    aux_thm_prop_core_plateau (centeredCube z R hR) E hcore K O hK hO hKO hOQ
  obtain ⟨v, hv, hvrep⟩ := _root_.SubdiffusiveProcess.DirichletForm.mul_mem_of_bounded E O u chi hu F
    F.continuous huF ⟨‖F‖, fun x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm x⟩
    hchi chic hchic hchirep
  refine ⟨v, fun x => F x * chic x, hv, F.continuous.mul hchic,
    hchics.mul_left, tsupport_mul_subset_right.trans hchicO, hvrep, ?_⟩
  intro x hx
  change F x * chic x = U x
  rw [hchiK x hx, mul_one, hF x (subset_closure (hOQ (hKO hx)))]

end SubdiffusiveProcess.Paper


end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper

/-- The literal continuous boundary-energy classes agree in two consistent
ambient cubes. Both directions localize competitors with actual form-domain
cutoffs, so no zero boundary value of an arbitrary representative is assumed. -/
theorem aux_thm_prop_boundary_energy_set_restriction
    {d : ℕ} (zQ zP zq : SpatialCoordinates d) (R P r : ℝ)
    (hR : 0 < R) (hP : 0 < P) (hr : 0 < r)
    (hPQ : (centeredCube zP P hP : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (hqP : closure (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zP P hP : Set (SpatialCoordinates d)))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (EP : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zP P hP : Set (SpatialCoordinates d))))
    (GammaQ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (GammaP : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EP.toClosedForm)
    (hcoreQ : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EQ.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (hcoreP : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EP.toClosedForm
      (centeredCube zP P hP : Set (SpatialCoordinates d)) C)
    (DP : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hDP : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm
      (centeredCube zP P hP : Set (SpatialCoordinates d)) DP)
    (hDPmem : ∀ w, w ∈ DP ↔ ∃ v, v ∈ EP.domain ∧ zeroExtensionLp hPQ v = w)
    (hGamma : ∀ v ∈ EP.domain, GammaQ.measure (zeroExtensionLp hPQ v) = GammaP.measure v)
    (b : SpatialCoordinates d → ℝ) :
    aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) EQ.toClosedForm GammaQ
        (centeredCube zq r hr : Set (SpatialCoordinates d)) b =
      aux_thm_prop_boundary_energy_set (centeredCube zP P hP) EP.toClosedForm GammaP
        (centeredCube zq r hr : Set (SpatialCoordinates d)) b := by
  have hqCompact := lane2_isCompact_closure_centeredCube zq hr
  apply Set.Subset.antisymm
  · rintro e ⟨v, V, hv, hV, hvrep, hVb, he⟩
    obtain ⟨w, W, hw, hW, hWc, hWP, hwrep, hWV⟩ :=
      aux_thm_prop_core_localization zQ R hR EQ hcoreQ
        (closure (centeredCube zq r hr : Set (SpatialCoordinates d)))
        (centeredCube zP P hP : Set (SpatialCoordinates d)) hqCompact
        (centeredCube zP P hP).isOpen hqP hPQ v hv V hV hvrep
    obtain ⟨wp, hwp, hext⟩ := (hDPmem w).mp (hDP.memCoreOn_mem w hw)
    have hrepP : ⇑wp =ᵐ[volume.restrict (centeredCube zP P hP : Set (SpatialCoordinates d))] W := by
      have hextrep := ae_restrict_of_ae_restrict_of_subset hPQ (zeroExtensionLp_coeFn hPQ wp)
      rw [hext] at hextrep
      filter_upwards [hextrep, ae_restrict_of_ae_restrict_of_subset hPQ hwrep,
        ae_restrict_mem (centeredCube zP P hP).isOpen.measurableSet] with x hx hy hxP
      rw [Set.indicator_of_mem hxP] at hx
      exact hx.symm.trans hy
    have hlocal : GammaQ.measure w (centeredCube zq r hr : Set (SpatialCoordinates d)) =
        GammaQ.measure v (centeredCube zq r hr : Set (SpatialCoordinates d)) := by
      apply GammaQ.locality_apply hw.mem_domain hv (centeredCube zq r hr).isOpen
      filter_upwards [ae_restrict_of_ae hwrep, ae_restrict_of_ae hvrep,
        ae_restrict_mem (centeredCube zq r hr).isOpen.measurableSet] with x hx hy hxq
      exact hx.trans ((hWV x (subset_closure hxq)).trans hy.symm)
    refine ⟨wp, W, hwp, hW.continuousOn, hrepP,
      fun x hx => (hWV x (frontier_subset_closure hx)).trans (hVb x hx), ?_⟩
    rw [← hGamma wp hwp, hext, hlocal]
    exact he
  · rintro e ⟨v, V, hv, hV, hvrep, hVb, he⟩
    obtain ⟨w, W, hw, hW, hWc, hWP, hwrep, hWV⟩ :=
      aux_thm_prop_core_localization zP P hP EP hcoreP
        (closure (centeredCube zq r hr : Set (SpatialCoordinates d)))
        (centeredCube zP P hP : Set (SpatialCoordinates d)) hqCompact
        (centeredCube zP P hP).isOpen hqP (Subset.refl _) v hv V hV hvrep
    have hwQ : zeroExtensionLp hPQ w ∈ EQ.domain :=
      hDP.le_domain ((hDPmem _).mpr ⟨w, hw.mem_domain, rfl⟩)
    have hwrep' := (ae_restrict_iff' (centeredCube zP P hP).isOpen.measurableSet).mp hwrep
    have hrepQ : ⇑(zeroExtensionLp hPQ w)
        =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] W := by
      filter_upwards [zeroExtensionLp_coeFn hPQ w, ae_restrict_of_ae hwrep'] with x hx hy
      rw [hx]
      by_cases hxP : x ∈ (centeredCube zP P hP : Set (SpatialCoordinates d))
      · rw [Set.indicator_of_mem hxP]
        exact hy hxP
      · rw [Set.indicator_of_notMem hxP]
        exact (image_eq_zero_of_notMem_tsupport (fun h => hxP (hWP h))).symm
    have hlocal : GammaP.measure w (centeredCube zq r hr : Set (SpatialCoordinates d)) =
        GammaP.measure v (centeredCube zq r hr : Set (SpatialCoordinates d)) := by
      apply GammaP.locality_apply hw.mem_domain hv (centeredCube zq r hr).isOpen
      filter_upwards [ae_restrict_of_ae hwrep, ae_restrict_of_ae hvrep,
        ae_restrict_mem (centeredCube zq r hr).isOpen.measurableSet] with x hx hy hxq
      exact hx.trans ((hWV x (subset_closure hxq)).trans hy.symm)
    refine ⟨zeroExtensionLp hPQ w, W, hwQ, hW.continuousOn, hrepQ,
      fun x hx => (hWV x (frontier_subset_closure hx)).trans (hVb x hx), ?_⟩
    rw [hGamma w hw.mem_domain, hlocal]
    exact he

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

/-- Boundary-energy classes on actual controlled limits agree under changing
the ambient cube. The killed-domain and energy-measure identifications are
constructed from the two response limits, rather than carried as premises. -/
theorem aux_thm_prop_controlled_boundary_restriction
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR0))
    (Sq : ResponseSpace (centeredCube zq r hr0))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR0))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr0))
    (aQ : ℕ → PositiveCoefficient (centeredCube zQ R hR0))
    (aq : ℕ → PositiveCoefficient (centeredCube zq r hr0))
    (hcoeff : ∀ n, ((aQ n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))]
        ((aq n).val : SpatialCoordinates d → ℝ))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Eq : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))))
    (AQ : aux_thm_prop_analytic_controls d hd zQ R hR0 SQ aQ)
    (Aq : aux_thm_prop_analytic_controls d hd zq r hr0 Sq aq)
    (GNQ : ℕ → DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (GNq : ℕ → DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (hGNQ : ∀ n f, GNQ n f = (responseSolution SQ (aQ n)
      ((sobolevVolumeLoad f).comp SQ.space.subtypeL)).val.1)
    (hGNq : ∀ n f, GNq n f = (responseSolution Sq (aq n)
      ((sobolevVolumeLoad f).comp Sq.space.subtypeL)).val.1)
    (hconvQ : Tendsto GNQ atTop (𝓝 GQ)) (hconvq : Tendsto GNq atTop (𝓝 Gq))
    (hEQ : ∀ v, EQ.energy v = limitFormEnergy GQ v)
    (hEq : ∀ v, Eq.energy v = limitFormEnergy Gq v)
    (hqRegular : ∃ C : Set (DomainL2 (centeredCube zq r hr0)),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Eq.toClosedForm (centeredCube zq r hr0 : Set (SpatialCoordinates d)) C)
    (hQRegular : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EQ.toClosedForm
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) C)
    (GammaQ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (Gammaq : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eq.toClosedForm)
    (zcell : SpatialCoordinates d) (rcell : ℝ) (hrcell : 0 < rcell)
    (hcell : closure (centeredCube zcell rcell hrcell : Set (SpatialCoordinates d)) ⊆
      (centeredCube zq r hr0 : Set (SpatialCoordinates d))) :
    ∀ b : SpatialCoordinates d → ℝ,
      aux_thm_prop_boundary_energy_set (centeredCube zQ R hR0) EQ.toClosedForm GammaQ
        (centeredCube zcell rcell hrcell : Set (SpatialCoordinates d)) b =
      aux_thm_prop_boundary_energy_set (centeredCube zq r hr0) Eq.toClosedForm Gammaq
        (centeredCube zcell rcell hrcell : Set (SpatialCoordinates d)) b := by
  obtain ⟨D, hD, hmem, hext, hform⟩ := aux_thm_prop_controlled_killed_consistency d hd
    zQ zq R r hR0 hr0 hqQ SQ Sq hSQ hSq aQ aq hcoeff EQ.toClosedForm Eq.toClosedForm
    AQ Aq GNQ GNq GQ Gq hGNQ hGNq hconvQ hconvq hEQ hEq hqRegular
  have hGamma := aux_thm_prop_controlled_energy_restriction BD BDQ EM hcontract
    zQ zq R r hR0 hr0 hqQ SQ Sq hSQ hSq aQ aq hcoeff EQ Eq AQ Aq GNQ GNq GQ Gq
    hGNQ hGNq hconvQ hconvq hEQ hEq hqRegular hQRegular GammaQ Gammaq
  exact aux_thm_prop_boundary_energy_set_restriction zQ zq zcell R r rcell hR0 hr0 hrcell
    hqQ hcell EQ Eq GammaQ Gammaq hQRegular hqRegular D hD hmem hGamma

end Standing
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


/-- The represented source/trace catalogue supplies all finite-mesh estimates
needed to identify the actual affine response matrix with the limiting
boundary-energy minimum. No separate mesh, source-density, or exponent-match
hypothesis is passed to the consumer. -/
theorem aux_thm_prop_represented_affine_glb
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
    (SP : ResponseSpace (centeredCube (z jQ) (3 * rq) h3rq))
    (hSP : SP.space = killedSobolevGraph (centeredCube (z jQ) (3 * rq) h3rq))
    (Controls : aux_thm_prop_analytic_controls d hd (z jQ) (3 * rq) h3rq SP
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z jQ) h3rq))
    (GN : ℕ → DomainL2 (centeredCube (z jQ) (3 * rq) h3rq) →L[ℝ]
      DomainL2 (centeredCube (z jQ) (3 * rq) h3rq))
    (Glim : DomainL2 (centeredCube (z jQ) (3 * rq) h3rq) →L[ℝ]
      DomainL2 (centeredCube (z jQ) (3 * rq) h3rq))
    (hGN : ∀ n f, GN n f =
      (responseSolution SP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z jQ) h3rq)
        ((sobolevVolumeLoad f).comp SP.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 Glim))
    (F : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube (z jQ) (3 * rq) h3rq : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (hF : ∀ v, F.energy v = limitFormEnergy Glim v)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube (z jQ) (3 * rq) h3rq : Set (SpatialCoordinates d)) C)
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
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (3 * rq) h3rq)
        F.toClosedForm Gamma (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c))
        ((volume (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ Amat.mulVec p)) ∧
      (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (3 * rq) h3rq)
        F.toClosedForm Gamma (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c)).Nonempty := by
  have hMesh := aux_thm_prop_represented_mesh_control d hd M H Ω P cutoff env J j0 z r hr
    S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders I Index
    resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
    sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
    hRep om hom jQ rq hrq h3rq hrQ
  obtain ⟨Ugrid, UgridStar, hUg, hGridBound⟩ := aux_thm_prop_represented_mesh_extension
    d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell
    Cext beta alpha eta t orders I Index resp respLim constants G coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid origin gridRoot gridKey hRep om hom jQ rq hrq h3rq hrQ
  rcases hRep with ⟨ht, hAlpha, hBeta, hC, hOrders, hN, hIR, hMeas, hLaw, hSeq,
    hcontain, hrat, htri, hcomplete, hgrat, hcover, hS, hDense, hSrc, hSrcDense,
    hTrace, hSt, hParent, hTDense, hPlateau, hMeasc, hMom, hNonneg, hSol, hCoeff,
    hCoerc, hExt, hGrid, hSrcEst, hCellEst⟩
  let A : ℕ → SpatialCoordinates d → ℝ := fun n => cutoffCoefficient M H (env n om) (cutoff n)
  have hcont (n : ℕ) : Continuous (A n) :=
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (env n om) (cutoff n)
  have hell (n : ℕ) : ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ closure (centeredCube (z jQ) (3 * rq) h3rq : Set (SpatialCoordinates d)),
        lo ≤ A n x ∧ A n x ≤ hi := by
    have hK := lane2_isCompact_closure_centeredCube (z jQ) h3rq
    have hne : (closure (centeredCube (z jQ) (3 * rq) h3rq : Set (SpatialCoordinates d))).Nonempty :=
      ⟨z jQ, subset_closure (Metric.mem_ball_self (by positivity))⟩
    obtain ⟨lo, hlo, hmin⟩ := hK.exists_isMinOn hne (hcont n).continuousOn
    obtain ⟨hi, hhi, hmax⟩ := hK.exists_isMaxOn hne (hcont n).continuousOn
    exact ⟨A n lo, A n hi, _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (env n om) (cutoff n) lo,
      fun x hx => ⟨hmin hx, hmax hx⟩⟩
  have hsource := aux_thm_prop_source_catalogue
    (centeredCube (z jQ) (3 * rq) h3rq : Set (SpatialCoordinates d)) (f jQ)
    (fun g => ⟨(hSrc jQ g).1, (hSrc jQ g).2.1, by
      simpa only [hrQ] using (hSrc jQ g).2.2.1⟩)
    (by simpa only [hrQ] using hSrcDense jQ)
  let hcsub := fun k : OddGridIndex d (triadicHalf 1) =>
    oddGridCell_subset (z jQ) h3rq (triadicHalf 1) k
  have hMesh' := aux_thm_prop_mesh_controls_of_cells (z jQ) rq h3rq hcsub A
    (Set.range (f jQ)) alpha t hMesh
  let s : ℝ := min Controls.t t
  let Controls' := aux_thm_prop_controls_lower_exponent Controls s
    (lt_min Controls.t_lower ht.1) (min_le_left _ _)
  have hMeshS := aux_thm_prop_mesh_controls_lower_exponent (z jQ) rq h3rq hcsub A
    (Set.range (f jQ)) alpha t hMesh' s (min_le_right _ _)
  obtain ⟨B, hB⟩ := hSeq.2.2.2.2 (extensionKey jC) om hom
  have hcell : (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d)) =
      (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d)) := by
    simp only [centeredCube, hzC, hrC]
  have hBound : ∀ n : ℕ, ∀ e : H1Function (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (z jQ) rq e.toFun →
      cellDirichletInfimum (A n) (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d)) e ≤
        Cext * constants (extensionKey jC) n om * rq ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta (z jQ) rq e.toFun ^ 2 := by
    intro n
    have h := hExt jC n om hom
    rw [hcell] at h
    simpa only [hzC, hrC] using h
  exact aux_thm_prop_affine_boundary_glb BD BDQ EM hcontract (z jQ) rq hrq h3rq hcsub
    beta alpha hBeta.1 hBeta.2 hAlpha.1 SP hSP A (fun n => (hcont n).continuousOn)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z jQ) h3rq)
    (fun n => aux_lem_replace_large_cube_cutoff_positive_coe M H (env n om) (cutoff n) (z jQ) h3rq)
    hell F Gamma Controls' GN Glim hGN hConv hF hcore
    (aux_thm_prop_killed_domain F.toClosedForm (centeredCube (z jQ) rq hrq : Set (SpatialCoordinates d)))
    (aux_thm_prop_isKilledDomain F.toClosedForm _) s le_rfl (Set.range (f jQ))
    hsource.2.1 hMeshS hsource.1 Cext hC.le Ugrid UgridStar hUg hGridBound (max B 0)
    (fun n => constants (extensionKey jC) n om)
    (fun n => ⟨hNonneg _ om hom n, (le_abs_self _).trans ((hB n).trans (le_max_left _ _))⟩)
    hBound hsource.2.2 hP
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z jQ) hrq)
    (fun n => aux_lem_replace_large_cube_cutoff_positive_coe M H (env n om) (cutoff n) (z jQ) hrq)
    Amat hAffine

end Standing
end SubdiffusiveProcess.Paper


end

