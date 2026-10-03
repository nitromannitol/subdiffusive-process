module

public import SubdiffusiveProcess.Paper.prop_conc_local_affine_order
public import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
-- Working candidate. Two local supplier interfaces remain unproved; see STATEMENT-ISSUE.md.
public import SubdiffusiveProcess.Paper.thm_prop_affine_parameters
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Lane2.LimitForm
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
public import SubdiffusiveProcess.Lane4.Inputs
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
public import SubdiffusiveProcess.Lane3.RelativeConcentration
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
public import SubdiffusiveProcess.Lane4.Scaling
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import SubdiffusiveProcess.Sobolev.DomainPoincare

public import SubdiffusiveProcess.Paper.Support.ThmPropBasePart03


@[expose] public section

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
namespace Paper

/-- **Deterministic endpoint step of `mfd:thm-prop`.**  If, for one realization, the two limit forms are
proportional, `F = c E`, on every cube of the family with a common domain, and some cube carries a
nonzero-energy element of `E`, then the lower endpoint `m` and the upper endpoint `M` of the ratio
(the supremum/infimum of the admissible comparison constants) both equal `c`, so the endpoint gap
vanishes. -/
theorem thm_prop_base {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (c : ℝ) (omega : Ω)
    (hprop : ∀ i : ℕ,
      limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
        ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
          u ∈ limitFormDomain (GE i omega) →
            (limitFormEnergy (GF i omega) u).toReal =
              c * (limitFormEnergy (GE i omega) u).toReal)
    (hnz : aux_thm_prop_nonzero z r hr GE omega) :
    sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = c ∧
      sInf (aux_thm_prop_upperSet z r hr GE GF omega) = c := by
  obtain ⟨i0, u0, hu0, hpos⟩ := hnz
  have hlow : IsGreatest (aux_thm_prop_lowerSet z r hr GE GF omega) c := by
    refine ⟨fun i u hu => ?_, fun a ha => ?_⟩
    · rw [(hprop i).2 u hu]
    · have h := ha i0 u0 hu0
      rw [(hprop i0).2 u0 hu0] at h
      exact le_of_mul_le_mul_right h hpos
  have hup : IsLeast (aux_thm_prop_upperSet z r hr GE GF omega) c := by
    refine ⟨fun i u hu => ?_, fun a ha => ?_⟩
    · rw [(hprop i).2 u hu]
    · have h := ha i0 u0 hu0
      rw [(hprop i0).2 u0 hu0] at h
      exact le_of_mul_le_mul_right h hpos
  exact ⟨hlow.csSup_eq, hup.csInf_eq⟩

end Paper
