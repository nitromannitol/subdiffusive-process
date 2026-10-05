module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.lem_finite_good_cell
public import SubdiffusiveProcess.Paper.finite_interval_packing
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.Paper.finite_response_ramp
public import SubdiffusiveProcess.Paper.lem_rare_tests
public import SubdiffusiveProcess.Paper.lem_finite_trace_tests
public import SubdiffusiveProcess.Paper.lem_local_normalizations
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.lfsgs_trace_moments
public import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
public import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
public import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding
public import SubdiffusiveProcess.FiniteStopping.QuotientNormBounds
public import SubdiffusiveProcess.FiniteStopping.TraceRescaling
public import SubdiffusiveProcess.Paper.lfsgs_quotientCBetaNorm_congr_on
public import SubdiffusiveProcess.Paper.lfsgs_sub_mem_killed_of_boundary_eq

@[expose] public section

/-! This module establishes normalized Aext seminorm for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- isHolderOn dilation transfer in the finite stopping construction. -/
theorem aux_lfsgs_normalized_Aext_seminorm_isHolderOn_dilation_transfer {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (U0 : SpatialCoordinates d → ℝ)
    (hU0 : IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
      U0) :
    IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d)))
      (U0 ∘ cubeDilation 0 z r⁻¹) := by
  obtain ⟨Mb, hMb⟩ := hU0
  refine ⟨r ^ (-beta) * Mb, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  set x' := cubeDilation 0 z r⁻¹ x with hx'def
  set y' := cubeDilation 0 z r⁻¹ y with hy'def
  have hx'mem : x' ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) := aux_lem_local_normalizations_inv_frontier z hr x hx
  have hy'mem : y' ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) := aux_lem_local_normalizations_inv_frontier z hr y hy
  have hx'y' : x' ≠ y' := by
    intro he
    apply hxy
    have hcong := congrArg (cubeDilation z 0 r) he
    rwa [aux_lem_local_normalizations_dil_inv z hr, aux_lem_local_normalizations_dil_inv z hr]
      at hcong
  have hxy'diff : ∀ j : Fin d, x j - y j = r * (x' j - y' j) := by
    intro j
    have hxj : x' j = r⁻¹ * (x j - z j) := by simp only [hx'def, cubeDilation_apply, Pi.zero_apply, zero_add]
    have hyj : y' j = r⁻¹ * (y j - z j) := by simp only [hy'def, cubeDilation_apply, Pi.zero_apply, zero_add]
    rw [hxj, hyj]
    field_simp
    ring
  have hsum_eq : (∑ j : Fin d, (x j - y j) ^ 2) = r ^ 2 * (∑ j : Fin d, (x' j - y' j) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [hxy'diff j]; ring)
  have hsqrt_eq : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
      r * Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2) := by
    rw [hsum_eq, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  have hmem : |U0 x' - U0 y'| / (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta ∈
      holderRatioSet beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) U0 :=
    ⟨x', hx'mem, y', hy'mem, hx'y', rfl⟩
  have hle := hMb hmem
  have hgoal_eq : |(U0 ∘ cubeDilation 0 z r⁻¹) x - (U0 ∘ cubeDilation 0 z r⁻¹) y| /
      (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta =
      r ^ (-beta) *
        (|U0 x' - U0 y'| / (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta) := by
    show |U0 x' - U0 y'| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta = _
    rw [hsqrt_eq, Real.mul_rpow hr.le (Real.sqrt_nonneg _), Real.rpow_neg hr.le,
      div_mul_eq_div_div_swap, ← div_eq_inv_mul]
  rw [hgoal_eq]
  exact mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hr.le _)

/-- dirichletResponse eq sInf in the finite stopping construction. -/
theorem aux_lfsgs_normalized_Aext_seminorm_dirichletResponse_eq_sInf
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x) :
    dirichletResponse (killedResponseSpace hP) a b =
      sInf (aux_lem_local_normalizations_Lset z r hr a g) := by
  apply le_antisymm
  · apply le_csInf
    · exact ⟨sobolevCoefficientForm a b.val b.val, ⟨b, G, hGc, hb, hGg, rfl⟩⟩
    · rintro e ⟨u, U, hUc, hurep, hUg, rfl⟩
      have hbdry : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = G x :=
        fun x hx => (hUg x hx).trans (hGg x hx).symm
      have hsub : u.val - b.val ∈ killedSobolevGraph (centeredCube z r hr) :=
        _root_.SubdiffusiveProcess.Paper.lfsgs_sub_mem_killed_of_boundary_eq hd z r hr u b U G hUc hGc
          hurep hb hbdry
      have hmem : sobolevCoefficientForm a u.val u.val ∈
          Set.range (fun w : (killedResponseSpace hP).space =>
            sobolevCoefficientForm a (b.val + w.val) (b.val + w.val)) := by
        refine ⟨⟨u.val - b.val, hsub⟩, ?_⟩
        show sobolevCoefficientForm a (b.val + (u.val - b.val)) (b.val + (u.val - b.val)) =
          sobolevCoefficientForm a u.val u.val
        have heq2 : b.val + (u.val - b.val) = u.val := by abel
        rw [heq2]
      exact (dirichletResponse_isLeast (killedResponseSpace hP) a b).2 hmem
  · exact aux_lem_local_normalizations_sInf_le_response z r hr hP a b g G hGc hb hGg

/-- normalized Aext seminorm in the finite stopping construction. -/
theorem lfsgs_normalized_Aext_seminorm
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sf : SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (aQ : PositiveCoefficient (centeredCube z r hr))
    (aU : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (s Aext : ℝ) (hs : 0 < s) (hAext : 0 < Aext)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hscale : ∀ g : SpatialCoordinates d → ℝ,
      sInf (aux_lem_local_normalizations_Lset z r hr aQ g) =
        r ^ ((d : ℝ) - 2) * s *
          sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aU (g ∘ cubeDilation z 0 r)))
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (hClauseAext : ∀ (b : weakSobolevGraph (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      ∀ c : ℝ, dirichletResponse (killedResponseSpace hP) aQ b ≤
        Aext * r ^ ((d : ℝ) - 2) * s *
          (cAlphaNorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
            Set (SpatialCoordinates d))) (fun x => G (z + r • x) - c)) ^ 2) :
    ∃ q : Seminorm ℝ (SpatialCoordinates d → ℝ),
      (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
        (q g) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aU g)) ∧
      (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
        (q g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2) := by
  obtain ⟨q, hq⟩ := _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_seminorm hd Sf beta hbeta aU
  refine ⟨q, hq, ?_⟩
  intro g hg
  have hg' := hg
  obtain ⟨hHold0, -⟩ := hg'
  rw [SubdiffusiveProcess.FiniteStopping.rescaledDatum_unit] at hHold0
  obtain ⟨b0, U0, hU0cont, hb0rep, hU0g, -⟩ :=
    Sf.traceRightInverse beta hbeta 0 1 one_pos rfl g hHold0
  have hU0Hold : IsHolderOn beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) U0 := by
    unfold IsHolderOn
    rw [aux_lem_local_normalizations_holderRatio_congr beta _ U0 g hU0g]
    exact hHold0
  obtain ⟨b, hbval⟩ := aux_lem_as_regularity_affine_transport_weak_pushforward d z 0 r hr one_pos b0
  set G : SpatialCoordinates d → ℝ := U0 ∘ cubeDilation 0 z r⁻¹ with hGdef
  have hGcont : Continuous G := hU0cont.comp (continuous_cubeDilation 0 z r⁻¹)
  have hGholder : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G :=
    _root_.SubdiffusiveProcess.Paper.aux_lfsgs_normalized_Aext_seminorm_isHolderOn_dilation_transfer beta z r hr U0 hU0Hold
  have hbrep : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G := by
    apply (aux_lem_local_normalizations_ae_iff z hr
      (fun x => ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) x =
        G x)).2
    filter_upwards [hbval, hb0rep] with x h1 h2
    show ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        (cubeDilation z 0 r x) = G (cubeDilation z 0 r x)
    rw [hGdef]
    show _ = U0 (cubeDilation 0 z r⁻¹ (cubeDilation z 0 r x))
    rw [aux_lem_local_normalizations_inv_dil z hr]
    rw [← h1, h2]
  have hinvdil_apply : ∀ x : SpatialCoordinates d,
      cubeDilation 0 z r⁻¹ (cubeDilation z 0 r x) = x := aux_lem_local_normalizations_inv_dil z hr
  have hGT : ∀ x : SpatialCoordinates d, G (z + r • x) = U0 x := by
    intro x
    have hTeq : z + r • x = cubeDilation z 0 r x := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cubeDilation, Pi.zero_apply, sub_zero]
    rw [hTeq, hGdef]
    show U0 (cubeDilation 0 z r⁻¹ (cubeDilation z 0 r x)) = U0 x
    rw [hinvdil_apply]
  set gDR : SpatialCoordinates d → ℝ := g ∘ cubeDilation 0 z r⁻¹ with hgDRdef
  have hgDR_T : gDR ∘ cubeDilation z 0 r = g := by
    funext x
    show g (cubeDilation 0 z r⁻¹ (cubeDilation z 0 r x)) = g x
    rw [hinvdil_apply]
  have hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = gDR x := by
    intro x hx
    have hx'mem : cubeDilation 0 z r⁻¹ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1
        one_pos : Set (SpatialCoordinates d)) := aux_lem_local_normalizations_inv_frontier z hr x hx
    show U0 (cubeDilation 0 z r⁻¹ x) = g (cubeDilation 0 z r⁻¹ x)
    exact hU0g _ hx'mem
  have hresp : dirichletResponse (killedResponseSpace hP) aQ b =
      sInf (aux_lem_local_normalizations_Lset z r hr aQ gDR) :=
    _root_.SubdiffusiveProcess.Paper.aux_lfsgs_normalized_Aext_seminorm_dirichletResponse_eq_sInf hd z r hr hP aQ b gDR G hGcont.continuousOn hbrep hGg
  have hresp2 : dirichletResponse (killedResponseSpace hP) aQ b =
      r ^ ((d : ℝ) - 2) * s * (q g) ^ 2 := by
    rw [hresp, hscale gDR, hgDR_T, hq g hg]
  have hbound_raw := hClauseAext b G hGcont.continuousOn hGholder hbrep
  have hbound : ∀ c : ℝ, dirichletResponse (killedResponseSpace hP) aQ b ≤
      Aext * r ^ ((d : ℝ) - 2) * s * (cAlphaNorm beta (frontier (centeredCube
        (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) (fun x => U0 x - c)) ^ 2 := by
    intro c
    have hfun_eq : (fun x => G (z + r • x) - c) = (fun x => U0 x - c) := by
      funext x; rw [hGT]
    rw [← hfun_eq]
    exact hbound_raw c
  have hA : 0 < r ^ ((d : ℝ) - 2) * s := by positivity
  have hfinal : ∀ c : ℝ, (q g) ^ 2 ≤ Aext * (cAlphaNorm beta (frontier (centeredCube
      (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) (fun x => U0 x - c)) ^ 2 := by
    intro c
    apply SubdiffusiveProcess.FiniteStopping.cancel_pos_left _ _ _ hA
    have heq : Aext * r ^ ((d : ℝ) - 2) * s *
        (cAlphaNorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) (fun x => U0 x - c)) ^ 2 =
        r ^ ((d : ℝ) - 2) * s * (Aext * (cAlphaNorm beta (frontier (centeredCube
          (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
          (fun x => U0 x - c)) ^ 2) := by ring
    rw [← heq, ← hresp2]
    exact hbound c
  have hqfinal := SubdiffusiveProcess.FiniteStopping.forall_c_to_quotient beta (frontier (centeredCube
    (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) U0 ((q g) ^ 2) Aext
    (sq_nonneg _) hAext hfinal
  have hU0g' : quotientCBetaNorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1
      one_pos : Set (SpatialCoordinates d))) U0 =
      quotientCBetaNorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) g :=
    _root_.SubdiffusiveProcess.Paper.lfsgs_quotientCBetaNorm_congr_on beta _ U0 g hU0g
  rw [hU0g'] at hqfinal
  have hcell_eq : cellBoundaryQuotientNorm beta 0 1 g = quotientCBetaNorm beta (frontier
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) g := by
    unfold cellBoundaryQuotientNorm
    rw [SubdiffusiveProcess.FiniteStopping.rescaledDatum_unit]
  rw [hcell_eq]
  exact hqfinal

end SubdiffusiveProcess.Paper
