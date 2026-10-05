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
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
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
public import SubdiffusiveProcess.FiniteStopping.MeasurableVersions

@[expose] public section

/-! This module establishes theta band measurable for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- step4 bank in the finite stopping construction. -/
theorem aux_lfsgs_theta_band_measurable_step4_bank
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (Cp : CampanatoInput d) (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (_Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ q δ0 a : ℝ, p < q ∧ 0 < δ0 ∧ 0 < a ∧ a = aux_prop16_aD d ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization model H),
      model.delta ≤ δ0 →
    ∀ (T : Type) [Fintype T] [Nonempty T]
    (testOf : T → SpatialCoordinates d → ℝ)
    (_htestSmooth : ∀ t, ContDiff ℝ ∞ (testOf t))
    (_hnonconst : ∀ t, ∃ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)), testOf t x ≠ testOf t y)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
        ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w‖)
    (bOf : T → weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (_hbOf : ∀ t, ((bOf t : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))]
        testOf t),
    (    ∃ Cmom Cband : ℝ, 0 < Cmom ∧ 0 < Cband ∧
    ∃ R0 : T → ℕ → BilateralField d → ℝ,
      R0 = (fun t m tau => dirichletResponse (killedResponseSpace hP)
        (cutoffPositiveCoefficient model H tau m (0 : SpatialCoordinates d) one_pos) (bOf t)) ∧
    ∃ Rlim0 : T → BilateralField d → ℝ,
      (∀ t m, AEStronglyMeasurable (R0 t m) (chaosSampleLaw model).toMeasure) ∧
      (∀ t, AEStronglyMeasurable (Rlim0 t) (chaosSampleLaw model).toMeasure) ∧
      (∀ t m, MemLp (R0 t m) (ENNReal.ofReal q) (chaosSampleLaw model).toMeasure) ∧
      (∀ t m, eLpNorm (R0 t m) (ENNReal.ofReal q) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cmom) ∧
      (∀ t, TendstoInMeasure (chaosSampleLaw model).toMeasure (R0 t) atTop (Rlim0 t)) ∧
      ∀ t m (Hb : ℕ),
        eLpNorm (fun tau => R0 t m tau - ((chaosSampleLaw model).toMeasure[R0 t m |
          bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hb]) tau)
          (ENNReal.ofReal p) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (Hb : ℝ)))) := by
  classical
  let instNeZeroDimension : NeZero d := ⟨by omega⟩
  obtain ⟨q, δm, hq, hδm, hmom⟩ :=
    _root_.SubdiffusiveProcess.Paper.lfsgs_trace_moments d hd Jc Pc Xc W Sf D p hp
  obtain ⟨δb, hδb, hband⟩ :=
    _root_.SubdiffusiveProcess.Paper.aux_test_prop16_rd_band d hd Jc Pc Xc W Sf D p hp
  have Interp : CubeFractionalInterpolationInput d hd := by
    constructor
    · intro z r hr threeQuarters hthreeQuarters
      exact classical_cube_fractional_interpolation d hd z r hr threeQuarters hthreeQuarters
    · intro z r hr threeQuarters hthreeQuarters w M hbound
      exact classical_cube_fractional_compact_embedding d hd z r hr threeQuarters
        hthreeQuarters w M hbound
  obtain ⟨δa, hδa, hLN⟩ :=
    _root_.SubdiffusiveProcess.Paper.lem_local_normalizations d hd Jc Pc Xc Sf W Cp D hES Step Interp
      (fun z r hr F => inputs_EM_witness d z r hr F) (3 / 4) (by norm_num) (by norm_num)
  have ha : 0 < aux_prop16_aD d := by
    unfold aux_prop16_aD
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have ht : 0 < (d : ℝ) - 1 / 2 := by linarith only [hd, hp, hq, hδm, hδb, hδa, hdreal]
    have ht2 : 0 < (d : ℝ) - 1 / 2 - (d : ℝ) + 1 := by ring_nf; norm_num
    have hden : 0 < (d : ℝ) - 1 / 2 + 1 := by linarith only [hd, hp, hq, hδm, hδb, hδa, hdreal, ht, ht2]
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    change 0 < ((d : ℝ) - 1 / 2) * (((d : ℝ) - 1 / 2) - (d : ℝ) + 1) /
      (((d : ℝ) - 1 / 2) + 1) / (8 * Real.log 3)
    positivity
  refine ⟨q, min 1 (min δm (min δb δa)), aux_prop16_aD d, hq, ?_, ha, rfl, ?_⟩
  · exact lt_min zero_lt_one (lt_min hδm (lt_min hδb hδa))
  · intro model Rm Sreg It H hH hdelta T _ _ testOf htestSmooth hnonconst hP bOf hbOf
    have hdeltaOne : model.delta ≤ 1 := le_trans hdelta (min_le_left _ _)
    have hdm : model.delta ≤ min 1 δm := le_min hdeltaOne
      (le_trans hdelta ((min_le_right 1 (min δm (min δb δa))).trans
        (min_le_left δm (min δb δa))))
    have hdb : model.delta ≤ min 1 δb := le_min hdeltaOne
      (le_trans hdelta ((min_le_right 1 (min δm (min δb δa))).trans
        ((min_le_right δm (min δb δa)).trans (min_le_left δb δa))))
    have hda : model.delta ≤ min 1 δa := le_min hdeltaOne
      (le_trans hdelta ((min_le_right 1 (min δm (min δb δa))).trans
        ((min_le_right δm (min δb δa)).trans (min_le_right δb δa))))
    obtain ⟨Cmom, hCmom, hmom0⟩ := hmom model Rm Sreg It H hH hdm T hP testOf htestSmooth bOf hbOf
    have hbandEach : ∀ t : T, ∃ Ct : ℝ, 0 < Ct ∧ ∀ (h m : ℕ),
        eLpNorm (fun tau =>
          dirichletResponse (killedResponseSpace hP)
            (cutoffPositiveCoefficient model H tau m (0 : SpatialCoordinates d) one_pos) (bOf t) -
          ((chaosSampleLaw model).toMeasure[
            (fun tau => dirichletResponse (killedResponseSpace hP)
              (cutoffPositiveCoefficient model H tau m (0 : SpatialCoordinates d) one_pos) (bOf t)) |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) tau)
          (ENNReal.ofReal p) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (Ct * model.delta * (3 : ℝ) ^ (-aux_prop16_aD d * (h : ℝ))) := by
      intro t
      obtain ⟨Ct, hCt, hCtall⟩ := hband 0 1 one_pos (by norm_num) hP (testOf t) (htestSmooth t)
        (hnonconst t) (bOf t) (hbOf t) model Rm Sreg It H hH hdb
      exact ⟨Ct, hCt, hCtall⟩
    choose Ct hCt hCtall using hbandEach
    let Cband : ℝ := 1 + ∑ t, Ct t
    have hCband : 0 < Cband := by
      dsimp [Cband]
      exact add_pos zero_lt_one (Finset.sum_pos (fun t _ => hCt t) Finset.univ_nonempty)
    have hCt_le : ∀ t : T, Ct t ≤ ∑ t, Ct t := by
      intro t
      exact Finset.single_le_sum (fun x _ => le_of_lt (hCt x)) (Finset.mem_univ t)
    have hCbandBound : ∀ t : T, Ct t ≤ Cband := by
      intro t
      dsimp [Cband]
      linarith only [hd, hp, hq, hδm, hδb, hδa, ha, hdelta, hdeltaOne, hdm, hdb, hda, hCmom, hCband, hCt_le t]
    obtain ⟨e, RL, he, hLam, hRLbound, hRLpos, hThetaMP, hHidentity, hscale⟩ :=
      hLN model Rm Sreg It H hH hda
    let R0 : T → ℕ → BilateralField d → ℝ := fun t m tau =>
      dirichletResponse (killedResponseSpace hP)
        (cutoffPositiveCoefficient model H tau m (0 : SpatialCoordinates d) one_pos) (bOf t)
    let RlimRaw : T → BilateralField d → ℝ := fun t tau =>
      (RL 0 1 one_pos tau (testOf t)) ^ 2
    have hpoint : ∀ t m tau, R0 t m tau =
        aux_lem_local_normalizations_Lam model H 0 1 one_pos m tau (testOf t) := by
      intro t m tau
      dsimp [R0, aux_lem_local_normalizations_Lam]
      exact (aux_lem_local_normalizations_Lam_eq_response hd model H tau m
        (0 : SpatialCoordinates d) one_pos hP
        (cutoffPositiveCoefficient model H tau m (0 : SpatialCoordinates d) one_pos)
        (bOf t) (testOf t) (testOf t) (htestSmooth t).continuous.continuousOn
        (hbOf t) (fun _ _ => rfl) rfl).symm
    have hconvRaw : ∀ t, TendstoInMeasure (chaosSampleLaw model).toMeasure (R0 t) atTop
        (RlimRaw t) := by
      intro t
      have hclass := aux_lem_local_normalizations_smooth_class (3 / 4)
        (by norm_num : (3 / 4 : ℝ) ≤ 1) 0 1 (testOf t) (htestSmooth t)
      have hlim := hLam 0 1 one_pos (testOf t) ⟨0, by norm_num⟩ hclass
      have hseq : R0 t = fun m tau =>
          aux_lem_local_normalizations_Lam model H 0 1 one_pos m tau (testOf t) := by
        funext m tau
        exact hpoint t m tau
      rw [hseq]
      exact hlim
    let Rlim0 : T → BilateralField d → ℝ := fun t =>
      Classical.choose (SubdiffusiveProcess.FiniteStopping.measurable_version (chaosSampleLaw model).toMeasure
        (R0 t) (fun m => (hmom0 t m).1.aestronglyMeasurable.aemeasurable)
        (RlimRaw t) (hconvRaw t))
    have hlimmeas0 : ∀ t, Measurable (Rlim0 t) := by
      intro t
      exact (Classical.choose_spec (SubdiffusiveProcess.FiniteStopping.measurable_version
        (chaosSampleLaw model).toMeasure (R0 t)
        (fun m => (hmom0 t m).1.aestronglyMeasurable.aemeasurable)
        (RlimRaw t) (hconvRaw t))).1
    have hlimAE : ∀ t, Rlim0 t =ᵐ[(chaosSampleLaw model).toMeasure] RlimRaw t := by
      intro t
      exact (Classical.choose_spec (SubdiffusiveProcess.FiniteStopping.measurable_version
        (chaosSampleLaw model).toMeasure (R0 t)
        (fun m => (hmom0 t m).1.aestronglyMeasurable.aemeasurable)
        (RlimRaw t) (hconvRaw t))).2
    have hconv0 : ∀ t, TendstoInMeasure (chaosSampleLaw model).toMeasure (R0 t) atTop (Rlim0 t) := by
      intro t
      exact (hconvRaw t).congr_right (hlimAE t).symm
    refine ⟨Cmom, Cband, hCmom, hCband, R0, rfl, ?_⟩
    refine ⟨Rlim0, ?_, ?_, ?_, ?_, hconv0, ?_⟩
    · intro t m
      exact (hmom0 t m).1.aestronglyMeasurable
    · intro t
      exact (hlimmeas0 t).aestronglyMeasurable
    · intro t m
      exact (hmom0 t m).1
    · intro t m
      exact (hmom0 t m).2
    · intro t m h
      have hh := hCtall t h m
      apply hh.trans
      apply ENNReal.ofReal_le_ofReal
      have hpow : 0 ≤ (3 : ℝ) ^ (-aux_prop16_aD d * (h : ℝ)) := by positivity
      calc
        Ct t * model.delta * (3 : ℝ) ^ (-aux_prop16_aD d * (h : ℝ)) ≤
            Ct t * 1 * (3 : ℝ) ^ (-aux_prop16_aD d * (h : ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ hpow
              nlinarith only [hd, hp, hq, hδm, hδb, hδa, ha, hdelta, hdeltaOne, hdm, hdb, hda, hCmom, hCband, hh, hpow, hCt t, hdeltaOne]
        _ ≤ Cband * (3 : ℝ) ^ (-aux_prop16_aD d * (h : ℝ)) := by
              rw [mul_one]
              exact mul_le_mul_of_nonneg_right (hCbandBound t) hpow

/-- theta band measurable in the finite stopping construction. -/
theorem lfsgs_theta_band_measurable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (k : ℕ) (z : SpatialCoordinates d) (a b : ℤ) :
    @Measurable (BilateralField d) (BilateralField d)
      (MeasurableSpace.comap ((Set.Icc (a - (k : ℤ)) (b - (k : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (a - (k : ℤ)) (b - (k : ℤ))) → C(SpatialCoordinates d, ℝ))))
      (MeasurableSpace.comap ((Set.Icc a b).domRestrict)
        (inferInstance : MeasurableSpace ((i : Set.Icc a b) → C(SpatialCoordinates d, ℝ))))
      (aux_lem_local_normalizations_Theta k z) := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_comp]
  let G : ((i : Set.Icc (a - (k:ℤ)) (b - (k:ℤ))) → C(SpatialCoordinates d, ℝ)) →
          ((i : Set.Icc a b) → C(SpatialCoordinates d, ℝ)) :=
    fun f i => (f ⟨(i:ℤ) - k, by obtain ⟨hi1, hi2⟩ := i.2; exact ⟨by omega, by omega⟩⟩).comp
      (aux_lem_local_normalizations_T k z)
  have hcomp : ((Set.Icc a b).domRestrict ∘ aux_lem_local_normalizations_Theta k z)
      = G ∘ (Set.Icc (a - (k:ℤ)) (b - (k:ℤ))).domRestrict := by rfl
  have hG : @Measurable _ _ inferInstance inferInstance G := by measurability
  rw [hcomp, ← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono
  rw [← measurable_iff_comap_le]
  exact hG

end SubdiffusiveProcess.Paper
