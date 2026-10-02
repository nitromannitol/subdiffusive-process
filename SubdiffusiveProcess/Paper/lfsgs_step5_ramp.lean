import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Paper.cell_catalogue
import SubdiffusiveProcess.Paper.good_event
import SubdiffusiveProcess.Paper.lem_finite_good_cell
import SubdiffusiveProcess.Paper.finite_interval_packing
import SubdiffusiveProcess.Paper.paper_responses_bank
import SubdiffusiveProcess.Paper.finite_response_ramp
import SubdiffusiveProcess.Paper.lem_rare_tests
import SubdiffusiveProcess.Paper.lem_finite_trace_tests
import SubdiffusiveProcess.Paper.lem_local_normalizations
import SubdiffusiveProcess.Paper.inputs_EM_witness
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.rem_bank
import SubdiffusiveProcess.Paper.prop_16
import SubdiffusiveProcess.Paper.lfsgs_trace_moments
import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding
import SubdiffusiveProcess.FiniteStopping.WindowPullback
import SubdiffusiveProcess.Paper.lfsgs_theta_band_measurable

/-! This module establishes step5 ramp for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

/-- Cgeom in the finite stopping construction. -/
noncomputable def aux_lfsgs_step5_ramp_Cgeom : ℝ := lem_rare_tests.choose

/-- Cgeom ge4 in the finite stopping construction. -/
theorem aux_lfsgs_step5_ramp_Cgeom_ge4 : 4 ≤ Paper.aux_lfsgs_step5_ramp_Cgeom := lem_rare_tests.choose_spec.1

/-- hRT in the finite stopping construction. -/
def aux_lfsgs_step5_ramp_hRT := lem_rare_tests.choose_spec.2

/-- step5 ramp in the finite stopping construction. -/
theorem lfsgs_step5_ramp
    {d : ℕ} (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (T : Type) [Fintype T] [Nonempty T]
    (p q a Cmom Cband : ℝ) (hp : 1 ≤ p) (hpq : p < q) (ha : 0 < a)
    (hCmom : 0 < Cmom) (hCband : 0 < Cband)
    (R0 : T → ℕ → BilateralField d → ℝ) (Rlim0 : T → BilateralField d → ℝ)
    (hmeas0 : ∀ t m, AEStronglyMeasurable (R0 t m) (chaosSampleLaw model).toMeasure)
    (hlimmeas0 : ∀ t, AEStronglyMeasurable (Rlim0 t) (chaosSampleLaw model).toMeasure)
    (hmem0 : ∀ t m, MemLp (R0 t m) (ENNReal.ofReal q) (chaosSampleLaw model).toMeasure)
    (hmom0 : ∀ t m, eLpNorm (R0 t m) (ENNReal.ofReal q) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cmom)
    (hconv0 : ∀ t, TendstoInMeasure (chaosSampleLaw model).toMeasure (R0 t) atTop (Rlim0 t))
    (hband0 : ∀ t m (Hb : ℕ),
      eLpNorm (fun tau => R0 t m tau -
          ((chaosSampleLaw model).toMeasure[R0 t m |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hb]) tau)
        (ENNReal.ofReal p) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (Hb : ℝ))))
    (eta : ℝ) (heta : 0 < eta) (B : ℝ) (hB : 0 < B)
    (hmargin : Paper.aux_lfsgs_step5_ramp_Cgeom * B < a * p * Real.log 3) :
    ∃ H0 m0 : ℕ, 0 < H0 ∧
    ∀ (k : ℕ) (z : SpatialCoordinates d) (m : ℕ), m0 ≤ m →
      ∃ W : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
            ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                C(SpatialCoordinates d, ℝ)))] (W h)) ∧
        (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (W h) ≤
          ENNReal.ofReal (Real.exp (-(B * (h : ℝ))))) ∧
        (∀ h : ℕ+, (h : ℕ) < H0 → W h = ∅) ∧
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
          omega ∉ (⋃ h : ℕ+, W h) →
          ∀ t : T, |R0 t m (aux_lem_local_normalizations_Theta k z omega) -
            Rlim0 t (aux_lem_local_normalizations_Theta k z omega)| ≤ eta) := by
  classical
  set P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure with hPdef
  obtain ⟨hRlimprops, hramp⟩ := finite_response_ramp
    (Y := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
    (laws := fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) j :
      Measure C(SpatialCoordinates d, ℝ)))
    T p q a Cmom Cband hp hpq ha hCmom hCband R0 Rlim0
    hmeas0 hlimmeas0 hmem0 hmom0 hconv0 hband0
  obtain ⟨Cstar, hCstarpos, hXprops⟩ := hramp eta heta
  set Xm : ℕ → BilateralField d → ℝ :=
    fun m tau => min 1 ((Finset.univ.sup' Finset.univ_nonempty
      (fun t : T => |R0 t m tau - Rlim0 t tau|)) / eta) with hXmdef
  have hXm01 : ∀ m tau, Xm m tau ∈ Set.Icc (0 : ℝ) 1 := fun m tau => hXprops.1 (some m) none tau
  have hXmmeas : ∀ m, AEStronglyMeasurable (Xm m) P := fun m => hXprops.2.1 (some m) none
  have hXmInt : ∀ m, Integrable (Xm m) P := fun m =>
    (memLp_of_bounded (ae_of_all P (hXm01 m)) (hXmmeas m) 1).integrable le_rfl
  set R0mk : T → ℕ → BilateralField d → ℝ := fun t m => (hmeas0 t m).mk (R0 t m) with hR0mkdef
  set Rlim0mk : T → BilateralField d → ℝ := fun t => (hlimmeas0 t).mk (Rlim0 t) with hRlim0mkdef
  have hR0mkMeas : ∀ t m, Measurable (R0mk t m) := fun t m => (hmeas0 t m).measurable_mk
  have hRlim0mkMeas : ∀ t, Measurable (Rlim0mk t) := fun t => (hlimmeas0 t).measurable_mk
  have hR0eq : ∀ t m, R0 t m =ᵐ[P] R0mk t m := fun t m => (hmeas0 t m).ae_eq_mk
  have hRlim0eq : ∀ t, Rlim0 t =ᵐ[P] Rlim0mk t := fun t => (hlimmeas0 t).ae_eq_mk
  set Xm' : ℕ → BilateralField d → ℝ :=
    fun m tau => min 1 ((Finset.univ.sup' Finset.univ_nonempty
      (fun t : T => |R0mk t m tau - Rlim0mk t tau|)) / eta) with hXm'def
  have hXm'meas : ∀ m, Measurable (Xm' m) := by
    intro m
    apply Measurable.min measurable_const
    apply Measurable.div _ measurable_const
    have hpt : (fun tau => Finset.univ.sup' Finset.univ_nonempty
        (fun t : T => |R0mk t m tau - Rlim0mk t tau|)) =
        Finset.univ.sup' Finset.univ_nonempty
          (fun t : T => fun tau => |R0mk t m tau - Rlim0mk t tau|) := by
      funext tau
      rw [Finset.sup'_apply]
    rw [hpt]
    apply Finset.measurable_sup' Finset.univ_nonempty
    intro t _
    exact ((hR0mkMeas t m).sub (hRlim0mkMeas t)).abs
  have hall : ∀ m, ∀ᵐ tau ∂P, ∀ t : T,
      R0mk t m tau = R0 t m tau ∧ Rlim0mk t tau = Rlim0 t tau := by
    intro m
    rw [ae_all_iff]
    intro t
    filter_upwards [hR0eq t m, hRlim0eq t] with tau h1 h2 using ⟨h1.symm, h2.symm⟩
  have hXeq : ∀ m, Xm' m =ᵐ[P] Xm m := by
    intro m
    filter_upwards [hall m] with tau htau
    show (min 1 ((Finset.univ.sup' Finset.univ_nonempty
        (fun t : T => |R0mk t m tau - Rlim0mk t tau|)) / eta)) =
      (min 1 ((Finset.univ.sup' Finset.univ_nonempty
        (fun t : T => |R0 t m tau - Rlim0 t tau|)) / eta))
    have hfun : (fun t : T => |R0mk t m tau - Rlim0mk t tau|) =
        (fun t : T => |R0 t m tau - Rlim0 t tau|) := by
      funext t
      rw [(htau t).1, (htau t).2]
    rw [hfun]
  have hXm'01 : ∀ m tau, Xm' m tau ∈ Set.Icc (0 : ℝ) 1 := by
    intro m tau
    have hsupnn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun t : T => |R0mk t m tau - Rlim0mk t tau|) :=
      le_trans (abs_nonneg (R0mk (Classical.arbitrary T) m tau - Rlim0mk (Classical.arbitrary T) tau))
        (Finset.le_sup' (fun t : T => |R0mk t m tau - Rlim0mk t tau|)
          (Finset.mem_univ (Classical.arbitrary T)))
    refine ⟨le_min (by norm_num) (div_nonneg hsupnn heta.le), min_le_left _ _⟩
  have hXm'band : ∀ m Hb : ℕ, eLpNorm (fun tau => Xm' m tau -
      (P[Xm' m | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hb]) tau)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-a * (Hb : ℝ))) := by
    intro m Hb
    have hce : (P[Xm' m | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hb]) =ᵐ[P]
        (P[Xm m | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hb]) :=
      condExp_congr_ae (hXeq m)
    have hdiffeq : (fun tau => Xm' m tau -
          (P[Xm' m | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hb]) tau) =ᵐ[P]
        (fun tau => Xm m tau -
          (P[Xm m | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hb]) tau) := by
      filter_upwards [hXeq m, hce] with tau h1 h2
      rw [h1, h2]
    rw [eLpNorm_congr_ae hdiffeq]
    exact hXprops.2.2.1 (some m) none Hb
  have hXmtend0 : ∀ eps : ℝ, 0 < eps → ∃ m0 : ℕ, ∀ m, m0 ≤ m → ∫ tau, Xm m tau ∂P < eps := by
    intro eps heps
    obtain ⟨m0, hm0⟩ := hXprops.2.2.2 eps heps
    exact ⟨m0, fun m hm => hm0 (some m) none
      (fun n hn => by rw [Option.some_inj] at hn; omega)
      (fun n hn => absurd hn (by simp only [reduceCtorEq, not_false_eq_true]))⟩
  have hXmItendsto : Tendsto (fun m => ∫ tau, Xm m tau ∂P) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨m0, hm0⟩ := hXmtend0 eps heps
    exact ⟨m0, fun m hm => by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun tau => (hXm01 m tau).1))]
      exact hm0 m hm⟩
  have hXmeLpeq : ∀ m, eLpNorm (Xm m) 1 P = ENNReal.ofReal (∫ tau, Xm m tau ∂P) := by
    intro m
    rw [eLpNorm_one_eq_lintegral_enorm,
      ofReal_integral_eq_lintegral_ofReal (hXmInt m) (ae_of_all P (fun tau => (hXm01 m tau).1))]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_of_all P (fun tau => (hXm01 m tau).1)] with tau htau
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg htau]
  have hXmeLptendsto : Tendsto (fun m => eLpNorm (Xm m) 1 P) atTop (nhds 0) := by
    have heq2 : (fun m => eLpNorm (Xm m) 1 P) = fun m => ENNReal.ofReal (∫ tau, Xm m tau ∂P) :=
      funext hXmeLpeq
    rw [heq2]
    have hcont := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hXmItendsto
    simpa only [ENNReal.ofReal_zero] using hcont
  have hprobXm : TendstoInMeasure P Xm atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞)) one_ne_zero hXmmeas
      aestronglyMeasurable_const
    have heq4 : ∀ n : ℕ, Xm n - (fun _ : BilateralField d => (0 : ℝ)) = Xm n := fun n => sub_zero _
    simp only [heq4]
    exact hXmeLptendsto
  have hprobXm' : TendstoInMeasure P Xm' atTop (fun _ => (0 : ℝ)) :=
    TendstoInMeasure.congr_left (fun m => (hXeq m).symm) hprobXm
  obtain ⟨H0, m0, hH0pos, hWfun⟩ := Paper.aux_lfsgs_step5_ramp_hRT d (by omega) P (0 : ℤ) Xm'
    hXm'01 hXm'meas hprobXm' Cstar a p hCstarpos ha hp
    (fun m H => by
      show eLpNorm (fun tau => Xm' m tau -
          (P[Xm' m | MeasurableSpace.comap
            ((Set.Icc ((0 : ℤ) - (H : ℤ)) ((0 : ℤ) + (H : ℤ))).restrict) inferInstance]) tau)
        (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))
      have hset : Set.Icc ((0 : ℤ) - (H : ℤ)) ((0 : ℤ) + (H : ℤ)) =
          SubdiffusiveProcess.Lane3.bandSet H := by
        simp only [zero_sub, zero_add, bandSet]
      rw [hset, ← bandSigma_eq_comap]
      simpa only [ge_iff_le, neg_mul] using hXm'band m H)
    B hB hmargin
  refine ⟨H0, m0, hH0pos, ?_⟩
  intro k z m hm
  obtain ⟨W0, hW0meas, hW0prob, hW0empty, hW0ae⟩ := hWfun m hm
  have hΘ : MeasurePreserving (aux_lem_local_normalizations_Theta k z) P P :=
    aux_lem_local_normalizations_Theta_measurePreserving model k z
  have hQ : ∀ᵐ tau ∂P, tau ∉ ⋃ h : ℕ+, W0 h →
      ∀ t : T, |R0 t m tau - Rlim0 t tau| ≤ eta := by
    filter_upwards [hW0ae, hall m] with tau hW0tau hallt hnotin
    have hXm'le : Xm' m tau ≤ 1 / 2 := by
      by_contra hgt
      push_neg at hgt
      exact hnotin (hW0tau hgt)
    have hsup_le : (Finset.univ.sup' Finset.univ_nonempty
        (fun t' : T => |R0mk t' m tau - Rlim0mk t' tau|)) ≤ eta / 2 := by
      rcases (min_le_iff.mp hXm'le) with h1 | h2
      · norm_num at h1
      · linarith only [hd, hp, hpq, ha, hCmom, hCband, heta, hB, hmargin, hPdef, hCstarpos, hXmdef, hR0mkdef, hRlim0mkdef, hXm'def, hH0pos, hm, hnotin, hXm'le, h2, (div_le_iff₀ heta).mp h2]
    intro t
    have ht_le : |R0mk t m tau - Rlim0mk t tau| ≤ eta / 2 :=
      le_trans (Finset.le_sup' (fun t' : T => |R0mk t' m tau - Rlim0mk t' tau|)
        (Finset.mem_univ t)) hsup_le
    have heqt : |R0 t m tau - Rlim0 t tau| = |R0mk t m tau - Rlim0mk t tau| := by
      rw [(hallt t).1, (hallt t).2]
    rw [heqt]
    linarith only [hd, hp, hpq, ha, hCmom, hCband, heta, hB, hmargin, hPdef, hCstarpos, hXmdef, hR0mkdef, hRlim0mkdef, hXm'def, hH0pos, hm, hnotin, hXm'le, hsup_le, ht_le, heqt]
  have hicc0 : ∀ h : ℕ+, Set.Icc ((0 : ℤ) - 2 * (h : ℤ)) ((0 : ℤ) + (h : ℤ)) =
      Set.Icc (-2 * (h : ℤ)) (h : ℤ) := fun h => by congr 1 <;> ring
  have hW0meas' : ∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
      ((Set.Icc (-2 * (h : ℤ)) (h : ℤ)).restrict) inferInstance] (W0 h) := by
    intro h
    have hW0meash := hW0meas h
    rwa [hicc0 h] at hW0meash
  have hicc : ∀ h : ℕ+, Set.Icc (-2 * (h : ℤ) - (k : ℤ)) ((h : ℤ) - (k : ℤ)) =
      Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ)) := fun h => by congr 1 <;> ring
  obtain ⟨W, hWmeas, hWprob, hWempty, hWae⟩ := SubdiffusiveProcess.FiniteStopping.window_pullback P
    (aux_lem_local_normalizations_Theta k z) hΘ
    (fun h => MeasurableSpace.comap ((Set.Icc (-2 * (h : ℤ)) (h : ℤ)).restrict) inferInstance)
    (fun h => MeasurableSpace.comap
      ((Set.Icc (-2 * (h : ℤ) - (k : ℤ)) ((h : ℤ) - (k : ℤ))).restrict) inferInstance)
    (fun h => (measurable_restrict _).comap_le)
    (fun h => Paper.lfsgs_theta_band_measurable k z (-2 * (h : ℤ)) (h : ℤ))
    W0 hW0meas' B H0 hW0prob hW0empty
    (fun tau => ∀ t : T, |R0 t m tau - Rlim0 t tau| ≤ eta) hQ
  refine ⟨W, fun h => ?_, hWprob, hWempty, hWae⟩
  have hWmeas' := hWmeas h
  rwa [hicc h] at hWmeas'

end Paper
