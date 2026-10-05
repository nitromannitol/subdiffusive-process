module

public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.LinearAlgebra.DFinsupp
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.common_trace_class
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.prop_gluing_replacement
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.lem_replace_harmonic_projection
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_represented_mosco
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling
public import SubdiffusiveProcess.Paper.lane4_coercivity_dilation
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.Sobolev.FractionalRepresentatives
public import SubdiffusiveProcess.Main.CubeFractionalL2Seminorm
public import SubdiffusiveProcess.Sobolev.CoordinateL2Integral

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Riesz representation on an abstract carrier, with completeness stated in
terms of the proposed inner product. Keeping the carrier abstract prevents a
pre-existing ambient norm from being selected for the energy-space instances. -/
theorem aux_lem_replace_riesz_from_complete_core
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (core : InnerProductSpace.Core ℝ V)
    (hcomplete : ∀ v : ℕ → V,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p, N ≤ p → ∀ q, N ≤ q →
        core.inner (v p - v q) (v p - v q) < ε) →
      ∃ w : V, Tendsto (fun n => core.inner (v n - w) (v n - w)) atTop (𝓝 0))
    (L : V →ₗ[ℝ] ℝ) (C : ℝ)
    (hbound : ∀ v, |L v| ≤ C * Real.sqrt (core.inner v v)) :
    ∃ p : V, ∀ v : V, core.inner p v = L v := by
  let : NormedAddCommGroup V := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore
  have hnorm (v : V) : ‖v‖ ^ 2 = core.inner v v :=
    (real_inner_self_eq_norm_sq v).symm
  let : CompleteSpace V := by
    apply Metric.complete_of_cauchySeq_tendsto
    intro v hv
    obtain ⟨w, hw⟩ := hcomplete v (by
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hv _ (Real.sqrt_pos.2 hε)
      refine ⟨N, fun p hp q hq => ?_⟩
      have hdist := hN p hp q hq
      rw [dist_eq_norm] at hdist
      have hsq := (sq_lt_sq₀ (norm_nonneg (v p - v q)) (Real.sqrt_nonneg ε)).2 hdist
      rwa [hnorm, Real.sq_sqrt hε.le] at hsq)
    refine ⟨w, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hw
    change Tendsto (fun n => Real.sqrt (core.inner (v n - w) (v n - w)))
      atTop (𝓝 (Real.sqrt 0)) at hs
    have heq : (fun n => Real.sqrt (core.inner (v n - w) (v n - w))) =
        (fun n => ‖v n - w‖) := by
      funext n
      rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    rw [heq, Real.sqrt_zero] at hs
    exact hs
  let f : V →L[ℝ] ℝ := L.mkContinuous C (by
    intro v
    change ‖L v‖ ≤ C * ‖v‖
    simpa only [Real.norm_eq_abs, ← hnorm, Real.sqrt_sq (norm_nonneg _)] using hbound v)
  let p : V := (InnerProductSpace.toDual ℝ V).symm f
  refine ⟨p, fun v => ?_⟩
  change (InnerProductSpace.toDual ℝ V p) v = f v
  exact congrArg (fun g : V →L[ℝ] ℝ => g v)
    ((InnerProductSpace.toDual ℝ V).apply_symm_apply f)

/-- Coercivity makes the killed domain complete for the bare form. Its Riesz
representative is the harmonic projection required by the replacement proof.
Reuses the stopped killed-domain core construction and sequential completeness proof. -/
theorem aux_lem_replace_projection_exists {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    {U : Set (SpatialCoordinates d)}
    {D : Submodule ℝ (DomainL2 Q)} (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D)
    (hPoin : ∃ C : ℝ, 0 < C ∧ ∀ v ∈ D, ‖v‖ ^ 2 ≤ C * E.form v v)
    (u : DomainL2 Q) (hu : u ∈ E.domain) :
    ∃ p : DomainL2 Q, p ∈ D ∧ ∀ v ∈ D, E.form (u - p) v = 0 := by
  obtain ⟨C, hC, hbound⟩ := hPoin
  let core : InnerProductSpace.Core ℝ D := {
    inner := fun v w => E.form v.val w.val
    conj_inner_symm := fun v w => by
      simpa only [conj_trivial] using E.form_symm w.val (hD.le_domain w.property)
        v.val (hD.le_domain v.property)
    re_inner_nonneg := fun v => E.form_nonneg v.val (hD.le_domain v.property)
    add_left := fun v w x => E.form_add_left v.val (hD.le_domain v.property)
      w.val (hD.le_domain w.property) x.val (hD.le_domain x.property)
    smul_left := fun v w c => by
      simpa only [conj_trivial] using! E.form_smul_left c v.val
        (hD.le_domain v.property) w.val (hD.le_domain w.property)
    definite := fun v hv => by
      apply Subtype.ext
      have hb := hbound v.val v.property
      change E.form v.val v.val = 0 at hv
      rw [hv, mul_zero] at hb
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg v.val]) }
  have hcomplete : ∀ v : ℕ → D,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p, N ≤ p → ∀ q, N ≤ q →
        core.inner (v p - v q) (v p - v q) < ε) →
      ∃ w : D, Tendsto (fun n => core.inner (v n - w) (v n - w)) atTop (𝓝 0) := by
    intro v hv
    obtain ⟨w, hw, hlim⟩ := E.complete (fun n => (v n).val)
      (fun n => hD.le_domain (v n).property) (by
        intro ε hε
        obtain ⟨N, hN⟩ := hv (ε / (1 + C)) (div_pos hε (by positivity))
        refine ⟨N, fun p hp q hq => ?_⟩
        have hn := hN p hp q hq
        change E.form ((v p).val - (v q).val) ((v p).val - (v q).val) < ε / (1 + C) at hn
        have hb := hbound ((v p).val - (v q).val) (D.sub_mem (v p).property (v q).property)
        have ht := (lt_div_iff₀ (show 0 < 1 + C by positivity)).1 hn
        change E.form ((v p).val - (v q).val) ((v p).val - (v q).val) +
          ‖(v p).val - (v q).val‖ ^ 2 < ε
        nlinarith only [hb, ht])
    have hwD : w ∈ D := hD.isClosed _ w (fun n => (v n).property) hw hlim
    refine ⟨⟨w, hwD⟩, ?_⟩
    exact squeeze_zero
      (fun n => E.form_nonneg _ (E.domain.sub_mem (hD.le_domain (v n).property) hw))
      (fun n => E.form_le_energyNormSq) hlim
  let L : D →ₗ[ℝ] ℝ := {
    toFun := fun v => E.form u v.val
    map_add' := fun v w => E.form_add_right hu (hD.le_domain v.property) (hD.le_domain w.property)
    map_smul' := fun c v => E.form_smul_right c hu (hD.le_domain v.property) }
  obtain ⟨p, hp⟩ := aux_lem_replace_riesz_from_complete_core core hcomplete L
    (Real.sqrt (E.form u u)) (fun v => E.abs_form_le hu (hD.le_domain v.property))
  refine ⟨p.val, p.property, ?_⟩
  intro v hv
  have hpv : E.form p.val v = E.form u v := hp ⟨v, hv⟩
  rw [E.form_sub_left hu (hD.le_domain p.property) (hD.le_domain hv), hpv, sub_self]

/-- The represented inverse itself gives the global Poincaré bound needed
for harmonic projection. No fractional or small-cell estimate is used here. -/
theorem aux_lem_replace_limit_form_coercivity {d : ℕ}
    {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ u ∈ E.domain, E.form u u = (limitFormEnergy G u).toReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ E.domain, ‖v‖ ^ 2 ≤ C * E.form v v := by
  refine ⟨‖G‖ + 1, by positivity, ?_⟩
  intro v hv
  have htop : limitFormEnergy G v ≠ ⊤ := by
    have hmem : v ∈ limitFormDomain G := by rw [← hEdom]; exact hv
    exact hmem.ne
  have hbot : limitFormEnergy G v ≠ ⊥ :=
    (limitFormEnergy_nonneg G v).trans_lt' (by
      simp) |>.ne'
  have heq : limitFormEnergy G v = (E.form v v : EReal) := by
    rw [hEenergy v hv, EReal.coe_toReal htop hbot]
  have hbound := norm_sq_le_operatorNorm_mul_quadraticDual G v (E.form v v) heq
  nlinarith [E.form_nonneg v hv]

/-- Harmonic projection for a represented limit form, using only ties already
present in the frozen replacement statement. -/
theorem aux_lem_replace_limit_projection_exists {d : ℕ}
    {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ u ∈ E.domain, E.form u u = (limitFormEnergy G u).toReal)
    {U : Set (SpatialCoordinates d)} {D : Submodule ℝ (DomainL2 Q)}
    (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D)
    (u : DomainL2 Q) (hu : u ∈ E.domain) :
    ∃ p : DomainL2 Q, p ∈ D ∧ ∀ v ∈ D, E.form (u - p) v = 0 := by
  obtain ⟨C, hC, hbound⟩ := aux_lem_replace_limit_form_coercivity G E hEdom hEenergy
  exact aux_lem_replace_projection_exists E hD
    ⟨C, hC, fun v hv => hbound v (hD.le_domain hv)⟩ u hu

/-! ### Assembled machinery for `lem_replace` 

Proved sub-lemmas below (`aux_lem_replace_killed_ae_zero`,
`aux_lem_replace_gamma_killed_compl`, `aux_lem_replace_killed_form_orth`,
`aux_lem_replace_cell_energy_split`, `aux_lem_replace_form_sum`,
`aux_lem_replace_sum_ae_zero`, `aux_lem_replace_projection_assembly`) supply the
killed-domain calculus and projection assembly. The remaining ingredients are the
three `aux_lem_replace_gap_*` lemmas further below. -/

/-- Killed-domain elements vanish a.e. off the cell (energy-norm limits of core
functions supported in `U`; energy-norm convergence dominates `L²` convergence).
Paper  ("harmonic in `q`... exterior agreement"). -/
theorem aux_lem_replace_killed_ae_zero {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    {D : Submodule ℝ (DomainL2 Q)} (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D)
    {v : DomainL2 Q} (hv : v ∈ D) :
    (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)]
      (0 : SpatialCoordinates d → ℝ) := by
  classical
  obtain ⟨w, hw_mem, hw_conv⟩ := hD.exists_seq hv
  have hsub : ((Q : Set (SpatialCoordinates d)) \ U) ⊆ (Q : Set (SpatialCoordinates d)) :=
    sdiff_subset
  have hmono : volume.restrict ((Q : Set (SpatialCoordinates d)) \ U) ≤
      volume.restrict (Q : Set (SpatialCoordinates d)) :=
    Measure.restrict_mono hsub le_rfl
  have hmeas : MeasurableSet ((Q : Set (SpatialCoordinates d)) \ U) :=
    Q.isOpen.measurableSet.diff hU.measurableSet
  have hw_zero : ∀ n, (w n : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)]
      (0 : SpatialCoordinates d → ℝ) := by
    intro n
    obtain ⟨f, hf_cont, hf_cs, hf_supp, hf_ae⟩ := (hw_mem n).2
    have hf0 : ∀ x ∈ ((Q : Set (SpatialCoordinates d)) \ U), f x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx.2 (hf_supp h))
    have h1 : (w n : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)] f :=
      ae_restrict_of_ae_restrict_of_subset hsub hf_ae
    have h2 : f =ᵐ[volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)]
        (0 : SpatialCoordinates d → ℝ) := by
      filter_upwards [ae_restrict_mem hmeas] with x hx
      exact hf0 x hx
    exact h1.trans h2
  have hle : ∀ n, (eLpNorm (v : SpatialCoordinates d → ℝ) 2
      (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal ≤ ‖v - w n‖ := by
    intro n
    have hc : ((v - w n : DomainL2 Q) : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)]
        ((v : SpatialCoordinates d → ℝ) - (w n : SpatialCoordinates d → ℝ)) :=
      ae_restrict_of_ae_restrict_of_subset hsub (Lp.coeFn_sub v (w n))
    have hcw : ((v : SpatialCoordinates d → ℝ) - (w n : SpatialCoordinates d → ℝ)) =ᵐ[
        volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)]
        (v : SpatialCoordinates d → ℝ) := by
      filter_upwards [hw_zero n] with x hx
      rw [Pi.sub_apply, hx, Pi.zero_apply, sub_zero]
    have hv_eq : (v : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)]
        ((v - w n : DomainL2 Q) : SpatialCoordinates d → ℝ) := (hc.trans hcw).symm
    calc (eLpNorm (v : SpatialCoordinates d → ℝ) 2
            (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal
        = (eLpNorm ((v - w n : DomainL2 Q) : SpatialCoordinates d → ℝ) 2
            (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal := by
          rw [eLpNorm_congr_ae hv_eq]
      _ ≤ (eLpNorm ((v - w n : DomainL2 Q) : SpatialCoordinates d → ℝ) 2
            (volume.restrict (Q : Set (SpatialCoordinates d)))).toReal :=
          ENNReal.toReal_mono (Lp.eLpNorm_ne_top (v - w n))
            (eLpNorm_mono_measure _ hmono)
      _ = ‖v - w n‖ := (Lp.norm_def (v - w n)).symm
  have hsqu : ∀ n, ((eLpNorm (v : SpatialCoordinates d → ℝ) 2
      (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal)^2 ≤
      E.energyNormSq (v - w n) := by
    intro n
    have hmem : v - w n ∈ E.domain :=
      E.domain.sub_mem (hD.le_domain hv) ((hw_mem n).mem_domain)
    calc ((eLpNorm (v : SpatialCoordinates d → ℝ) 2
              (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal)^2
        = (eLpNorm (v : SpatialCoordinates d → ℝ) 2
              (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal *
          (eLpNorm (v : SpatialCoordinates d → ℝ) 2
              (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal := by ring
      _ ≤ ‖v - w n‖ * ‖v - w n‖ :=
          mul_le_mul (hle n) (hle n) ENNReal.toReal_nonneg (norm_nonneg _)
      _ = ‖v - w n‖^2 := by ring
      _ ≤ E.energyNormSq (v - w n) := E.sq_norm_le_energyNormSq hmem
  have hsq_zero : ((eLpNorm (v : SpatialCoordinates d → ℝ) 2
      (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal)^2 = 0 :=
    le_antisymm
      (le_of_tendsto_of_tendsto tendsto_const_nhds hw_conv (Filter.Eventually.of_forall hsqu))
      (sq_nonneg _)
  have htoReal : (eLpNorm (v : SpatialCoordinates d → ℝ) 2
      (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U))).toReal = 0 :=
    sq_eq_zero_iff.mp hsq_zero
  have hne_top : eLpNorm (v : SpatialCoordinates d → ℝ) 2
      (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (eLpNorm_mono_measure _ hmono) (Lp.eLpNorm_lt_top v))
  have hzero : eLpNorm (v : SpatialCoordinates d → ℝ) 2
      (volume.restrict ((Q : Set (SpatialCoordinates d)) \ U)) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp htoReal with h | h
    · exact h
    · exact absurd h hne_top
  exact (eLpNorm_eq_zero_iff (by norm_num)).mp hzero

/-- The energy measure of a killed-domain element does not charge the complement
of the cell. Paper. -/
theorem aux_lem_replace_gamma_killed_compl {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    {D : Submodule ℝ (DomainL2 Q)} (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D)
    {v : DomainL2 Q} (hv : v ∈ D) :
    Γ.measure v Uᶜ = 0 := by
  have hB : MeasurableSet Uᶜ := hU.measurableSet.compl
  have hvD : v ∈ E.domain := hD.le_domain hv
  have hcore_zero : ∀ w : DomainL2 Q, E.MemCoreOn U w → Γ.measure w Uᶜ = 0 := by
    intro w hw
    obtain ⟨f, hfcont, -, hfU, hae⟩ := hw.hasCoreRep
    have h1 : Γ.measure w (tsupport f)ᶜ = 0 :=
      Γ.measure_compl_tsupport w hw.mem_domain f hfcont hae
    have hsub : Uᶜ ⊆ (tsupport f)ᶜ := fun x hx hxf => hx (hfU hxf)
    have h2 : Γ.measure w Uᶜ ≤ 0 := by rw [← h1]; exact measure_mono hsub
    exact le_antisymm h2 zero_le
  have hmain : ∀ ε : ℝ, 0 < ε → (Γ.measure v Uᶜ).toReal ≤ ε := by
    intro ε hε
    obtain ⟨w, hwcore, hwlt⟩ := hD.approx v hv ε hε
    have hwD : w ∈ E.domain := hwcore.mem_domain
    have hwz : Γ.measure w Uᶜ = 0 := hcore_zero w hwcore
    have hsubD : v - w ∈ E.domain := E.domain.sub_mem hvD hwD
    have hcrossw : Γ.cross w (v - w) Uᶜ = 0 := by
      have h := Γ.abs_cross_le w hwD (v - w) hsubD Uᶜ hB
      rw [hwz, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hexp := Γ.cross_add_self_apply hwD hsubD Uᶜ
    have hself_add : Γ.cross (w + (v - w)) (w + (v - w)) Uᶜ =
        (Γ.measure (w + (v - w)) Uᶜ).toReal :=
      Γ.cross_self (w + (v - w)) (E.domain.add_mem hwD hsubD) Uᶜ hB
    have hself3 : Γ.cross (v - w) (v - w) Uᶜ = (Γ.measure (v - w) Uᶜ).toReal :=
      Γ.cross_self (v - w) hsubD Uᶜ hB
    have hselfw : Γ.cross w w Uᶜ = (Γ.measure w Uᶜ).toReal :=
      Γ.cross_self w hwD Uᶜ hB
    have hveq : w + (v - w) = v := by abel
    have htoReal : (Γ.measure v Uᶜ).toReal = (Γ.measure (v - w) Uᶜ).toReal := by
      have hv_meas : Γ.measure v Uᶜ = Γ.measure (w + (v - w)) Uᶜ := by rw [hveq]
      rw [hv_meas, ← hself_add, hexp, hselfw, hcrossw, hself3, hwz, ENNReal.toReal_zero]
      ring
    rw [htoReal]
    calc (Γ.measure (v - w) Uᶜ).toReal ≤ E.form (v - w) (v - w) :=
          Γ.toReal_measure_le_form hsubD Uᶜ
      _ ≤ E.energyNormSq (v - w) := E.form_le_energyNormSq
      _ ≤ ε := hwlt.le
  have hfin : Γ.measure v Uᶜ ≠ ⊤ := Γ.measure_ne_top hvD Uᶜ
  have hle : (Γ.measure v Uᶜ).toReal ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa using hmain ε hε
  have hz : (Γ.measure v Uᶜ).toReal = 0 := le_antisymm hle (ENNReal.toReal_nonneg)
  rcases (ENNReal.toReal_eq_zero_iff _).mp hz with h | h
  · exact h
  · exact absurd h hfin

/-- Killed domains on disjoint open sets are `E`-orthogonal.
Paper  ("mutually orthogonal"). -/
theorem aux_lem_replace_killed_form_orth {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    {U V : Set (SpatialCoordinates d)} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    {D₁ D₂ : Submodule ℝ (DomainL2 Q)}
    (h₁ : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D₁) (h₂ : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E V D₂)
    {a b : DomainL2 Q} (ha : a ∈ D₁) (hb : b ∈ D₂) :
    E.form a b = 0 := by
  have hmeas : MeasurableSet U := hU.measurableSet
  have hmeasc : MeasurableSet Uᶜ := hmeas.compl
  have hadom : a ∈ E.domain := h₁.le_domain ha
  have hbdom : b ∈ E.domain := h₂.le_domain hb
  have haUc : (Γ.measure a Uᶜ).toReal = 0 := by
    rw [aux_lem_replace_gamma_killed_compl E Γ hU h₁ ha, ENNReal.toReal_zero]
  have hbVc : (Γ.measure b Vᶜ).toReal = 0 := by
    rw [aux_lem_replace_gamma_killed_compl E Γ hV h₂ hb, ENNReal.toReal_zero]
  have hUVsub : U ⊆ Vᶜ := fun x hx hxv => Set.disjoint_left.mp hUV hx hxv
  have hbU : (Γ.measure b U).toReal = 0 := by
    have hle : Γ.measure b U ≤ Γ.measure b Vᶜ := measure_mono hUVsub
    have hle2 : (Γ.measure b U).toReal ≤ (Γ.measure b Vᶜ).toReal :=
      ENNReal.toReal_mono (Γ.measure_ne_top hbdom Vᶜ) hle
    rw [hbVc] at hle2
    exact le_antisymm hle2 ENNReal.toReal_nonneg
  have hcrossU : Γ.cross a b U = 0 := by
    have hle := Γ.abs_cross_le a hadom b hbdom U hmeas
    rw [hbU, Real.sqrt_zero, mul_zero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hcrossUc : Γ.cross a b Uᶜ = 0 := by
    have hle := Γ.abs_cross_le a hadom b hbdom Uᶜ hmeasc
    rw [haUc, Real.sqrt_zero, zero_mul] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hunion : Γ.cross a b univ = Γ.cross a b U + Γ.cross a b Uᶜ := by
    have h := VectorMeasure.of_union (v := Γ.cross a b)
      (show Disjoint U Uᶜ from disjoint_compl_right) hmeas hmeasc
    rwa [Set.union_compl_self] at h
  rw [← Γ.cross_univ a hadom b hbdom, hunion, hcrossU, hcrossUc]
  ring

/-- Cellwise energy split: if `a` is `E`-orthogonal to `ψ` in the killed domain
of `U`, then `Γ(a + ψ)(U) = Γ(a)(U) + E(ψ)`.
Paper  (`E(u^C) = ∑Λ + Γ(Q∖⋃)`, strong locality). -/
theorem aux_lem_replace_cell_energy_split {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    {D : Submodule ℝ (DomainL2 Q)} (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D)
    {a ψ : DomainL2 Q} (ha : a ∈ E.domain) (hψ : ψ ∈ D) (horth : E.form a ψ = 0) :
    (Γ.measure (a + ψ) U).toReal = (Γ.measure a U).toReal + E.form ψ ψ := by
  classical
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hψdom : ψ ∈ E.domain := hD.le_domain hψ
  have hψcompl : Γ.measure ψ Uᶜ = 0 := aux_lem_replace_gamma_killed_compl E Γ hU hD hψ
  have haψ_compl : Γ.cross a ψ Uᶜ = 0 := by
    have h0 := Γ.abs_cross_le a ha ψ hψdom Uᶜ hUmeas.compl
    rw [hψcompl, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at h0
    exact abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  have hsplit : Γ.cross a ψ U = 0 := by
    have hunion := VectorMeasure.of_union (v := Γ.cross a ψ)
      disjoint_compl_right hUmeas hUmeas.compl
    rw [union_compl_self, Γ.cross_univ a ha ψ hψdom, horth, haψ_compl, add_zero] at hunion
    exact hunion.symm
  have hψU : (Γ.measure ψ U).toReal = E.form ψ ψ := by
    have hUeq : Γ.measure ψ U = Γ.measure ψ univ := by
      have hadd := measure_add_measure_compl (μ := Γ.measure ψ) hUmeas
      rwa [hψcompl, add_zero] at hadd
    rw [hUeq, Γ.measure_univ ψ hψdom]
  rw [← Γ.cross_self (a + ψ) (E.domain.add_mem ha hψdom) U hUmeas,
    Γ.cross_add_self_apply ha hψdom U,
    Γ.cross_self a ha U hUmeas,
    Γ.cross_self ψ hψdom U hUmeas,
    hsplit, hψU]
  ring

/-- Finite-sum linearity of `E` in the first slot, and the Pythagoras identity
for a pairwise `E`-orthogonal finite family in the domain.
The first-slot calculation uses `E.form_add_left`. -/
theorem aux_lem_replace_form_sum {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    {n : ℕ} (p : Fin n → DomainL2 Q) (hp : ∀ i, p i ∈ E.domain)
    (v : DomainL2 Q) (hv : v ∈ E.domain) :
    (∑ i ∈ (Finset.univ : Finset (Fin n)), p i) ∈ E.domain ∧
    E.form (∑ i ∈ (Finset.univ : Finset (Fin n)), p i) v = ∑ i, E.form (p i) v ∧
    ((Pairwise fun i j => E.form (p i) (p j) = 0) →
      E.form (∑ i ∈ (Finset.univ : Finset (Fin n)), p i)
          (∑ i ∈ (Finset.univ : Finset (Fin n)), p i) = ∑ i, E.form (p i) (p i)) := by
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin n)), p i) ∈ E.domain :=
    E.domain.sum_mem fun i _ => hp i
  have hlin : E.form (∑ i ∈ (Finset.univ : Finset (Fin n)), p i) v = ∑ i, E.form (p i) v := by
    classical
    induction' (Finset.univ : Finset (Fin n)) using Finset.induction_on with i s his ih
    · simp [E.form_zero_left hv]
    · have hi : i ∉ s := his
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [E.form_add_left (p i) (hp i) (∑ j ∈ s, p j) (E.domain.sum_mem fun j hj => hp j) v hv, ih]
  have hpyth : ((Pairwise fun i j => E.form (p i) (p j) = 0) →
      E.form (∑ i ∈ (Finset.univ : Finset (Fin n)), p i)
          (∑ i ∈ (Finset.univ : Finset (Fin n)), p i) = ∑ i, E.form (p i) (p i)) := by
    intro hpw
    have hpair : ∀ i j, i ≠ j → E.form (p i) (p j) = 0 := hpw
    classical
    induction' (Finset.univ : Finset (Fin n)) using Finset.induction_on with i s his ih
    · simp [E.form_zero_right E.domain.zero_mem]
    · have hi : i ∉ s := his
      have hs_mem : (∑ j ∈ s, p j) ∈ E.domain := E.domain.sum_mem fun j hj => hp j
      have h_cross1_gen : ∀ t : Finset (Fin n), i ∉ t → E.form (p i) (∑ j ∈ t, p j) = 0 := by
        intro t
        induction t using Finset.induction_on with
        | empty => intro _; simp [E.form_zero_right (hp i)]
        | insert k t' hkt ih_cross =>
          intro hi_kt
          have hik : i ≠ k := fun h => hi_kt (h ▸ Finset.mem_insert_self k t')
          have hit' : i ∉ t' := fun h => hi_kt (Finset.mem_insert_of_mem h)
          have ht_mem : (∑ j ∈ t', p j) ∈ E.domain := E.domain.sum_mem fun j hj => hp j
          rw [Finset.sum_insert hkt, E.form_add_right (hp i) (hp k) ht_mem,
            ih_cross hit', hpair i k hik]
          ring
      have h_cross1 : E.form (p i) (∑ j ∈ s, p j) = 0 := h_cross1_gen s hi
      have h_cross2 : E.form (∑ j ∈ s, p j) (p i) = 0 := by
        rw [E.form_symm (∑ j ∈ s, p j) hs_mem (p i) (hp i), h_cross1]
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have h_expand : E.form (p i + (∑ j ∈ s, p j)) (p i + (∑ j ∈ s, p j)) =
          E.form (p i) (p i) + E.form (∑ j ∈ s, p j) (∑ j ∈ s, p j) := by
        calc
          E.form (p i + (∑ j ∈ s, p j)) (p i + (∑ j ∈ s, p j))
              = E.form (p i) (p i + (∑ j ∈ s, p j)) + E.form (∑ j ∈ s, p j) (p i + (∑ j ∈ s, p j)) :=
            E.form_add_left (p i) (hp i) (∑ j ∈ s, p j) hs_mem (p i + (∑ j ∈ s, p j))
              (E.domain.add_mem (hp i) hs_mem)
          _ = (E.form (p i) (p i) + E.form (p i) (∑ j ∈ s, p j)) +
              (E.form (∑ j ∈ s, p j) (p i) + E.form (∑ j ∈ s, p j) (∑ j ∈ s, p j)) := by
            rw [E.form_add_right (hp i) (hp i) hs_mem, E.form_add_right hs_mem (hp i) hs_mem]
          _ = (E.form (p i) (p i) + 0) + (0 + E.form (∑ j ∈ s, p j) (∑ j ∈ s, p j)) := by
            rw [h_cross1, h_cross2]
          _ = E.form (p i) (p i) + E.form (∑ j ∈ s, p j) (∑ j ∈ s, p j) := by ring
      rw [h_expand]
      rw [ih]
  exact ⟨hsum, hlin, hpyth⟩

/-- A finite sum of `L²(Q)` elements each vanishing a.e. on `S ⊆ Q` vanishes a.e. on `S`. -/
theorem aux_lem_replace_sum_ae_zero {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {S : Set (SpatialCoordinates d)} (hS : S ⊆ (Q : Set (SpatialCoordinates d)))
    {ι : Type*} (s : Finset ι) (p : ι → DomainL2 Q)
    (hp : ∀ j ∈ s, (p j : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict S]
      (0 : SpatialCoordinates d → ℝ)) :
    ((∑ j ∈ s, p j : DomainL2 Q) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict S]
      (0 : SpatialCoordinates d → ℝ) := by
  classical
  have htr : ∀ {P : SpatialCoordinates d → Prop},
      (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))), P x) →
        ∀ᵐ x ∂(volume.restrict S), P x :=
    fun h => ae_restrict_of_ae_restrict_of_subset hS h
  induction s using Finset.induction_on with
  | empty =>
    simpa using! htr (Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have h1 := htr (Lp.coeFn_add (p j) (∑ k ∈ s, p k))
    have h2 := hp j (Finset.mem_insert_self j s)
    have h3 := ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hx1]
    simp only [Pi.add_apply, Pi.zero_apply] at hx2 hx3 ⊢
    rw [hx2, hx3, add_zero]

/-- **Consumer: cellwise projection assembly**.  Given the
per-cell `E`-projections `p i` of `u` onto the killed domains `Vi i`, the
replacement `uC = u - ∑ p i` has every clause of the first family conclusion of
`lem_replace`. -/
theorem aux_lem_replace_projection_assembly {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    {n : ℕ} (q : Fin n → Opens (SpatialCoordinates d))
    (hdisjoint : Pairwise (fun i j =>
      Disjoint (q i : Set (SpatialCoordinates d)) (q j : Set (SpatialCoordinates d))))
    (Vi : Fin n → Submodule ℝ (DomainL2 Q))
    (hVi : ∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E (q i : Set (SpatialCoordinates d)) (Vi i))
    (u : DomainL2 Q) (hu : u ∈ E.domain)
    (p : Fin n → DomainL2 Q) (hp : ∀ i, p i ∈ Vi i)
    (hporth : ∀ i, ∀ v ∈ Vi i, E.form (u - p i) v = 0) :
    let uC : DomainL2 Q := u - ∑ i, p i
    let Vsum : Submodule ℝ (DomainL2 Q) := ⨆ i, Vi i
    let cellUnion : Set (SpatialCoordinates d) :=
      ⋃ i : Fin n, (q i : Set (SpatialCoordinates d))
    let Lambda : Fin n → ℝ := fun i =>
      sInf {t : ℝ | ∃ v : DomainL2 Q, v ∈ Vi i ∧
        t = (Γ.measure (u + v) (q i : Set (SpatialCoordinates d))).toReal}
    uC ∈ E.domain ∧
    u - uC ∈ Vsum ∧
    (∀ v ∈ Vsum, E.form uC v = 0) ∧
    E.form u u = E.form uC uC + E.form (u - uC) (u - uC) ∧
    (∀ i, (Γ.measure uC (q i : Set (SpatialCoordinates d))).toReal = Lambda i) ∧
    ((uC : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict ((Q : Set (SpatialCoordinates d)) \ cellUnion)]
      (u : SpatialCoordinates d → ℝ)) ∧
    (∑ i : Fin n,
      ((Γ.measure u (q i : Set (SpatialCoordinates d))).toReal - Lambda i)) =
        E.form (u - uC) (u - uC) := by
  intro uC Vsum cellUnion Lambda
  have hpD : ∀ i, p i ∈ E.domain := fun i => (hVi i).le_domain (hp i)
  obtain ⟨hsumD, hsumlin, hsumpyth⟩ := aux_lem_replace_form_sum E p hpD u hu
  have hdiff : u - uC = ∑ i, p i := by simp only [uC]; abel
  have huC : uC ∈ E.domain := E.domain.sub_mem hu hsumD
  have hcross : ∀ i j, i ≠ j → ∀ v ∈ Vi j, E.form (p i) v = 0 := by
    intro i j hij v hv
    exact aux_lem_replace_killed_form_orth E Γ (q i).isOpen (q j).isOpen
      (hdisjoint hij) (hVi i) (hVi j) (hp i) hv
  have horthj : ∀ j, ∀ v ∈ Vi j, E.form uC v = 0 := by
    intro j v hv
    have hvD : v ∈ E.domain := (hVi j).le_domain hv
    obtain ⟨-, hlin, -⟩ := aux_lem_replace_form_sum E p hpD v hvD
    have hsplit : E.form uC v = E.form (u - p j) v -
        ∑ i ∈ (Finset.univ.erase j), E.form (p i) v := by
      have h1 : E.form uC v = E.form u v - ∑ i, E.form (p i) v := by
        simp only [uC]
        rw [E.form_sub_left hu hsumD hvD, hlin]
      rw [h1, E.form_sub_left hu (hpD j) hvD,
        ← Finset.add_sum_erase Finset.univ (fun i => E.form (p i) v) (Finset.mem_univ j)]
      ring
    rw [hsplit, hporth j v hv]
    have hz : ∑ i ∈ (Finset.univ.erase j), E.form (p i) v = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      exact hcross i j (Finset.ne_of_mem_erase hi) v hv
    rw [hz]; ring
  have horth : ∀ v ∈ Vsum, E.form uC v = 0 := by
    intro v hv
    have key : v ∈ E.domain ∧ E.form uC v = 0 := by
      refine Submodule.iSup_induction (motive := fun v => v ∈ E.domain ∧ E.form uC v = 0)
        Vi hv ?_ ?_ ?_
      · exact fun j v hv => ⟨(hVi j).le_domain hv, horthj j v hv⟩
      · exact ⟨E.domain.zero_mem, E.form_zero_right huC⟩
      · intro x y hx hy
        refine ⟨E.domain.add_mem hx.1 hy.1, ?_⟩
        rw [E.form_add_right huC hx.1 hy.1, hx.2, hy.2, add_zero]
    exact key.2
  have hVsum : u - uC ∈ Vsum := by
    rw [hdiff]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (hp i)
  have hpyth : E.form u u = E.form uC uC + E.form (u - uC) (u - uC) :=
    lem_replace_harmonic_projection d Q E u Vsum uC hu huC hVsum horth
  have hzero : ∀ j, ∀ S : Set (SpatialCoordinates d),
      S ⊆ (Q : Set (SpatialCoordinates d)) \ (q j : Set (SpatialCoordinates d)) →
      (p j : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict S] (0 : SpatialCoordinates d → ℝ) :=
    fun j S hS => ae_restrict_of_ae_restrict_of_subset hS
      (aux_lem_replace_killed_ae_zero E (q j).isOpen (hVi j) (hp j))
  have hcell : ∀ i, (uC : SpatialCoordinates d → ℝ) =ᵐ[
      (volume.restrict (Q : Set (SpatialCoordinates d))).restrict (q i : Set (SpatialCoordinates d))]
      ((u - p i : DomainL2 Q) : SpatialCoordinates d → ℝ) := by
    intro i
    rw [Measure.restrict_restrict (q i).isOpen.measurableSet]
    have hsub : (q i : Set (SpatialCoordinates d)) ∩ (Q : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)) := Set.inter_subset_right
    have hrest := aux_lem_replace_sum_ae_zero hsub (Finset.univ.erase i) p (by
      intro j hj
      refine hzero j _ fun x hx => ⟨hx.2, fun hxj => ?_⟩
      exact Set.disjoint_left.mp (hdisjoint (Finset.ne_of_mem_erase hj).symm) hx.1 hxj)
    have heq : uC = (u - p i) - ∑ j ∈ Finset.univ.erase i, p j := by
      simp only [uC]
      rw [← Finset.add_sum_erase Finset.univ p (Finset.mem_univ i)]
      abel
    have htr : ∀ {P : SpatialCoordinates d → Prop},
        (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))), P x) →
          ∀ᵐ x ∂(volume.restrict ((q i : Set (SpatialCoordinates d)) ∩
            (Q : Set (SpatialCoordinates d)))), P x :=
      fun h => ae_restrict_of_ae_restrict_of_subset hsub h
    rw [heq]
    filter_upwards [htr (Lp.coeFn_sub (u - p i) (∑ j ∈ Finset.univ.erase i, p j)), hrest]
      with x hx1 hx2
    rw [hx1]
    simp only [Pi.sub_apply, Pi.zero_apply] at hx2 ⊢
    rw [hx2, sub_zero]
  have hLambda : ∀ i, Lambda i = (Γ.measure (u - p i) (q i : Set (SpatialCoordinates d))).toReal := by
    intro i
    have hai : u - p i ∈ E.domain := E.domain.sub_mem hu (hpD i)
    have hleast : IsLeast {t : ℝ | ∃ v : DomainL2 Q, v ∈ Vi i ∧
        t = (Γ.measure (u + v) (q i : Set (SpatialCoordinates d))).toReal}
        (Γ.measure (u - p i) (q i : Set (SpatialCoordinates d))).toReal := by
      refine ⟨⟨-p i, (Vi i).neg_mem (hp i), by rw [← sub_eq_add_neg]⟩, ?_⟩
      rintro t ⟨v, hv, rfl⟩
      have hψ : p i + v ∈ Vi i := (Vi i).add_mem (hp i) hv
      have hsplit := aux_lem_replace_cell_energy_split E Γ (q i).isOpen (hVi i) hai hψ
        (hporth i _ hψ)
      have hre : u - p i + (p i + v) = u + v := by abel
      rw [hre] at hsplit
      rw [hsplit]
      linarith [E.form_nonneg _ ((hVi i).le_domain hψ)]
    exact hleast.csInf_eq
  refine ⟨huC, hVsum, horth, hpyth, ?_, ?_, ?_⟩
  · intro i
    rw [hLambda i, Γ.locality_apply huC (E.domain.sub_mem hu (hpD i)) (q i).isOpen (hcell i)]
  · have hsub : (Q : Set (SpatialCoordinates d)) \ cellUnion ⊆ (Q : Set (SpatialCoordinates d)) :=
      sdiff_subset
    have hrest := aux_lem_replace_sum_ae_zero hsub Finset.univ p (by
      intro j _
      refine hzero j _ fun x hx => ⟨hx.1, fun hxj => hx.2 ?_⟩
      exact Set.mem_iUnion.mpr ⟨j, hxj⟩)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (Lp.coeFn_sub u (∑ j, p j)),
      hrest] with x hx1 hx2
    simp only [uC]
    rw [hx1]
    simp only [Pi.sub_apply, Pi.zero_apply] at hx2 ⊢
    rw [hx2, sub_zero]
  · have hterm : ∀ i, (Γ.measure u (q i : Set (SpatialCoordinates d))).toReal - Lambda i =
        E.form (p i) (p i) := by
      intro i
      have hai : u - p i ∈ E.domain := E.domain.sub_mem hu (hpD i)
      have hsplit := aux_lem_replace_cell_energy_split E Γ (q i).isOpen (hVi i) hai (hp i)
        (hporth i _ (hp i))
      have hre : u - p i + p i = u := by abel
      rw [hre] at hsplit
      rw [hsplit, hLambda i]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, hdiff]
    refine (hsumpyth ?_).symm
    intro i j hij
    exact hcross i j hij (p j) (hp j)

/-! Verified limit-transfer and cell-sum helpers. -/


section
open _root_.SubdiffusiveProcess.EllipticRegularity ProbabilityTheory

/-- A finite extended liminf gives one bounded subsequence. The bound and
subsequence are chosen after the sample, not uniformly in the sample. -/
theorem aux_lem_replace_bounded_subsequence_of_liminf
    (k : ℕ → ℝ) (hk : liminf (fun n => ‖k n‖ₑ) atTop < ⊤) :
    ∃ (B : ℝ) (φ : ℕ → ℕ), 0 < B ∧ StrictMono φ ∧
      ∀ n, |k (φ n)| ≤ B := by
  obtain ⟨b, hb, hbtop⟩ := exists_between hk
  have hfreq : ∃ᶠ n in atTop, ‖k n‖ₑ < b :=
    frequently_lt_of_liminf_lt ⟨⊤, fun _ _ => le_top⟩ hb
  obtain ⟨φ, hφ, hφb⟩ := extraction_of_frequently_atTop hfreq
  refine ⟨b.toReal + 1, φ, by positivity, hφ, ?_⟩
  intro n
  have hle := ENNReal.toReal_mono hbtop.ne (hφb n).le
  have hnorm : |k (φ n)| ≤ b.toReal := by
    simpa only [toReal_enorm, Real.norm_eq_abs] using hle
  exact hnorm.trans (le_add_of_nonneg_right zero_le_one)

/-- Uniform moment bounds imply pathwise boundedness along a sample-dependent
subsequence. Only almost-everywhere measurability of the constants is needed. -/
theorem aux_lem_replace_ae_bounded_subsequence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ℝ≥0∞) (hp : p ≠ 0) (k : ℕ → Ω → ℝ) (C : ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (k n) P)
    (hbound : ∀ n, eLpNorm (k n) p P ≤ ENNReal.ofReal C) :
    ∀ᵐ ω ∂P, ∃ (B : ℝ) (φ : ℕ → ℕ),
      0 < B ∧ StrictMono φ ∧ ∀ n, |k (φ n) ω| ≤ B := by
  let km : ℕ → Ω → ℝ := fun n => (hmeas n).mk (k n)
  have hm : ∀ n, Measurable (km n) := fun n => (hmeas n).measurable_mk
  have heq : ∀ n, k n =ᵐ[P] km n := fun n => (hmeas n).ae_eq_mk
  have hbm : ∀ n, eLpNorm (km n) p P ≤ (Real.toNNReal C : ℝ≥0∞) := by
    intro n
    rw [← eLpNorm_congr_ae (heq n)]
    exact hbound n
  have hlim := ae_bdd_liminf_atTop_of_eLpNorm_bdd hp hbm
  have hall : ∀ᵐ ω ∂P, ∀ n, k n ω = km n ω := ae_all_iff.mpr heq
  filter_upwards [hlim, hall] with ω hω heqω
  have hω' : liminf (fun n => ‖k n ω‖ₑ) atTop < ⊤ := by
    simpa only [heqω] using hω
  exact aux_lem_replace_bounded_subsequence_of_liminf (fun n => k n ω) hω'

/-- Lower semicontinuity transfers a finite quadratic bound without ever
converting an infinite seminorm to a real number. -/
theorem aux_lem_replace_seminorm_bound_of_lsc
    (a : ℕ → ℝ≥0∞) (a₀ : ℝ≥0∞) (b : ℕ → ℝ) (b₀ : ℝ)
    (ha : ∀ n, a n < ⊤)
    (hlsc : a₀ ≤ liminf a atTop)
    (hbound : ∀ n, (a n).toReal ^ 2 ≤ b n)
    (hb : Tendsto b atTop (𝓝 b₀)) :
    a₀ < ⊤ ∧ a₀.toReal ^ 2 ≤ b₀ := by
  have hbnonneg : ∀ n, 0 ≤ b n := fun n => (sq_nonneg _).trans (hbound n)
  have hb₀ : 0 ≤ b₀ := ge_of_tendsto' hb hbnonneg
  have hsqrt : ∀ n, a n ≤ ENNReal.ofReal (Real.sqrt (b n)) := by
    intro n
    have hs : (a n).toReal ≤ Real.sqrt (b n) :=
      (Real.le_sqrt (ENNReal.toReal_nonneg) (hbnonneg n)).mpr (hbound n)
    exact (ENNReal.toReal_le_toReal (ha n).ne ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using hs)
  have hts : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (b n))) atTop
      (𝓝 (ENNReal.ofReal (Real.sqrt b₀))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (Real.continuous_sqrt.tendsto _ |>.comp hb)
  have hle : a₀ ≤ ENNReal.ofReal (Real.sqrt b₀) := by
    exact hlsc.trans ((liminf_le_liminf (Eventually.of_forall hsqrt)).trans_eq hts.liminf_eq)
  have hafin : a₀ < ⊤ := hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hafin, ?_⟩
  have hreal : a₀.toReal ≤ Real.sqrt b₀ := by
    simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  exact (Real.le_sqrt ENNReal.toReal_nonneg hb₀).mp hreal

theorem aux_lem_replace_ae_prod_fst {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ z ∂(μ.prod μ), p z.1 := by
  rw [ae_iff] at h ⊢
  have hset : {z : α × α | ¬ p z.1} = {x : α | ¬ p x} ×ˢ (Set.univ : Set α) := by
    ext z
    simp
  rw [hset, Measure.prod_prod, h, zero_mul]

theorem aux_lem_replace_ae_prod_snd {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ z ∂(μ.prod μ), p z.2 := by
  rw [ae_iff] at h ⊢
  have hset : {z : α × α | ¬ p z.2} = (Set.univ : Set α) ×ˢ {x : α | ¬ p x} := by
    ext z
    simp
  rw [hset, Measure.prod_prod, h, mul_zero]

theorem aux_lem_replace_mul_liminf_le (A : ℝ≥0∞) (v : ℕ → ℝ≥0∞) :
    A * liminf v atTop ≤ liminf (fun n => A * v n) atTop := by
  rw [liminf_eq_iSup_iInf, liminf_eq_iSup_iInf]
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun s => iSup_le fun hs => ?_
  refine le_iSup_of_le s (le_iSup_of_le hs ?_)
  refine le_iInf fun a => le_iInf fun ha => ?_
  exact mul_le_mul' le_rfl (le_trans (iInf_le _ a) (iInf_le _ ha))

theorem aux_lem_replace_le_liminf_div_const {b : ℕ → ℝ≥0∞} {B D : ℝ≥0∞}
    (hb : Tendsto b atTop (𝓝 B)) : B / D ≤ liminf (fun n => b n / D) atTop := by
  have hcongr : liminf (fun n => b n / D) atTop = liminf (fun n => D⁻¹ * b n) atTop :=
    liminf_congr (Filter.Eventually.of_forall fun n => ENNReal.div_eq_inv_mul)
  rw [ENNReal.div_eq_inv_mul, hcongr]
  calc D⁻¹ * B = D⁻¹ * liminf b atTop := by rw [hb.liminf_eq]
    _ ≤ liminf (fun n => D⁻¹ * b n) atTop := aux_lem_replace_mul_liminf_le D⁻¹ b

theorem aux_lem_replace_liminf_rpow_half {u : ℕ → ℝ≥0∞} :
    (liminf u atTop) ^ (1 / 2 : ℝ) ≤ liminf (fun n => (u n) ^ (1 / 2 : ℝ)) atTop := by
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
    intro x
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  rw [le_liminf_iff]
  intro y hy
  have hy2 : y ^ (2 : ℝ) < liminf u atTop := by
    rw [← hsq (liminf u atTop)]
    exact ENNReal.rpow_lt_rpow hy (by norm_num)
  obtain ⟨e, hye, hel⟩ := exists_between hy2
  have hiff : (e ≤ liminf u atTop ↔ ∀ z < e, ∀ᶠ n in atTop, z < u n) := le_liminf_iff
  have hget : ∀ᶠ n in atTop, y ^ (2 : ℝ) < u n :=
    hiff.mp (le_of_lt hel) (y ^ (2 : ℝ)) hye
  filter_upwards [hget] with n hn
  have h := ENNReal.rpow_lt_rpow hn (show (0 : ℝ) < 1 / 2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at h

theorem aux_lem_replace_fatou_double {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {g : ℕ → α → ℝ} {g₀ : α → ℝ} {D : α × α → ℝ≥0∞} {A : ℝ≥0∞}
    (hg : ∀ n, AEMeasurable (g n) μ) (_hg₀ : AEMeasurable g₀ μ)
    (hD : AEMeasurable D (μ.prod μ))
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) :
    A * (∫⁻ p, ENNReal.ofReal ((g₀ p.1 - g₀ p.2) ^ 2) / D p ∂(μ.prod μ)) ≤
      liminf (fun n => A * (∫⁻ p,
        ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p ∂(μ.prod μ))) atTop := by
  have hmeas : ∀ n, AEMeasurable (fun p : α × α =>
      ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p) (μ.prod μ) := by
    intro n
    have h1 : AEMeasurable (g n) μ := hg n
    measurability
  have hpoint : ∀ᵐ p ∂(μ.prod μ),
      ENNReal.ofReal ((g₀ p.1 - g₀ p.2) ^ 2) / D p ≤
        liminf (fun n => ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p) atTop := by
    have h1 : ∀ᵐ p ∂(μ.prod μ), Tendsto (fun n => g n p.1) atTop (𝓝 (g₀ p.1)) :=
      aux_lem_replace_ae_prod_fst hconv
    have h2 : ∀ᵐ p ∂(μ.prod μ), Tendsto (fun n => g n p.2) atTop (𝓝 (g₀ p.2)) :=
      aux_lem_replace_ae_prod_snd hconv
    filter_upwards [h1, h2] with p hp1 hp2
    have hb : Tendsto (fun n => ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((g₀ p.1 - g₀ p.2) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((hp1.sub hp2).pow 2)
    exact aux_lem_replace_le_liminf_div_const hb
  have hF := lintegral_liminf_le' (u := atTop) hmeas
  have hmono := lintegral_mono_ae hpoint
  calc A * (∫⁻ p, ENNReal.ofReal ((g₀ p.1 - g₀ p.2) ^ 2) / D p ∂(μ.prod μ))
      ≤ A * liminf (fun n => ∫⁻ p,
          ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p ∂(μ.prod μ)) atTop :=
        mul_le_mul' le_rfl (le_trans hmono hF)
    _ ≤ liminf (fun n => A * (∫⁻ p,
          ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p ∂(μ.prod μ))) atTop :=
        aux_lem_replace_mul_liminf_le A _

theorem aux_lem_replace_fractional_seminorm_lsc {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (w : ℕ → DomainL2 (centeredCube z r hr)) (u : DomainL2 (centeredCube z r hr))
    (hw : Tendsto w atTop (𝓝 u)) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) ≤
      liminf (fun n => cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w n)) atTop := by
  classical
  let μ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let D : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun p =>
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (p.1 j - p.2 j) ^ 2))) ^
      ((d : ℝ) + 2 * (s : ℝ))
  let G : DomainL2 (centeredCube z r hr) → SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ :=
    fun f p => ENNReal.ofReal ((f p.1 - f p.2) ^ 2) / D p
  have hden : AEMeasurable D (μ.prod μ) := by
    show AEMeasurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (p.1 j - p.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * (s : ℝ))) (μ.prod μ)
    measurability
  have hS : ∀ f : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f) =
        ((ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
          (∫⁻ p, G f p ∂(μ.prod μ))) ^ (1 / 2 : ℝ) := by
    intro f
    rw [cubeFractionalL2Seminorm]
    congr 1
    congr 1
    rw [MeasureTheory.lintegral_prod _ (by
      have hf : AEMeasurable (⇑f) μ := (Lp.aestronglyMeasurable f).aemeasurable
      show AEMeasurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
        ENNReal.ofReal ((⇑f p.1 - ⇑f p.2) ^ 2) / D p) (μ.prod μ)
      measurability)]
    refine lintegral_congr_ae ?_
    filter_upwards with x
    refine lintegral_congr_ae ?_
    filter_upwards with y
    rw [Fin.sum_univ_one]
  have hmain : ∀ c : ℝ≥0∞,
      liminf (fun n => cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w n)) atTop < c →
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) ≤ c := by
    intro c hc
    have hfreq : ∃ᶠ n in atTop,
        cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w n) < c :=
      Filter.frequently_lt_of_liminf_lt ⟨⊤, fun a _ => le_top⟩ hc
    obtain ⟨φ, hφ, hφlt⟩ := Filter.extraction_of_frequently_atTop hfreq
    have hwφ : Tendsto (fun n => w (φ n)) atTop (𝓝 u) := hw.comp hφ.tendsto_atTop
    have hTIM : TendstoInMeasure μ (fun n : ℕ => ⇑(w (φ n))) atTop (⇑u) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
        (f := fun n : ℕ => ⇑(w (φ n))) (g := ⇑u) (l := atTop)
        (by norm_num)
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => w (φ n)) u).mp hwφ)
    obtain ⟨ns, -, hnsae⟩ := hTIM.exists_seq_tendsto_ae
    have hfat := aux_lem_replace_fatou_double μ (g := fun i => ⇑(w (φ (ns i)))) (g₀ := ⇑u)
      (D := D) (A := ENNReal.ofReal (s : ℝ) /
        volume (centeredCube z r hr : Set (SpatialCoordinates d)))
      (fun i => (Lp.aestronglyMeasurable (w (φ (ns i)))).aemeasurable)
      (Lp.aestronglyMeasurable u).aemeasurable hden hnsae
    have hlim_eq : liminf (fun i => cubeFractionalL2Seminorm hd z r hr s
          (fun _ : Fin 1 => w (φ (ns i)))) atTop =
        liminf (fun i => ((ENNReal.ofReal (s : ℝ) /
          volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
          (∫⁻ p, G (w (φ (ns i))) p ∂(μ.prod μ))) ^ (1 / 2 : ℝ)) atTop :=
      liminf_congr (Filter.Eventually.of_forall fun i => hS (w (φ (ns i))))
    have hstep : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) ≤
        liminf (fun i => cubeFractionalL2Seminorm hd z r hr s
          (fun _ : Fin 1 => w (φ (ns i)))) atTop := by
      rw [hS u, hlim_eq]
      exact le_trans (ENNReal.rpow_le_rpow hfat (by norm_num)) aux_lem_replace_liminf_rpow_half
    exact le_trans hstep
      (liminf_le_of_frequently_le (Filter.Frequently.of_forall fun i => le_of_lt (hφlt (ns i)))
        ⟨⊥, by filter_upwards with i; exact bot_le⟩)
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hLc, hcu⟩ := exists_between hcon
  exact absurd (hmain c hLc) (not_le.mpr hcu)

/-- Strong convergence and a convergent upper energy bound preserve the full
normalized fractional square norm, including its finite-domain guard. -/
theorem aux_lem_replace_fractional_sqnorm_transfer {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (w : ℕ → DomainL2 (centeredCube z r hr))
    (u : DomainL2 (centeredCube z r hr)) (hw : Tendsto w atTop (𝓝 u))
    (e : ℕ → ℝ) (e₀ K : ℝ) (he : Tendsto e atTop (𝓝 e₀))
    (hfin : ∀ n, cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w n) < ⊤)
    (hbound : ∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr s (w n) ≤ K * e n) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) < ⊤ ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr s u ≤ K * e₀ := by
  have hb : Tendsto
      (fun n => K * e n - ‖w n‖ ^ 2 /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) atTop
      (𝓝 (K * e₀ - ‖u‖ ^ 2 /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) :=
    (tendsto_const_nhds.mul he).sub ((hw.norm.pow 2).div_const _)
  have hsq : ∀ n,
      (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w n)).toReal ^ 2 ≤
        K * e n - ‖w n‖ ^ 2 /
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro n
    have h := hbound n
    simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm, _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSqNorm,
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSeminormSq, Fin.sum_univ_one] at h
    exact le_sub_iff_add_le.mpr h
  obtain ⟨hufin, hu⟩ := aux_lem_replace_seminorm_bound_of_lsc _ _ _ _ hfin
    (aux_lem_replace_fractional_seminorm_lsc hd z r hr s w u hw) hsq hb
  refine ⟨hufin, ?_⟩
  simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm, _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSqNorm,
    _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSeminormSq, Fin.sum_univ_one]
  exact le_sub_iff_add_le.mp hu

/-- Convert the represented recovery's extended energy convergence to the real
form energy. This uses the actual domain and diagonal-energy identifications. -/
theorem aux_lem_replace_recovery_real_energy {d : ℕ}
    {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ v ∈ E.domain, E.form v v = (limitFormEnergy G v).toReal)
    (u : DomainL2 Q) (hu : u ∈ E.domain)
    (e : ℕ → ℝ)
    (he : Tendsto (fun n => (e n : EReal)) atTop (𝓝 (limitFormEnergy G u))) :
    Tendsto e atTop (𝓝 (E.form u u)) := by
  have hutop : limitFormEnergy G u ≠ ⊤ := by
    have hu' : u ∈ limitFormDomain G := hEdom ▸ hu
    exact hu'.ne
  have hubot : limitFormEnergy G u ≠ ⊥ :=
    (limitFormEnergy_nonneg G u).trans_lt'
      (by simp) |>.ne'
  have h := (EReal.tendsto_toReal hutop hubot).comp he
  simpa only [Function.comp_def, EReal.toReal_coe, ← hEenergy u hu] using h

/-- The root Mosco package transfers finite-level fractional coercivity along
any bounded-constant subsequence. No cell limit or localized recovery is used. -/
theorem aux_lem_replace_root_fractional_coercivity
    (d : ℕ) (hd : 2 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (N : ℕ → ℕ)
    (Gn : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGn : ∀ n f, Gn n f =
      (responseSolution S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hconv : Tendsto Gn atTop (𝓝 G))
    (K : ℕ → ℝ)
    (hK : ∀ n (w : killedSobolevGraph (centeredCube z r hr)),
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => (w : SobolevData _).1) < ⊤ ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (w : SobolevData _).1 ≤
        K n * sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) w w)
    (B : ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ) (hB : ∀ n, K (φ n) ≤ B)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ v ∈ E.domain, E.form v v = (limitFormEnergy G v).toReal) :
    ∀ u ∈ E.domain,
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u) < ⊤ ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder u ≤
        B * E.form u u := by
  have hmosco := aux_in_represented_mosco_free d hd model H om z r hr S G N Gn hGn hconv
  intro u hu
  obtain ⟨w, hw⟩ := hmosco.2.2 u (hEdom ▸ hu)
  have hwval := (continuous_fst.tendsto _).comp hw
  have hwe := (continuous_snd.tendsto _).comp hw
  let e : ℕ → ℝ := fun n =>
    responseForm S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) (w n) (w n)
  have her : Tendsto e atTop (𝓝 (E.form u u)) :=
    aux_lem_replace_recovery_real_energy G E hEdom hEenergy u hu e hwe
  have hK' (n : ℕ) :
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => (w n).val.1) < ⊤ ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (w n).val.1 ≤ K n * e n := by
    let wk : killedSobolevGraph (centeredCube z r hr) :=
      ⟨(w n).val, hS ▸ (w n).property⟩
    exact hK n wk
  refine aux_lem_replace_fractional_sqnorm_transfer hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
    (fun n => (w (φ n)).val.1) u (hwval.comp hφ.tendsto_atTop)
    (fun n => e (φ n)) (E.form u u) B (her.comp hφ.tendsto_atTop)
    (fun n => (hK' (φ n)).1) ?_
  intro n
  exact ((hK' (φ n)).2).trans (mul_le_mul_of_nonneg_right (hB n)
    (sobolevCoefficientForm_nonneg
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N (φ n)) z hr) (w (φ n)).val))



/-- The chart from the unit cube to a cube of side `3^k`. -/
def aux_lem_replace_large_cube_upMap {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun y => z + (3 : ℝ) ^ k • y,
    by
      simpa only [Pi.add_apply] using!
        (continuous_const (y := z)).add (continuous_const_smul ((3 : ℝ) ^ k))⟩

theorem aux_lem_replace_large_cube_upMap_apply {d : ℕ} (k : ℕ)
    (z y : SpatialCoordinates d) :
    aux_lem_replace_large_cube_upMap k z y = z + (3 : ℝ) ^ k • y := rfl

/-- Upward scale shift: read layer `j+k` in the large-cube chart. -/
def aux_lem_replace_large_cube_upShift {d : ℕ} (k : ℕ) (z : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun j => (omega (j + k)).comp (aux_lem_replace_large_cube_upMap k z)

theorem aux_lem_replace_large_cube_upShift_apply {d : ℕ} (k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) (j : ℤ) :
    aux_lem_replace_large_cube_upShift k z omega j y = omega (j + k) (z + (3 : ℝ) ^ k • y) := rfl

theorem aux_lem_replace_large_cube_upShift_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (k : ℕ) (z : SpatialCoordinates d) :
    Measurable (aux_lem_replace_large_cube_upShift (d := d) k z) := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (aux_lem_replace_large_cube_upMap k z) := by fun_prop
  exact Measurable.of_eval fun j => hc.comp (measurable_pi_apply (j + (k : ℤ)))

theorem aux_lem_replace_large_cube_upShift_downShift {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) :
    aux_lem_replace_large_cube_upShift k z
      (aux_lem_as_coarse_shallow_grid_scaleShift k (-((3 : ℝ) ^ (-(k : ℤ))) • z)
        omega) = omega := by
  funext j
  ext y
  simp only [aux_lem_replace_large_cube_upShift, aux_lem_as_coarse_shallow_grid_scaleShift,
    ContinuousMap.comp_apply, add_sub_cancel_right]
  congr 1
  ext i
  simp only [aux_lem_as_coarse_shallow_grid_cellMap, ContinuousMap.coe_mk,
    cubeDilation_apply, aux_lem_replace_large_cube_upMap, Pi.add_apply, Pi.smul_apply,
    Pi.zero_apply, sub_zero, smul_eq_mul, _root_.zpow_neg, zpow_natCast]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0))]
  ring

/-- The upward shift preserves the same field law, by inversion of the downward shift. -/
theorem aux_lem_replace_large_cube_upShift_measurePreserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : SpatialCoordinates d) :
    MeasurePreserving (aux_lem_replace_large_cube_upShift k z)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  let down := aux_lem_as_coarse_shallow_grid_scaleShift k
    (-((3 : ℝ) ^ (-(k : ℤ))) • z)
  have hd : MeasurePreserving down (chaosSampleLaw M).toMeasure
      (chaosSampleLaw M).toMeasure :=
    lem_as_coarse_shallow_grid_scale_shift M k _
  have hcomp : aux_lem_replace_large_cube_upShift k z ∘ down = id := by
    funext omega
    exact aux_lem_replace_large_cube_upShift_downShift k z omega
  refine ⟨aux_lem_replace_large_cube_upShift_measurable k z, ?_⟩
  calc
    Measure.map (aux_lem_replace_large_cube_upShift k z) (chaosSampleLaw M).toMeasure =
        Measure.map (aux_lem_replace_large_cube_upShift k z)
          (Measure.map down (chaosSampleLaw M).toMeasure) := by rw [hd.map_eq]
    _ = Measure.map (aux_lem_replace_large_cube_upShift k z ∘ down) (chaosSampleLaw M).toMeasure :=
      Measure.map_map (aux_lem_replace_large_cube_upShift_measurable k z) hd.measurable
    _ = (chaosSampleLaw M).toMeasure := by rw [hcomp, Measure.map_id]

/-- Transfer an arbitrary event through the upward shift, without a measurability premise. -/
theorem aux_lem_replace_large_cube_upShift_prob_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : SpatialCoordinates d)
    (S : Set (BilateralField d)) :
    (chaosSampleLaw M).toMeasure (aux_lem_replace_large_cube_upShift k z ⁻¹' S) ≤
      (chaosSampleLaw M).toMeasure S := by
  set P := (chaosSampleLaw M).toMeasure
  calc
    P (aux_lem_replace_large_cube_upShift k z ⁻¹' S) ≤
        P (aux_lem_replace_large_cube_upShift k z ⁻¹' toMeasurable P S) :=
      measure_mono (Set.preimage_mono (subset_toMeasurable P S))
    _ = P (toMeasurable P S) :=
      (aux_lem_replace_large_cube_upShift_measurePreserving M k z).measure_preimage
        (measurableSet_toMeasurable P S).nullMeasurableSet
    _ = P S := measure_toMeasurable S

theorem aux_lem_replace_large_cube_upShift_fine_sum {d : ℕ} (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) :
    (∑ j ∈ Finset.range (N + k + 1), aux_lem_replace_large_cube_upShift k z omega (-(j : ℤ)) y) =
      (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_lem_replace_large_cube_upMap k z y)) +
        ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_lem_replace_large_cube_upMap k z y) := by
  simp only [aux_lem_replace_large_cube_upShift, ContinuousMap.comp_apply]
  rw [show N + k + 1 = k + (N + 1) by omega, Finset.sum_range_add]
  congr 1
  · calc
      (∑ j ∈ Finset.range k, omega (-(j : ℤ) + k) (aux_lem_replace_large_cube_upMap k z y)) =
          ∑ j ∈ Finset.range k,
            omega (((k - 1 - j : ℕ) : ℤ) + 1) (aux_lem_replace_large_cube_upMap k z y) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := Finset.mem_range.mp hj
        congr 2
        omega
      _ = _ := Finset.sum_range_reflect
        (fun a => omega ((a : ℤ) + 1) (aux_lem_replace_large_cube_upMap k z y)) k
  · apply Finset.sum_congr rfl
    intro j hj
    congr 2
    push_cast
    ring

/-- Exact coefficient factorization into the old cutoff and the `k` new coarse layers. -/
theorem aux_lem_replace_large_cube_upShift_cutoff_factor {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_lem_replace_large_cube_upShift k z omega) (N + k) y =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k)) *
        Real.exp ((∑ a ∈ Finset.range k,
          omega ((a : ℤ) + 1) (aux_lem_replace_large_cube_upMap k z y)) -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          omega N (aux_lem_replace_large_cube_upMap k z y) := by
  have hsplit := aux_lem_replace_large_cube_upShift_fine_sum N k z y omega
  have hposN : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 :=
    ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  simp only [cutoffCoefficient, cutoffPotential, ContinuousMap.zero_apply, zero_add,
    Int.ofNat_eq_natCast, hsplit, Nat.cast_add]
  rw [show (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_lem_replace_large_cube_upMap k z y)) +
      (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_lem_replace_large_cube_upMap k z y)) -
      ((N : ℝ) + k + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
      ((∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_lem_replace_large_cube_upMap k z y)) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
      ((∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_lem_replace_large_cube_upMap k z y)) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring,
    Real.exp_add]
  field_simp

/-- The annealed ordering controls the change in the cutoff normalizer. -/
theorem aux_lem_replace_large_cube_ahom_ratio_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (N k : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k) ≤
      Real.exp (2 * ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
  by_cases hk : k = 0
  · simp only [hk, Nat.add_zero, Nat.cast_zero, zero_mul, mul_zero, Real.exp_zero]
    rw [div_self (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))]
  · have hNk : N < N + k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk)
    have hord := (Rm.ahom_ordering N (N + k) hNk).2
    apply (div_le_iff₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + k))).2
    have he : 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
        (((N + k : ℕ) : ℝ) - (N : ℝ)) =
        2 * ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      push_cast
      ring
    rw [he] at hord
    exact hord

private theorem aux_lem_replace_large_cube_exp_factor_le {r s b t : ℝ}
    (hr : r ≤ Real.exp (2 * t)) (hs : s ≤ b) :
    r * Real.exp (s - t) ≤ Real.exp (t + b) := by
  calc
    r * Real.exp (s - t) ≤ Real.exp (2 * t) * Real.exp (s - t) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_nonneg _)
    _ = Real.exp (t + s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t + b) := Real.exp_le_exp.mpr (add_le_add le_rfl hs)

/-- A compact restriction norm bounds the extra coarse layers uniformly in the old cutoff. -/
theorem aux_lem_replace_large_cube_upShift_cutoff_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d)
    (K : Compacts (SpatialCoordinates d)) (hy : aux_lem_replace_large_cube_upMap k z y ∈ K) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_lem_replace_large_cube_upShift k z omega) (N + k) y ≤
      Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict
          (K : Set (SpatialCoordinates d))‖) *
        cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          omega N (aux_lem_replace_large_cube_upMap k z y) := by
  have hsum : (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_lem_replace_large_cube_upMap k z y)) ≤
      ∑ a ∈ Finset.range k,
        ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖ := by
    apply Finset.sum_le_sum
    intro a ha
    exact (le_abs_self _).trans (by
      simpa only [ContinuousMap.restrict_apply, Real.norm_eq_abs] using
        ((omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm
          ⟨aux_lem_replace_large_cube_upMap k z y, hy⟩)
  rw [aux_lem_replace_large_cube_upShift_cutoff_factor]
  apply mul_le_mul_of_nonneg_right
    (aux_lem_replace_large_cube_exp_factor_le (aux_lem_replace_large_cube_ahom_ratio_le M Rm N k) hsum)
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)))
    (Real.exp_nonneg _)

/-- For an expanding cube chart, the normalized fractional square norm decreases. -/
theorem aux_lem_replace_large_cube_fractional_le_unit
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hr1 : 1 ≤ r)
    (f : DomainL2 (centeredCube z r hr))
    (g : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hfg : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      g x = f (cubeDilation z 0 r x)) :
    cubeFractionalSqNorm hd z r hr threeQuarterOrder f ≤
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder g := by
  have hsc := lane4_gagliardo_dilation_scaling d 1 hd z 0 r hr one_pos
    threeQuarterOrder (fun _ => f) (fun _ => g) (fun _ => hfg)
  obtain ⟨hsemi, hl2⟩ := hsc
  have hR : r ^ (-(2 * (threeQuarterOrder : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr1 (by
      change -(2 * (3 / 4 : ℝ)) ≤ 0
      norm_num)
  have hreal := congrArg ENNReal.toReal hsemi
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)] at hreal
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [hreal, hl2]
  exact add_le_add (mul_le_of_le_one_left (sq_nonneg _) hR) le_rfl

/-- A pointwise comparison with a coercive unit-cube coefficient transports to every
larger cube. The deterministic prefactor is allowed to depend on the fixed cube. -/
theorem aux_lem_replace_large_cube_coercivity_transport
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hr1 : 1 ≤ r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (K F : ℝ) (hK : 0 ≤ K)
    (hb : ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w : SobolevData _).1) < ⊤ ∧
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
        (w : SobolevData _).1 ≤ K * sobolevCoefficientForm b (w : SobolevData _) w)
    (hcoeff : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      b.val x ≤ F * a.val (cubeDilation z 0 r x)) :
    ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => (v : SobolevData _).1) < ⊤ ∧
      cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData _).1 ≤
        (K * F * (r ^ ((d : ℝ) - 2))⁻¹) *
          sobolevCoefficientForm a (v : SobolevData _) v := by
  obtain ⟨c, hc⟩ := lane4_dilation_coefficient_transport d z 0 r hr one_pos a
  intro v
  obtain ⟨w, hwval, hwgrad⟩ :=
    aux_lane4_coercivity_dilation_killed_pullback d z r hr one_pos v
  have hscale := (lane4_gagliardo_dilation_scaling d 1 hd z 0 r hr one_pos
    threeQuarterOrder (fun _ => (v : SobolevData _).1)
      (fun _ => (w : SobolevData _).1) (fun _ => hwval)).1
  have hfin : cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
      (fun _ : Fin 1 => (v : SobolevData _).1) < ⊤ := by
    by_contra h
    have hvtop := top_unique (not_lt.mp h)
    rw [hvtop] at hscale
    have hright : ENNReal.ofReal (r ^ (-(2 * (threeQuarterOrder : ℝ)))) *
        (cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
          (fun _ : Fin 1 => (w : SobolevData _).1)) ^ (2 : ℕ) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top (hb w).1)
    simp only [ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hscale
    exact hright.ne hscale.symm
  refine ⟨hfin, ?_⟩
  have hnorm := aux_lem_replace_large_cube_fractional_le_unit hd z r hr hr1
    (v : SobolevData _).1 (w : SobolevData _).1 hwval
  have henergy := aux_lane4_coercivity_dilation_energy_scaling d z r hr one_pos a c
    (v : SobolevData _) (w : SobolevData _) hc hwval hwgrad
  have hcmp : sobolevCoefficientForm b (w : SobolevData _) w ≤
      F * sobolevCoefficientForm c (w : SobolevData _) w := by
    apply weightedGradientForm_le_mul
    filter_upwards [hcoeff, hc] with x hx hcx
    rw [hcx]
    exact hx
  have hpow : r ^ ((d : ℝ) - 2) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  calc
    cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData _).1
        ≤ cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
          (w : SobolevData _).1 := hnorm
    _ ≤ K * sobolevCoefficientForm b (w : SobolevData _) w := (hb w).2
    _ ≤ K * (F * sobolevCoefficientForm c (w : SobolevData _) w) :=
      mul_le_mul_of_nonneg_left hcmp hK
    _ = (K * F * (r ^ ((d : ℝ) - 2))⁻¹) * sobolevCoefficientForm a (v : SobolevData _) v := by
      rw [henergy]
      field_simp

theorem aux_lem_replace_large_cube_upMap_eq {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    (aux_lem_replace_large_cube_upMap k z : SpatialCoordinates d → SpatialCoordinates d) =
      cubeDilation z 0 ((3 : ℝ) ^ k) := by
  funext y i
  simp only [aux_lem_replace_large_cube_upMap, ContinuousMap.coe_mk, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, cubeDilation_apply, Pi.zero_apply, sub_zero]

theorem aux_lem_replace_large_cube_cutoff_positive_coe
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (fun x => (cutoffPositiveCoefficient M H omega N z hr).val x) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      cutoffCoefficient M H omega N := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hval := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr) (cutoffCoefficientCM M H omega N z hr)
    (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [hval, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxQ
  simpa only [cutoffPositiveCoefficient, cutoffCoefficientCM, ContinuousMap.coe_mk,
    div_one] using hx hxQ

theorem aux_lem_replace_large_cube_cutoff_infrared_mul
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H omega N x = Real.exp (H omega x) *
      cutoffCoefficient M (fun _ => 0) omega N x := by
  simp only [cutoffCoefficient, cutoffPotential, ContinuousMap.zero_apply, zero_add,
    Int.ofNat_eq_natCast]
  rw [show H omega x + (∑ j ∈ Finset.range (N + 1), omega (-↑j) x) -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
    H omega x + ((∑ j ∈ Finset.range (N + 1), omega (-↑j) x) -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring, Real.exp_add]
  ring

/-- The finite factor used to compare a large cube with its scale-shifted unit cube. -/
def aux_lem_replace_large_cube_environment_factor
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (omega : BilateralField d) : ℝ :=
  Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
    (∑ a ∈ Finset.range k,
      ‖(omega ((a : ℤ) + 1)).restrict
        (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖) +
    ‖(H (aux_lem_replace_large_cube_upShift k z omega)).restrict
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖ +
    ‖(H omega).restrict
      (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖)

theorem aux_lem_replace_large_cube_environment_factor_pos
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (omega : BilateralField d) :
    0 < aux_lem_replace_large_cube_environment_factor M H k z hr omega := Real.exp_pos _

theorem aux_lem_replace_large_cube_coefficients_le
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (infrared : Bool) (N : ℕ) (omega : BilateralField d) :
    ∀ᵐ y ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H (aux_lem_replace_large_cube_upShift k z omega) (N + k) 0 one_pos).val y ≤
        aux_lem_replace_large_cube_environment_factor M H k z hr omega *
          (cutoffPositiveCoefficient M (if infrared then H else 0) omega N z hr).val
            (cubeDilation z 0 ((3 : ℝ) ^ k) y) := by
  have hq := lane4_dilation_quasi_measure_preserving d z 0 ((3 : ℝ) ^ k) hr one_pos
  filter_upwards [aux_lem_replace_large_cube_cutoff_positive_coe M H
      (aux_lem_replace_large_cube_upShift k z omega) (N + k) 0 one_pos,
    hq.ae (aux_lem_replace_large_cube_cutoff_positive_coe M (if infrared then H else 0) omega N z hr),
    ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet]
    with y hyunit hybig hy
  rw [hyunit, hybig]
  have hyeq := congrFun (aux_lem_replace_large_cube_upMap_eq k z) y
  rw [← hyeq]
  have hyK := centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos hy
  have hxK : aux_lem_replace_large_cube_upMap k z y ∈
      (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)) := by
    rw [hyeq]
    exact centeredCube_subset_closedCube z hr (cubeDilation_mapsTo z 0 hr one_pos y hy)
  have hcoarse := aux_lem_replace_large_cube_upShift_cutoff_le M Rm N k z y omega
    (closedCube z ((3 : ℝ) ^ k) hr) hxK
  have hu : H (aux_lem_replace_large_cube_upShift k z omega) y ≤
      ‖(H (aux_lem_replace_large_cube_upShift k z omega)).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖ := by
    exact (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm
      ((H (aux_lem_replace_large_cube_upShift k z omega)).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ⟨y, hyK⟩)
  have hb : -((if infrared then H else 0) omega (aux_lem_replace_large_cube_upMap k z y)) ≤
      ‖(H omega).restrict
        (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖ := by
    cases infrared
    · simpa only [Bool.false_eq_true, ↓reduceIte, Pi.zero_apply,
        ContinuousMap.zero_apply, neg_zero] using
        norm_nonneg ((H omega).restrict
          (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)))
    · exact (neg_le_abs _).trans (ContinuousMap.norm_coe_le_norm
        ((H omega).restrict (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)))
          ⟨aux_lem_replace_large_cube_upMap k z y, hxK⟩)
  have hremove : cutoffCoefficient M (fun _ => 0) omega N (aux_lem_replace_large_cube_upMap k z y) =
      Real.exp (-((if infrared then H else 0) omega (aux_lem_replace_large_cube_upMap k z y))) *
        cutoffCoefficient M (if infrared then H else 0) omega N (aux_lem_replace_large_cube_upMap k z y) := by
    rw [aux_lem_replace_large_cube_cutoff_infrared_mul M (if infrared then H else 0), ← mul_assoc,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [aux_lem_replace_large_cube_cutoff_infrared_mul M H]
  refine (mul_le_mul_of_nonneg_left hcoarse (Real.exp_pos _).le).trans ?_
  rw [hremove]
  have hpos : 0 ≤ cutoffCoefficient M (if infrared then H else 0) omega N
      (aux_lem_replace_large_cube_upMap k z y) :=
    (mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)).le
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ hpos
  apply Real.exp_le_exp.2
  linarith only [hu, hb]



theorem aux_lem_replace_raw_integral_restrict
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B : Set α) (hAB : A ⊆ B) (u v : α → ℝ) (W : α → α → ℝ≥0∞)
    (huv : u =ᵐ[μ.restrict A] v) :
    (∫⁻ x in A, ∫⁻ y in A, ENNReal.ofReal ((u x - u y) ^ 2) / W x y ∂μ ∂μ) ≤
      ∫⁻ x in B, ∫⁻ y in B, ENNReal.ofReal ((v x - v y) ^ 2) / W x y ∂μ ∂μ := by
  calc
    (∫⁻ x in A, ∫⁻ y in A, ENNReal.ofReal ((u x - u y) ^ 2) / W x y ∂μ ∂μ) =
        ∫⁻ x in A, ∫⁻ y in A, ENNReal.ofReal ((v x - v y) ^ 2) / W x y ∂μ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [huv] with x hx
      apply lintegral_congr_ae
      filter_upwards [huv] with y hy
      rw [hx, hy]
    _ ≤ ∫⁻ x in A, ∫⁻ y in B, ENNReal.ofReal ((v x - v y) ^ 2) / W x y ∂μ ∂μ :=
      lintegral_mono fun x => lintegral_mono_set hAB
    _ ≤ _ := lintegral_mono_set hAB

theorem aux_lem_replace_scalar_seminorm_sq {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (u : DomainL2 (centeredCube z r hr)) :
    (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u)) ^ (2 : ℕ) =
      (ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((u x - u y) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * (s : ℝ)) := by
  rw [← ENNReal.rpow_natCast, cubeFractionalL2Seminorm, ← ENNReal.rpow_mul]
  norm_num only [Nat.cast_ofNat, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    ENNReal.rpow_one, Fin.sum_univ_one]

theorem aux_lem_replace_normalization_ratio (s a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ENNReal.ofReal (b / a) * (ENNReal.ofReal s / ENNReal.ofReal b) =
      ENNReal.ofReal s / ENNReal.ofReal a := by
  rw [← ENNReal.ofReal_div_of_pos hb,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ b / a),
    ← ENNReal.ofReal_div_of_pos ha]
  congr 1
  field_simp [ha.ne', hb.ne']

theorem aux_lem_replace_fractional_sq_restrict {d : ℕ} (hd : 2 ≤ d)
    (z Z : SpatialCoordinates d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hle : centeredCube z r hr ≤ centeredCube Z R hR)
    (s : Set.Ioo (0 : ℝ) 1) (u : DomainL2 (centeredCube z r hr))
    (v : DomainL2 (centeredCube Z R hR))
    (huv : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      u x = v x) :
    (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u)) ^ (2 : ℕ) ≤
      ENNReal.ofReal (R ^ d / r ^ d) *
        (cubeFractionalL2Seminorm hd Z R hR s (fun _ : Fin 1 => v)) ^ (2 : ℕ) := by
  let W : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
      ((d : ℝ) + 2 * (s : ℝ))
  have hraw := aux_lem_replace_raw_integral_restrict volume
    (centeredCube z r hr : Set (SpatialCoordinates d))
    (centeredCube Z R hR : Set (SpatialCoordinates d)) hle u v W huv
  rw [aux_lem_replace_scalar_seminorm_sq, aux_lem_replace_scalar_seminorm_sq,
    ← mul_assoc, centeredCube_volume, centeredCube_volume,
    aux_lem_replace_normalization_ratio (s : ℝ) (r ^ d) (R ^ d)
      (pow_pos hr _) (pow_pos hR _)]
  exact mul_le_mul_right hraw _


theorem aux_lem_replace_fractional_zero_extension {d : ℕ} (hd : 2 ≤ d)
    (z Z : SpatialCoordinates d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hle : centeredCube z r hr ≤ centeredCube Z R hR)
    (s : Set.Ioo (0 : ℝ) 1) (u : DomainL2 (centeredCube z r hr))
    (hfin : cubeFractionalL2Seminorm hd Z R hR s
      (fun _ : Fin 1 => zeroExtensionLp hle u) < ⊤) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) < ⊤ ∧
      cubeFractionalSqNorm hd z r hr s u ≤
        (R ^ d / r ^ d) * cubeFractionalSqNorm hd Z R hR s (zeroExtensionLp hle u) := by
  have huv : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      u x = zeroExtensionLp hle u x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hle (zeroExtensionLp_coeFn hle u),
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxQ
    rw [hx, Set.indicator_of_mem hxQ]
  have hsq := aux_lem_replace_fractional_sq_restrict hd z Z r R hr hR hle s u
    (zeroExtensionLp hle u) huv
  have htop : ENNReal.ofReal (R ^ d / r ^ d) *
      (cubeFractionalL2Seminorm hd Z R hR s (fun _ : Fin 1 => zeroExtensionLp hle u)) ^
        (2 : ℕ) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hfin)
  have hufin : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) < ⊤ := by
    by_contra h
    have hutop := top_unique (not_lt.mp h)
    rw [hutop, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
    exact (not_le_of_gt htop) hsq
  refine ⟨hufin, ?_⟩
  have hreal := ENNReal.toReal_mono htop.ne hsq
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ R ^ d / r ^ d)] at hreal
  simp only [cubeFractionalSqNorm, cubeFractionalVecSqNorm, cubeFractionalVecSeminormSq,
    Fin.sum_univ_one, lane2_norm_zeroExtensionLp, centeredCube_volume_real, mul_add]
  have hl2 : ‖u‖ ^ 2 / r ^ d = (R ^ d / r ^ d) * (‖u‖ ^ 2 / R ^ d) := by
    field_simp
  exact add_le_add hreal hl2.le

theorem aux_lem_replace_zero_extension_restrict
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U)
    (v : SobolevData V) :
    sobolevDataRestrict hV (zeroExtensionSobolevData hV v) = v := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [domainLpRestrict_coeFn hV (zeroExtensionLp hV v.1),
      ae_restrict_of_ae_restrict_of_subset hV (zeroExtensionLp_coeFn hV v.1),
      ae_restrict_mem V.isOpen.measurableSet] with x h1 h2 hx
    change (domainLpRestrict hV (zeroExtensionLp hV v.1) :
      SpatialCoordinates d → ℝ) x = v.1 x
    rw [h1, h2, Set.indicator_of_mem hx]
  · funext i
    apply Lp.ext
    filter_upwards [domainLpRestrict_coeFn hV (zeroExtensionLp hV (v.2 i)),
      ae_restrict_of_ae_restrict_of_subset hV
        (zeroExtensionLp_coeFn hV (v.2 i)),
      ae_restrict_mem V.isOpen.measurableSet] with x h1 h2 hx
    change (domainLpRestrict hV (zeroExtensionLp hV (v.2 i)) :
      SpatialCoordinates d → ℝ) x = (v.2 i) x
    rw [h1, h2, Set.indicator_of_mem hx]

/-- Restriction of finite-level coercivity uses the native killed zero
extension, which preserves its energy exactly. -/
theorem aux_lem_replace_killed_coercivity_restrict
    {d : ℕ} (hd : 2 ≤ d) (z Z : SpatialCoordinates d) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (hle : centeredCube z r hr ≤ centeredCube Z R hR)
    (s : Set.Ioo (0 : ℝ) 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube Z R hR))
    (hab : (b.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] a.val)
    (C : ℝ)
    (hbig : ∀ w : killedSobolevGraph (centeredCube Z R hR),
      cubeFractionalL2Seminorm hd Z R hR s (fun _ : Fin 1 => (w : SobolevData _).1) < ⊤ ∧
      cubeFractionalSqNorm hd Z R hR s (w : SobolevData _).1 ≤
        C * sobolevCoefficientForm b w w) :
    ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => (v : SobolevData _).1) < ⊤ ∧
      cubeFractionalSqNorm hd z r hr s (v : SobolevData _).1 ≤
        (R ^ d / r ^ d * C) * sobolevCoefficientForm a v v := by
  intro v
  let vQ : killedSobolevGraph (centeredCube Z R hR) :=
    ⟨zeroExtensionSobolevData hle v.val,
      lane2_zeroExtensionSobolevData_mem_killed hle v.property⟩
  obtain ⟨hQfin, hQbound⟩ := hbig vQ
  obtain ⟨hrfin, hrbound⟩ := aux_lem_replace_fractional_zero_extension hd z Z r R hr hR
    hle s v.val.1 hQfin
  have henergy : sobolevCoefficientForm b vQ.val vQ.val =
      sobolevCoefficientForm a v.val v.val := by
    exact (sobolevCoefficientForm_zeroExtension hle b a hab v.val
      (zeroExtensionSobolevData hle v.val)).trans
      (congrArg (sobolevCoefficientForm a v.val)
        (aux_lem_replace_zero_extension_restrict hle v.val))
  refine ⟨hrfin, ?_⟩
  calc
    cubeFractionalSqNorm hd z r hr s v.val.1 ≤
        (R ^ d / r ^ d) * cubeFractionalSqNorm hd Z R hR s vQ.val.1 := hrbound
    _ ≤ (R ^ d / r ^ d) * (C * sobolevCoefficientForm b vQ.val vQ.val) :=
      mul_le_mul_of_nonneg_left hQbound (by positivity)
    _ = _ := by rw [henergy]; ring

/-- Finite-level coercivity on an arbitrary root: extend by zero to a containing
triadic cube, pull back to the unit cube, and use the finite coefficient factor. -/
theorem aux_lem_replace_arbitrary_root_coercivity
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (k : ℕ) (hrk : r ≤ (3 : ℝ) ^ k) (N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w : SobolevData _).1) < ⊤ ∧
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
        (w : SobolevData _).1 ≤ K * sobolevCoefficientForm
          (cutoffPositiveCoefficient M H
            (aux_lem_replace_large_cube_upShift k z om) (N + k) 0 one_pos) w w) :
    ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => (v : SobolevData _).1) < ⊤ ∧
      cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData _).1 ≤
        (((3 : ℝ) ^ k) ^ d / r ^ d *
          (aux_lem_replace_large_cube_environment_factor M H k z (pow_pos (by norm_num) k) om *
            (((3 : ℝ) ^ k) ^ ((d : ℝ) - 2))⁻¹) * K) *
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr) v v := by
  let R : ℝ := (3 : ℝ) ^ k
  have hR : 0 < R := pow_pos (by norm_num) k
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hle : centeredCube z r hr ≤ centeredCube z R hR := by
    change Metric.ball z (r / 2) ⊆ Metric.ball z (R / 2)
    exact Metric.ball_subset_ball (by dsimp only [R]; linarith)
  let a : PositiveCoefficient (centeredCube z R hR) :=
    cutoffPositiveCoefficient M H om N z hR
  let b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
    cutoffPositiveCoefficient M H
    (aux_lem_replace_large_cube_upShift k z om) (N + k) 0 one_pos
  let F : ℝ := aux_lem_replace_large_cube_environment_factor M H k z hR om
  have hcoeff : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      b.val x ≤ F * a.val (cubeDilation z 0 R x) := by
    simpa using
      aux_lem_replace_large_cube_coefficients_le M Rm H k z hR true N om
  have hlarge := aux_lem_replace_large_cube_coercivity_transport hd z R hR hR1
    a b K F hK hb hcoeff
  have hcoeff_same : (a.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (cutoffPositiveCoefficient M H om N z hr).val := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hle
        (aux_lem_replace_large_cube_cutoff_positive_coe M H om N z hR),
      aux_lem_replace_large_cube_cutoff_positive_coe M H om N z hr]
      with x hx hy
    exact hx.trans hy.symm
  have hsmall := aux_lem_replace_killed_coercivity_restrict hd z z r R hr hR hle
    threeQuarterOrder (cutoffPositiveCoefficient M H om N z hr) a hcoeff_same
    (K * F * (R ^ ((d : ℝ) - 2))⁻¹) hlarge
  intro v
  obtain ⟨hvfin, hvbound⟩ := hsmall v
  refine ⟨hvfin, ?_⟩
  calc
    cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData _).1 ≤
        (R ^ d / r ^ d * (K * F * (R ^ ((d : ℝ) - 2))⁻¹)) *
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr) v v := hvbound
    _ = _ := by ring

/-- Root fractional coercivity on arbitrary positive cubes. The threshold is
chosen for the canonical Borel structure and transported across its unique presentations. -/
theorem aux_lem_replace_ae_root_fractional_coercivity
    (d : ℕ) (hd : 2 ≤ d)
    (I : in_J d) (Pin : in_poincare d hd I)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : in_responses d model)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE : ℕ → ℕ),
        in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE →
      ∀ root, ∀ᵐ ω ∂P,
        ∃ B : ℝ, 0 < B ∧
          ∀ (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
            (volume.restrict (centeredCube (z root) (r root) (hr root) :
              Set (SpatialCoordinates d))))
            (_hEdom : E.domain = limitFormDomain (GE root ω))
            (_hEenergy : ∀ u ∈ E.domain,
              E.form u u = (limitFormEnergy (GE root ω) u).toReal),
            ∀ u ∈ E.domain,
              cubeFractionalL2Seminorm hd (z root) (r root) (hr root)
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (fun _ : Fin 1 => u) < ⊤ ∧
              _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd (z root) (r root) (hr root)
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder u ≤ B * E.form u u := by
  let : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  let : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨delta, hdelta, hcoer⟩ := aux_lem_coercivity_compat d hd I Pin Sob
  refine ⟨delta 1, hdelta 1 le_rfl, ?_⟩
  intro m bm
  have hm : m = borel C(SpatialCoordinates d, ℝ) := bm.measurable_eq
  subst m
  intro model hmodel Rm H Ω _ P field z r hr Sspace GN GE NE hjoint root
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 3)).eventually (eventually_gt_atTop (r root))).exists
  have hkpos : 0 < (3 : ℝ) ^ k := pow_pos (by norm_num) k
  obtain ⟨K, hKcoer, hKm⟩ :=
    hcoer model Rm H hjoint.2.2.2.1 (0 : SpatialCoordinates d) 1 one_pos le_rfl
  obtain ⟨C, hmem, hbound⟩ := hKm 1 le_rfl hmodel
  have hKae := aux_lem_replace_ae_bounded_subsequence (chaosSampleLaw model).toMeasure
    (ENNReal.ofReal 1) (by norm_num) (fun n => K (NE n + k)) C
    (fun n => (hmem (NE n + k)).aestronglyMeasurable) (fun n => hbound (NE n + k))
  have hshift := (aux_lem_replace_large_cube_upShift_measurePreserving model k (z root)).quasiMeasurePreserving.ae hKae
  have hKmap : ∀ᵐ om ∂P.map field,
      ∃ (B : ℝ) (φ : ℕ → ℕ), 0 < B ∧ StrictMono φ ∧
        ∀ n, |K (NE (φ n) + k) (aux_lem_replace_large_cube_upShift k (z root) om)| ≤ B := by
    rw [hjoint.2.2.1]
    exact hshift
  have hKP := ae_of_ae_map hjoint.2.1.aemeasurable hKmap
  filter_upwards [hKP, hjoint.2.2.2.2.2.2.2] with ω hKω hconv
  obtain ⟨B, φ, hB, hφ, hKB⟩ := hKω
  let shift := aux_lem_replace_large_cube_upShift k (z root) (field ω)
  let T : ℝ := (((3 : ℝ) ^ k) ^ d / (r root) ^ d) *
    (aux_lem_replace_large_cube_environment_factor model H k (z root) hkpos (field ω) *
      (((3 : ℝ) ^ k) ^ ((d : ℝ) - 2))⁻¹)
  have hT : 0 < T := mul_pos (div_pos (pow_pos hkpos _) (pow_pos (hr root) _))
    (mul_pos (aux_lem_replace_large_cube_environment_factor_pos model H k (z root) hkpos (field ω))
      (inv_pos.mpr (Real.rpow_pos_of_pos hkpos _)))
  refine ⟨T * B, mul_pos hT hB, ?_⟩
  intro E hEdom hEenergy
  apply aux_lem_replace_root_fractional_coercivity d hd model H (field ω)
    (z root) (r root) (hr root) (Sspace root) (hjoint.2.2.2.2.2.1 root)
    (GE root ω) NE (fun n => GN root (NE n) ω)
    (fun n f => hjoint.2.2.2.2.2.2.1 root (NE n) ω f) (hconv root).1
    (fun n => T * |K (NE n + k) shift|) ?_ (T * B) φ hφ ?_ E hEdom hEenergy
  · intro n
    apply aux_lem_replace_arbitrary_root_coercivity hd model Rm H (field ω)
      (z root) (r root) (hr root) k hk.le (NE n) |K (NE n + k) shift| (abs_nonneg _)
    intro w
    obtain ⟨hfin, hnorm⟩ := (hKcoer (NE n + k) shift).1 w
    refine ⟨hfin, hnorm.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (sobolevCoefficientForm_nonneg _ _)
  · intro n
    exact mul_le_mul_of_nonneg_left (hKB n) hT.le


end

/-- A set on which the function vanishes provides a lower bound for its
Gagliardo integral. No finite-real shadow of an infinite integral is used. -/
theorem aux_lem_replace_support_kernel_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u : α → ℝ) (A B : Set α) (hB : MeasurableSet B)
    (hsupport : ∀ᵐ x ∂μ, x ∉ A → u x = 0)
    (hzero : ∀ᵐ y ∂μ.restrict B, u y = 0)
    (W : α → α → ℝ≥0∞) (D : ℝ≥0∞)
    (hW : ∀ x ∈ A, ∀ y ∈ B, W x y ≤ D) :
    ((∫⁻ x, ENNReal.ofReal ((u x) ^ 2) ∂μ) / D) * μ B ≤
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2) / W x y ∂μ ∂μ := by
  calc
    ((∫⁻ x, ENNReal.ofReal ((u x) ^ 2) ∂μ) / D) * μ B =
        (∫⁻ x, ENNReal.ofReal ((u x) ^ 2) ∂μ) * (D⁻¹ * μ B) := by
      rw [div_eq_mul_inv, mul_assoc]
    _ ≤ ∫⁻ x, ENNReal.ofReal ((u x) ^ 2) * (D⁻¹ * μ B) ∂μ :=
      lintegral_mul_const_le _ _
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2) / W x y ∂μ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hsupport] with x hx
      by_cases hxA : x ∈ A
      · calc
          ENNReal.ofReal ((u x) ^ 2) * (D⁻¹ * μ B) =
              ∫⁻ y in B, ENNReal.ofReal ((u x) ^ 2) / D ∂μ := by
            rw [setLIntegral_const, div_eq_mul_inv, mul_assoc]
          _ ≤ ∫⁻ y in B, ENNReal.ofReal ((u x - u y) ^ 2) / W x y ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [hzero, ae_restrict_mem hB] with y hy hyB
            rw [hy, sub_zero]
            exact ENNReal.div_le_div_left (hW x hxA y hyB) _
          _ ≤ ∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2) / W x y ∂μ :=
            lintegral_mono' Measure.restrict_le_self le_rfl
      · simp only [hx hxA, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
          zero_mul, zero_le]

/-- Cube containment controls both endpoints in every coordinate, including
the boundary-touching case. -/
theorem aux_lem_replace_cube_endpoints {d : ℕ}
    (z zc : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hinside : (centeredCube zc r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d))) (j : Fin d) :
    z j - R / 2 ≤ zc j - r / 2 ∧ zc j + r / 2 ≤ z j + R / 2 := by
  apply (Set.Ioo_subset_Ioo_iff (by linarith : zc j - r / 2 < zc j + r / 2)).mp
  intro t ht
  have hx : Function.update zc j t ∈ (centeredCube zc r hr : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi]
    intro i _
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using ht
    · simp only [Function.update_of_ne hij]
      constructor <;> linarith
  have hy := hinside hx
  rw [centeredCube_eq_pi] at hy
  simpa only [Function.update_self] using hy j (Set.mem_univ j)

/-- A cell of side at most one third of the root side has a disjoint neighbour
of the same side inside the root. The construction allows touching boundaries. -/
theorem aux_lem_replace_cell_neighbour {d : ℕ} (hd : 1 ≤ d)
    (z zc : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hsmall : 3 * r ≤ R)
    (hinside : (centeredCube zc r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ zb : SpatialCoordinates d,
      (centeredCube zb r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      Disjoint (centeredCube zc r hr : Set (SpatialCoordinates d))
        (centeredCube zb r hr : Set (SpatialCoordinates d)) ∧
      ∀ x ∈ (centeredCube zc r hr : Set (SpatialCoordinates d)),
        ∀ y ∈ (centeredCube zb r hr : Set (SpatialCoordinates d)),
          Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ 2 * (d : ℝ) * r := by
  classical
  let j₀ : Fin d := ⟨0, hd⟩
  let zb : SpatialCoordinates d := Function.update zc j₀
    (if zc j₀ ≤ z j₀ then zc j₀ + r else zc j₀ - r)
  have hends := aux_lem_replace_cube_endpoints z zc R r hR hr hinside
  have hshift : ∀ j, |zb j - zc j| ≤ r := by
    intro j
    by_cases hj : j = j₀
    · subst j
      simp only [zb, Function.update_self]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    · simp only [zb, Function.update_of_ne hj, sub_self, abs_zero, hr.le]
  refine ⟨zb, ?_, ?_, ?_⟩
  · intro x hx
    rw [centeredCube_eq_pi] at hx ⊢
    intro j _
    have hxj := hx j (Set.mem_univ j)
    have he := hends j
    by_cases hj : j = j₀
    · subst j
      simp only [zb, Function.update_self, Set.mem_Ioo] at hxj
      split_ifs at hxj with hc <;> constructor <;> linarith
    · simp only [zb, Function.update_of_ne hj] at hxj
      exact ⟨lt_of_le_of_lt he.1 hxj.1, lt_of_lt_of_le hxj.2 he.2⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    rw [centeredCube_eq_pi] at hx hy
    have hxj := hx j₀ (Set.mem_univ j₀)
    have hyj := hy j₀ (Set.mem_univ j₀)
    simp only [zb, Function.update_self, Set.mem_Ioo] at hyj
    simp only [Set.mem_Ioo] at hxj
    split_ifs at hyj <;> linarith
  · intro x hx y hy
    rw [centeredCube_eq_pi] at hx hy
    have hjbound : ∀ j : Fin d, (x j - y j) ^ 2 ≤ (2 * r) ^ 2 := by
      intro j
      have hxj := hx j (Set.mem_univ j)
      have hyj := hy j (Set.mem_univ j)
      simp only [Set.mem_Ioo] at hxj hyj
      have hsj := (abs_le.mp (hshift j))
      have hdist : |x j - y j| ≤ 2 * r := abs_le.mpr ⟨by linarith, by linarith⟩
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdist
    have hsum : (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * (2 * r) ^ 2 := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hjbound j)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hscale : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hscale (sq_nonneg (2 * r))
    nlinarith [hsum]

/-- The support-kernel estimate in the repository's normalized fractional
seminorm, with a finite-domain guard before taking real values. -/
theorem aux_lem_replace_fractional_support_poincare {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (s : Set.Ioo (0 : ℝ) 1)
    (u : DomainL2 (centeredCube z R hR)) (A B : Set (SpatialCoordinates d))
    (hB : MeasurableSet B)
    (hBinside : B ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hBpos : 0 < volume.real B) (hAB : Disjoint A B)
    (hsupport : ∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)),
      x ∉ A → u x = 0)
    (D : ℝ) (hD : 0 < D)
    (hdiam : ∀ x ∈ A, ∀ y ∈ B,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ D)
    (hfin : cubeFractionalL2Seminorm hd z R hR s (fun _ : Fin 1 => u) < ⊤) :
    ‖u‖ ^ 2 ≤
      (D ^ ((d : ℝ) + 2 * (s : ℝ)) *
        volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) /
        ((s : ℝ) * volume.real B)) *
      (cubeFractionalL2Seminorm hd z R hR s (fun _ : Fin 1 => u)).toReal ^ 2 := by
  let μ := volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))
  let W : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^
      ((d : ℝ) + 2 * (s : ℝ))
  have he : 0 ≤ (d : ℝ) + 2 * (s : ℝ) := by
    have hs := s.property.1
    positivity
  have hzero : ∀ᵐ y ∂μ.restrict B, u y = 0 := by
    filter_upwards [ae_restrict_of_ae hsupport, ae_restrict_mem hB] with y hy hyB
    exact hy (fun hyA => Set.disjoint_left.mp hAB hyA hyB)
  have hden : ∀ x ∈ A, ∀ y ∈ B,
      W x y ≤ ENNReal.ofReal (D ^ ((d : ℝ) + 2 * (s : ℝ))) := by
    intro x hx y hy
    rw [← ENNReal.ofReal_rpow_of_pos hD]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hdiam x hx y hy)) he
  have hraw := aux_lem_replace_support_kernel_bound μ u A B hB hsupport hzero W
    (ENNReal.ofReal (D ^ ((d : ℝ) + 2 * (s : ℝ)))) hden
  have hL2 : (∫⁻ x, ENNReal.ofReal ((u x) ^ 2) ∂μ) = ENNReal.ofReal (‖u‖ ^ 2) := by
    simpa only [Fin.sum_univ_one] using
      lintegral_coordinate_sq_eq_sum_norm_sq (fun _ : Fin 1 => u)
  have hμB : μ B = volume B := by
    rw [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBinside]
  rw [hL2, hμB] at hraw
  have hsemi :
      (cubeFractionalL2Seminorm hd z R hR s (fun _ : Fin 1 => u)) ^ (2 : ℕ) =
        (ENNReal.ofReal (s : ℝ) /
          volume (centeredCube z R hR : Set (SpatialCoordinates d))) *
        ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2) / W x y ∂μ ∂μ := by
    rw [← ENNReal.rpow_natCast, cubeFractionalL2Seminorm, ← ENNReal.rpow_mul]
    norm_num only [Nat.cast_ofNat, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      ENNReal.rpow_one, Fin.sum_univ_one]
    rfl
  have hscaled := mul_le_mul_right hraw
    (ENNReal.ofReal (s : ℝ) /
      volume (centeredCube z R hR : Set (SpatialCoordinates d)))
  rw [← hsemi] at hscaled
  have hreal := ENNReal.toReal_mono (ENNReal.pow_ne_top hfin.ne) hscaled
  have hs : 0 < (s : ℝ) := s.property.1
  have hV := centeredCube_volume_pos z hR
  have hDp : 0 < D ^ ((d : ℝ) + 2 * (s : ℝ)) := Real.rpow_pos_of_pos hD _
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hs.le, ENNReal.toReal_ofReal (sq_nonneg ‖u‖),
    ENNReal.toReal_ofReal hDp.le] at hreal
  calc
    ‖u‖ ^ 2 =
        (D ^ ((d : ℝ) + 2 * (s : ℝ)) *
          volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) /
          ((s : ℝ) * volume.real B)) *
        ((s : ℝ) / volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) *
          (‖u‖ ^ 2 / D ^ ((d : ℝ) + 2 * (s : ℝ)) * volume.real B)) := by
      field_simp [hs.ne', hV.ne', hDp.ne', hBpos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hreal (by positivity)

/-- The neighbour construction gives the required scale power for all small
cells, using only the root fractional seminorm and vanishing off the cell. -/
theorem aux_lem_replace_small_cell_fractional_poincare {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (s : Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (zc : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), 3 * r ≤ R →
        (centeredCube zc r hr : Set (SpatialCoordinates d)) ⊆
          (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ u : DomainL2 (centeredCube z R hR),
        (∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)),
          x ∉ (centeredCube zc r hr : Set (SpatialCoordinates d)) → u x = 0) →
        cubeFractionalL2Seminorm hd z R hR s (fun _ : Fin 1 => u) < ⊤ →
        ‖u‖ ^ 2 ≤ C * r ^ (2 * (s : ℝ)) *
          (cubeFractionalL2Seminorm hd z R hR s (fun _ : Fin 1 => u)).toReal ^ 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < (s : ℝ) := s.property.1
  have hV := centeredCube_volume_pos z hR
  let C : ℝ := (2 * (d : ℝ)) ^ ((d : ℝ) + 2 * (s : ℝ)) *
    volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) / (s : ℝ)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro zc r hr hsmall hinside u hsupport hfin
  obtain ⟨zb, hbinside, hab, hdiam⟩ :=
    aux_lem_replace_cell_neighbour (by omega : 1 ≤ d) z zc R r hR hr hsmall hinside
  have h := aux_lem_replace_fractional_support_poincare hd z R hR s u
    (centeredCube zc r hr : Set (SpatialCoordinates d))
    (centeredCube zb r hr : Set (SpatialCoordinates d))
    (centeredCube zb r hr).isOpen.measurableSet hbinside
    (centeredCube_volume_pos zb hr) hab hsupport
    (2 * (d : ℝ) * r) (by positivity) hdiam hfin
  rw [centeredCube_volume_real zb hr] at h
  have hscale : (2 * (d : ℝ) * r) ^ ((d : ℝ) + 2 * (s : ℝ)) *
      volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) /
      ((s : ℝ) * r ^ d) = C * r ^ (2 * (s : ℝ)) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 2 * (d : ℝ)) hr.le,
      Real.rpow_add hr, Real.rpow_natCast]
    dsimp [C]
    field_simp [hs.ne', hr.ne']
  rwa [hscale] at h

/-- Global root fractional coercivity implies the uniform killed-cell estimate
on every contained cube. The large-cell branch uses the root L² term; the
small-cell branch uses a disjoint neighbour and the support estimate. -/
theorem aux_lem_replace_cells_of_root_fractional {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (s : Set.Ioo (0 : ℝ) 1)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (B : ℝ) (hB : 0 < B)
    (hfrac : ∀ u ∈ E.domain,
      cubeFractionalL2Seminorm hd z R hR s (fun _ : Fin 1 => u) < ⊤ ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z R hR s u ≤ B * E.form u u) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (zc : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (centeredCube zc r hr : Set (SpatialCoordinates d)) ⊆
          (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ (V : Submodule ℝ (DomainL2 (centeredCube z R hR))),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
          (centeredCube zc r hr : Set (SpatialCoordinates d)) V →
      ∀ u ∈ V, ‖u‖ ^ 2 ≤ K * r ^ (2 * (s : ℝ)) * E.form u u := by
  obtain ⟨C, hC, hlocal⟩ := aux_lem_replace_small_cell_fractional_poincare hd z R hR s
  let m : ℝ := volume.real (centeredCube z R hR : Set (SpatialCoordinates d))
  have hm : 0 < m := centeredCube_volume_pos z hR
  have hr3 : 0 < R / 3 := by positivity
  have hp3 : 0 < (R / 3) ^ (2 * (s : ℝ)) := Real.rpow_pos_of_pos hr3 _
  let L : ℝ := B * m / (R / 3) ^ (2 * (s : ℝ))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let K : ℝ := C * B + L + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hCK : C * B ≤ K :=
    (le_add_of_nonneg_right hL).trans (le_add_of_nonneg_right zero_le_one)
  have hLK : L ≤ K :=
    (le_add_of_nonneg_left (mul_nonneg hC.le hB.le)).trans
      (le_add_of_nonneg_right zero_le_one)
  refine ⟨K, hK, ?_⟩
  intro zc r hr hinside V hV u hu
  have hud : u ∈ E.domain := hV.le_domain hu
  obtain ⟨hfin, hnorm⟩ := hfrac u hud
  have he : 0 ≤ E.form u u := E.form_nonneg u hud
  have hsem : (cubeFractionalL2Seminorm hd z R hR s
      (fun _ : Fin 1 => u)).toReal ^ 2 ≤ B * E.form u u := by
    simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm, _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSqNorm,
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSeminormSq, Fin.sum_univ_one] at hnorm
    exact (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hm.le)).trans hnorm
  have hroot : ‖u‖ ^ 2 ≤ B * m * E.form u u := by
    simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm, _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSqNorm,
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSeminormSq, Fin.sum_univ_one] at hnorm
    have hdiv : ‖u‖ ^ 2 / m ≤ B * E.form u u :=
      (le_add_of_nonneg_left (sq_nonneg _)).trans hnorm
    have h := (div_le_iff₀ hm).mp hdiv
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  by_cases hsmall : 3 * r ≤ R
  · have hz := (ae_restrict_iff'
      ((centeredCube z R hR).isOpen.measurableSet.diff
        (centeredCube zc r hr).isOpen.measurableSet)).mp
      (aux_lem_replace_killed_ae_zero E (centeredCube zc r hr).isOpen hV hu)
    have hsupport : ∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)),
        x ∉ (centeredCube zc r hr : Set (SpatialCoordinates d)) → u x = 0 := by
      filter_upwards [ae_restrict_of_ae hz,
        ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hx hxQ
      intro hxq
      exact hx ⟨hxQ, hxq⟩
    have hp := hlocal zc r hr hsmall hinside u hsupport hfin
    calc
      ‖u‖ ^ 2 ≤ C * r ^ (2 * (s : ℝ)) *
          (cubeFractionalL2Seminorm hd z R hR s (fun _ : Fin 1 => u)).toReal ^ 2 := hp
      _ ≤ C * r ^ (2 * (s : ℝ)) * (B * E.form u u) :=
        mul_le_mul_of_nonneg_left hsem (mul_nonneg hC.le (Real.rpow_nonneg hr.le _))
      _ = (C * B) * r ^ (2 * (s : ℝ)) * E.form u u := by ring
      _ ≤ K * r ^ (2 * (s : ℝ)) * E.form u u :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hr.le _)) he
  · have hs : 0 ≤ 2 * (s : ℝ) := by have hs := s.property.1; positivity
    have hpow : (R / 3) ^ (2 * (s : ℝ)) ≤ r ^ (2 * (s : ℝ)) :=
      Real.rpow_le_rpow hr3.le (by linarith) hs
    have hscale : B * m ≤ L * r ^ (2 * (s : ℝ)) := by
      calc
        B * m = L * (R / 3) ^ (2 * (s : ℝ)) :=
          (div_mul_cancel₀ _ hp3.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hL
    exact hroot.trans ((mul_le_mul_of_nonneg_right hscale he).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLK (Real.rpow_nonneg hr.le _)) he))

theorem aux_lem_replace_killed_inner_orth {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    {U V : Set (SpatialCoordinates d)} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    {D₁ D₂ : Submodule ℝ (DomainL2 Q)}
    (h₁ : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D₁)
    (h₂ : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E V D₂)
    {a b : DomainL2 Q} (ha : a ∈ D₁) (hb : b ∈ D₂) :
    inner ℝ a b = 0 := by
  have ha0 := (ae_restrict_iff'
    (Q.isOpen.measurableSet.diff hU.measurableSet)).mp
      (aux_lem_replace_killed_ae_zero E hU h₁ ha)
  have hb0 := (ae_restrict_iff'
    (Q.isOpen.measurableSet.diff hV.measurableSet)).mp
      (aux_lem_replace_killed_ae_zero E hV h₂ hb)
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae ha0, ae_restrict_of_ae hb0,
    ae_restrict_mem Q.isOpen.measurableSet] with x hax hbx hxQ
  by_cases hxU : x ∈ U
  · have hxV : x ∉ V := fun hxV => Set.disjoint_left.mp hUV hxU hxV
    have hbx0 : b x = 0 := hbx ⟨hxQ, hxV⟩
    simp only [hbx0, inner_zero_right, Pi.zero_apply]
  · have hax0 : a x = 0 := hax ⟨hxQ, hxU⟩
    simp only [hax0, inner_zero_left, Pi.zero_apply]

/-- Cellwise coercivity passes to the algebraic sum with the same constant.
The energy measure already present in the principal supplies form orthogonality. -/
theorem aux_lem_replace_coercivity_sum {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (n : ℕ) (q : Fin n → Opens (SpatialCoordinates d))
    (hdisjoint : Pairwise (fun i j => Disjoint
      (q i : Set (SpatialCoordinates d)) (q j : Set (SpatialCoordinates d))))
    (Vi : Fin n → Submodule ℝ (DomainL2 Q))
    (hVi : ∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E (q i : Set (SpatialCoordinates d)) (Vi i))
    (L : ℝ) (hlocal : ∀ i w, w ∈ Vi i → ‖w‖ ^ 2 ≤ L * E.form w w) :
    ∀ v ∈ (⨆ i, Vi i), ‖v‖ ^ 2 ≤ L * E.form v v := by
  classical
  intro v hv
  have hv' : v ∈ ⨆ i ∈ (Finset.univ : Finset (Fin n)), Vi i := by
    simpa only [Finset.mem_univ, iSup_pos] using hv
  obtain ⟨p, hp⟩ :=
    (Submodule.mem_iSup_finset_iff_exists_sum (s := Finset.univ) Vi v).mp hv'
  let w : Fin n → DomainL2 Q := fun i => (p i).val
  have hw : ∀ i, w i ∈ Vi i := fun i => (p i).property
  have hwd : ∀ i, w i ∈ E.domain := fun i => (hVi i).le_domain (hw i)
  have hsum : ∑ i, w i = v := hp
  have hver : v ∈ E.domain := hsum ▸ E.domain.sum_mem (fun i _ => hwd i)
  have hi : Pairwise (fun i j => inner ℝ (w i) (w j) = 0) := by
    intro i j hij
    exact aux_lem_replace_killed_inner_orth E (q i).isOpen (q j).isOpen
      (hdisjoint hij) (hVi i) (hVi j) (hw i) (hw j)
  have he : Pairwise (fun i j => E.form (w i) (w j) = 0) := by
    intro i j hij
    exact aux_lem_replace_killed_form_orth E Γ (q i).isOpen (q j).isOpen
      (hdisjoint hij) (hVi i) (hVi j) (hw i) (hw j)
  have hnorm : ‖v‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
    rw [← hsum, ← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · exact real_inner_self_eq_norm_sq (w i)
    · intro j _ hji
      exact hi hji
    · intro hi'
      exact (hi' (Finset.mem_univ i)).elim
  have henergy : E.form v v = ∑ i, E.form (w i) (w i) := by
    rw [← hsum]
    exact (aux_lem_replace_form_sum E w hwd v hver).2.2 he
  rw [hnorm, henergy, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hlocal i (w i) (hw i)


theorem aux_lem_replace_gap_projection_exists {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ u ∈ E.domain, E.form u u = (limitFormEnergy G u).toReal)
    {U : Set (SpatialCoordinates d)} (_hU : IsOpen U)
    {D : Submodule ℝ (DomainL2 Q)} (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D)
    (u : DomainL2 Q) (hu : u ∈ E.domain) :
    ∃ p : DomainL2 Q, p ∈ D ∧ ∀ v ∈ D, E.form (u - p) v = 0 := by
  exact aux_lem_replace_limit_projection_exists G E hEdom hEenergy hD u hu


/-- Uniform killed-cell coercivity obtained from the represented root form. -/
theorem aux_lem_replace_cell_coercivity (d : ℕ) (hd : 2 ≤ d)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE : ℕ → ℕ),
      in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE →
      ∀ᵐ omega ∂P, ∀ root : ℕ,
        let Q := centeredCube (z root) (r root) (hr root)
        ∀ (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
          (_hEdom : E.domain = limitFormDomain (GE root omega))
          (_hEenergy : ∀ u ∈ E.domain,
            E.form u u = (limitFormEnergy (GE root omega) u).toReal),
          ∃ (s K : ℝ), (1 / 2 < s ∧ s < 1 ∧ 0 < K) ∧
            ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
              let q := centeredCube zc rc hrc
              ∀ (_hinside : (q : Set (SpatialCoordinates d)) ⊆
                  (Q : Set (SpatialCoordinates d)))
                (V : Submodule ℝ (DomainL2 Q))
                (_hV : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E (q : Set (SpatialCoordinates d)) V),
                ∀ v ∈ V, ‖v‖ ^ 2 ≤ K * rc ^ (2 * s) * E.form v v := by
  obtain ⟨delta0, hdelta0, hroot⟩ :=
    aux_lem_replace_ae_root_fractional_coercivity d hd I Pin _Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Rm H Ω _ P field z r hr Sspace GN GE NE hjoint
  have hall := ae_all_iff.mpr
    (fun root => hroot model hmodel Rm H Ω P field z r hr Sspace GN GE NE hjoint root)
  filter_upwards [hall] with omega hω
  intro root Q E hEdom hEenergy
  obtain ⟨B, hB, hfrac⟩ := hω root
  obtain ⟨K, hK, hcell⟩ := aux_lem_replace_cells_of_root_fractional hd
    (z root) (r root) (hr root) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder E B hB (hfrac E hEdom hEenergy)
  refine ⟨3 / 4, K, ⟨by norm_num, by norm_num, hK⟩, ?_⟩
  exact hcell

/-- The finite disjoint-family estimate follows from the uniform cell estimate.
Gamma is the existing energy-measure binder of the frozen principal. -/
theorem aux_lem_replace_gap_coercivity (d : ℕ) (hd : 2 ≤ d)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE : ℕ → ℕ),
      in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE →
      ∀ᵐ omega ∂P, ∀ root : ℕ,
        let Q := centeredCube (z root) (r root) (hr root)
        ∀ (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
          (_hEdom : E.domain = limitFormDomain (GE root omega))
          (_hEenergy : ∀ u ∈ E.domain,
            E.form u u = (limitFormEnergy (GE root omega) u).toReal)
          (_Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E),
          ∃ (s K : ℝ), (1 / 2 < s ∧ s < 1 ∧ 0 < K) ∧
            ∀ (n : ℕ) (zc : Fin n → SpatialCoordinates d)
              (rc : Fin n → ℝ) (hrc : ∀ i, 0 < rc i),
              let q : Fin n → Opens (SpatialCoordinates d) :=
                fun i => centeredCube (zc i) (rc i) (hrc i)
              ∀ (h : ℝ) (_hh : 0 < h)
                (_hside : ∀ i, rc i ≤ h)
                (_hinside : ∀ i, (q i : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
                (_hdisjoint : Pairwise (fun i j =>
                  Disjoint (q i : Set (SpatialCoordinates d))
                    (q j : Set (SpatialCoordinates d))))
                (Vi : Fin n → Submodule ℝ (DomainL2 Q))
                (_hVi : ∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
                  (q i : Set (SpatialCoordinates d)) (Vi i)),
                let Vsum : Submodule ℝ (DomainL2 Q) := ⨆ i, Vi i
                ∀ v ∈ Vsum, ‖v‖ ^ 2 ≤ K * h ^ (2 * s) * E.form v v := by
  obtain ⟨delta0, hdelta0, hcell⟩ := aux_lem_replace_cell_coercivity d hd I Pin _Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Rm H Ω _ P field z r hr Sspace GN GE NE hjoint
  filter_upwards [hcell model hmodel Rm H Ω P field z r hr Sspace GN GE NE hjoint]
    with omega hω
  intro root Q E hEdom hEenergy Gamma
  obtain ⟨s, K, hsK, hc⟩ := hω root E hEdom hEenergy
  refine ⟨s, K, hsK, ?_⟩
  intro n zc rc hrc q h hh hside hinside hdisjoint Vi hVi Vsum v hv
  refine aux_lem_replace_coercivity_sum E Gamma n q hdisjoint Vi hVi
    (K * h ^ (2 * s)) ?_ v hv
  intro i w hw
  have hbase := hc (zc i) (rc i) (hrc i) (hinside i) (Vi i) (hVi i) w hw
  have hs : 0 ≤ 2 * s := by linarith [hsK.1]
  have hpow : (rc i) ^ (2 * s) ≤ h ^ (2 * s) :=
    Real.rpow_le_rpow (hrc i).le (hside i) hs
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hsK.2.2.le)
    (E.form_nonneg w ((hVi i).le_domain hw)))

/-- Uniform killed-cell coercivity at the fixed exponent `3/2 = 2 * (3/4)` (paper: `H^{3/4}` Poincare on cells). -/
theorem aux_lem_replace_cell_coercivity_v2 (d : ℕ) (hd : 2 ≤ d)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE : ℕ → ℕ),
      in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE →
      ∀ᵐ omega ∂P, ∀ root : ℕ,
        let Q := centeredCube (z root) (r root) (hr root)
        ∀ (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
          (_hEdom : E.domain = limitFormDomain (GE root omega))
          (_hEenergy : ∀ u ∈ E.domain,
            E.form u u = (limitFormEnergy (GE root omega) u).toReal),
          ∃ K : ℝ, 0 < K ∧
            ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
              let q := centeredCube zc rc hrc
              ∀ (_hinside : (q : Set (SpatialCoordinates d)) ⊆
                  (Q : Set (SpatialCoordinates d)))
                (V : Submodule ℝ (DomainL2 Q))
                (_hV : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E (q : Set (SpatialCoordinates d)) V),
                ∀ v ∈ V, ‖v‖ ^ 2 ≤ K * rc ^ ((3 : ℝ) / 2) * E.form v v := by
  obtain ⟨delta0, hdelta0, hroot⟩ :=
    aux_lem_replace_ae_root_fractional_coercivity d hd I Pin _Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Rm H Ω _ P field z r hr Sspace GN GE NE hjoint
  have hall := ae_all_iff.mpr
    (fun root => hroot model hmodel Rm H Ω P field z r hr Sspace GN GE NE hjoint root)
  filter_upwards [hall] with omega hω
  intro root Q E hEdom hEenergy
  obtain ⟨B, hB, hfrac⟩ := hω root
  obtain ⟨K, hK, hcell⟩ := aux_lem_replace_cells_of_root_fractional hd
    (z root) (r root) (hr root) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder E B hB (hfrac E hEdom hEenergy)
  refine ⟨K, hK, ?_⟩
  intro zc rc hrc q hinside V hV v hv
  have h : ‖v‖ ^ 2 ≤ K * rc ^ (2 * (3 / 4 : ℝ)) * E.form v v := hcell zc rc hrc hinside V hV v hv
  have e : (2 * (3 / 4 : ℝ)) = (3 : ℝ) / 2 := by norm_num
  rw [e] at h
  exact h

/-- The finite disjoint-family estimate follows from the uniform cell estimate.
Gamma is the existing energy-measure binder of the frozen principal. -/
theorem aux_lem_replace_gap_coercivity_v2 (d : ℕ) (hd : 2 ≤ d)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE : ℕ → ℕ),
      in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE →
      ∀ᵐ omega ∂P, ∀ root : ℕ,
        let Q := centeredCube (z root) (r root) (hr root)
        ∀ (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
          (_hEdom : E.domain = limitFormDomain (GE root omega))
          (_hEenergy : ∀ u ∈ E.domain,
            E.form u u = (limitFormEnergy (GE root omega) u).toReal)
          (_Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E),
          ∃ K : ℝ, 0 < K ∧
            ∀ (n : ℕ) (zc : Fin n → SpatialCoordinates d)
              (rc : Fin n → ℝ) (hrc : ∀ i, 0 < rc i),
              let q : Fin n → Opens (SpatialCoordinates d) :=
                fun i => centeredCube (zc i) (rc i) (hrc i)
              ∀ (h : ℝ) (_hh : 0 < h)
                (_hside : ∀ i, rc i ≤ h)
                (_hinside : ∀ i, (q i : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
                (_hdisjoint : Pairwise (fun i j =>
                  Disjoint (q i : Set (SpatialCoordinates d))
                    (q j : Set (SpatialCoordinates d))))
                (Vi : Fin n → Submodule ℝ (DomainL2 Q))
                (_hVi : ∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
                  (q i : Set (SpatialCoordinates d)) (Vi i)),
                let Vsum : Submodule ℝ (DomainL2 Q) := ⨆ i, Vi i
                ∀ v ∈ Vsum, ‖v‖ ^ 2 ≤ K * h ^ ((3 : ℝ) / 2) * E.form v v := by
  obtain ⟨delta0, hdelta0, hcell⟩ := aux_lem_replace_cell_coercivity_v2 d hd I Pin _Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Rm H Ω _ P field z r hr Sspace GN GE NE hjoint
  filter_upwards [hcell model hmodel Rm H Ω P field z r hr Sspace GN GE NE hjoint]
    with omega hω
  intro root Q E hEdom hEenergy Gamma
  obtain ⟨K, hK, hc⟩ := hω root E hEdom hEenergy
  refine ⟨K, hK, ?_⟩
  intro n zc rc hrc q h hh hside hinside hdisjoint Vi hVi Vsum v hv
  refine aux_lem_replace_coercivity_sum E Gamma n q hdisjoint Vi hVi
    (K * h ^ ((3 : ℝ) / 2)) ?_ v hv
  intro i w hw
  have hbase := hc (zc i) (rc i) (hrc i) (hinside i) (Vi i) (hVi i) w hw
  have hs : 0 ≤ (3 : ℝ) / 2 := by norm_num
  have hpow : (rc i) ^ ((3 : ℝ) / 2) ≤ h ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (hrc i).le (hside i) hs
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hK.le)
    (E.form_nonneg w ((hVi i).le_domain hw)))

/-- **Gap 3** (proof paragraph 2,
"For a source solution, testing `E(u,φ)=⟨f,φ⟩` with the killed `φ = u-u^C`
gives `E(u-u^C) = ⟨f,u-u^C⟩ ≤ ‖f‖₂‖u-u^C‖₂`"): the source estimate
`E(u-uC) ≤ K h^{2s}‖f‖²` for `u = GE root omega f`, plus the resulting
`h → 0` limit of the cellwise sum.  The paper's own proof *treats*
`E(u,φ) = ⟨f,φ⟩` for `u = G_Ef` as already established (it is not re-derived
in this lemma of the paper); this
fact is carried as the explicit input `hweak` below, rather than re-derived
from `limitFormEnergy`'s Legendre-dual definition (in `SubdiffusiveProcess/VariationalResponses/LimitForm.lean`). `hcoer` is exactly clause 2 (`aux_lem_replace_gap_coercivity`'s own
conclusion for this `z r hr`), threaded in rather than re-derived. -/
theorem aux_lem_replace_gap_source_bound {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (s K : ℝ) (hK : 0 < K)
    (Vsum : Submodule ℝ (DomainL2 Q))
    (f u uC : DomainL2 Q) (_hu : u ∈ E.domain) (huC : uC ∈ E.domain)
    (hweak : ∀ φ ∈ E.domain, E.form u φ = inner ℝ f φ)
    (hcross : E.form uC (u - uC) = 0)
    (herr : u - uC ∈ Vsum) (herr_dom : u - uC ∈ E.domain)
    (h : ℝ) (hh : 0 < h)
    (hcoer : ∀ v ∈ Vsum, ‖v‖ ^ 2 ≤ K * h ^ (2 * s) * E.form v v) :
    E.form (u - uC) (u - uC) ≤ K * h ^ (2 * s) * ‖f‖ ^ 2 := by
  classical
  have hsplit : E.form u (u - uC) = E.form uC (u - uC) + E.form (u - uC) (u - uC) := by
    have hlin := E.form_add_left uC huC (u - uC) herr_dom (u - uC) herr_dom
    have heq : uC + (u - uC) = u := by abel
    rwa [heq] at hlin
  rw [hcross, zero_add] at hsplit
  have hweak' : E.form u (u - uC) = inner ℝ f (u - uC) := hweak (u - uC) herr_dom
  rw [hweak'] at hsplit
  set e : ℝ := E.form (u - uC) (u - uC) with e_def
  set n : ℝ := ‖u - uC‖ with n_def
  have he_nonneg : 0 ≤ e := E.form_nonneg _ herr_dom
  have hn_nonneg : 0 ≤ n := norm_nonneg _
  have he_le : e ≤ ‖f‖ * n := hsplit ▸ real_inner_le_norm f (u - uC)
  have hcoer' : n ^ 2 ≤ K * h ^ (2 * s) * e := hcoer (u - uC) herr
  have hpow_nonneg : (0 : ℝ) ≤ h ^ (2 * s) := Real.rpow_nonneg hh.le _
  rcases eq_or_lt_of_le he_nonneg with he0 | he_pos
  · rw [← he0]
    positivity
  · have hesq : e ^ 2 ≤ ‖f‖ ^ 2 * n ^ 2 := by
      have hmul := mul_le_mul he_le he_le he_nonneg
        (mul_nonneg (norm_nonneg f) hn_nonneg)
      nlinarith [hmul]
    have hscaled : ‖f‖ ^ 2 * n ^ 2 ≤ ‖f‖ ^ 2 * (K * h ^ (2 * s) * e) :=
      mul_le_mul_of_nonneg_left hcoer' (sq_nonneg ‖f‖)
    have hfinal : e * e ≤ (K * h ^ (2 * s) * ‖f‖ ^ 2) * e := by
      nlinarith [hesq, hscaled]
    have hdiv := le_of_mul_le_mul_right hfinal he_pos
    linarith [hdiv]

/-- **Gap 4.** The conclusion of `aux_lem_replace_gap_weak_solution` needs `GE root omega` to be symmetric and positive,
which is exactly what `hjoint`'s own convergence clause gives (`GN i (NE n) ω
→ GE i ω`), but only `∀ᵐ ω ∂P`, not for an arbitrary bound variable `omega`.
The argument uses the convergence fact
`hconv : Tendsto (fun n => GN root (NE n) omega) atTop (𝓝 (GE root omega))`,
which is exactly the `i = root` instance of `hjoint`'s own a.e. clause,
available at `lem_replace`'s call site once `omega` is drawn from the good
a.e.-set (i.e. by filtering the event, rather than applying `Filter.Eventually.of_forall`, using `hjoint`'s `∀ᵐ ω ∂P` clause, as in
`_needs` and `aux_lem_replace_gap_coercivity_needs` above).
Proved in full from `hconv`: symmetry/positivity of `GE root omega` from
`volumeResponse_pairing_symm`/`_nonneg` taken to the limit along `NE`:
membership `GE root omega f ∈ E.domain` from `iSup_quadraticDual_apply_image`
(`Variational/DualEnergy.lean`); the bilinear identity from the *real*
polarization identity for `E.form` (`ClosedForm.form_add_self` /
`form_add_smul_self`) matched against `quadraticDual_sub_image` applied at the
two base points `φ` and `-φ` (chosen so the shift lands exactly on `G f + φ`
and `G f - φ`, avoiding any separate "dual energy is even" lemma). -/
theorem aux_lem_replace_gap_weak_solution_needs
    (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE : ℕ → ℕ)
    (hjoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE)
    (omega : Ω) (root : ℕ)
    (hconv : Tendsto (fun n => GN root (NE n) omega) atTop
      (𝓝 (GE root omega)))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain (GE root omega))
    (hEenergy : ∀ u ∈ E.domain,
      E.form u u = (limitFormEnergy (GE root omega) u).toReal)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (_hsupport : ∀ u ∈ E.domain,
      Gamma.measure u (centeredCube (z root) (r root) (hr root) :
        Set (SpatialCoordinates d)).compl = 0)
    (f : DomainL2 (centeredCube (z root) (r root) (hr root))) :
    GE root omega f ∈ E.domain ∧
      ∀ φ ∈ E.domain, E.form (GE root omega f) φ = inner ℝ f φ := by
  classical
  set G := GE root omega with hG_def
  obtain ⟨-, -, -, -, -, -, hGNeq, -⟩ := hjoint
  -- `GN`'s finite-N pairings are symmetric and nonnegative (response-space facts).
  have hpair_symm : ∀ (n : ℕ) (x y : DomainL2 (centeredCube (z root) (r root) (hr root))),
      inner ℝ x (GN root (NE n) omega y) = inner ℝ y (GN root (NE n) omega x) := by
    intro n x y
    rw [hGNeq root (NE n) omega y, hGNeq root (NE n) omega x]
    exact volumeResponse_pairing_symm (Sspace root)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega) (NE n) (z root) (hr root)) x y
  have hpair_nonneg : ∀ (n : ℕ) (x : DomainL2 (centeredCube (z root) (r root) (hr root))),
      0 ≤ inner ℝ x (GN root (NE n) omega x) := by
    intro n x
    rw [hGNeq root (NE n) omega x]
    exact volumeResponse_pairing_nonneg (Sspace root)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega) (NE n) (z root) (hr root)) x
  -- Pointwise convergence `GN root (NE n) omega x → G x`, at any fixed `x`.
  have hconv_pt : ∀ x : DomainL2 (centeredCube (z root) (r root) (hr root)),
      Tendsto (fun n => GN root (NE n) omega x) atTop (𝓝 (G x)) := fun x =>
    ((continuous_id.clm_apply continuous_const).tendsto G).comp hconv
  -- Symmetry and positivity of `G` in the limit.
  have hsym : ∀ x y : DomainL2 (centeredCube (z root) (r root) (hr root)),
      inner ℝ (G x) y = inner ℝ x (G y) := by
    intro x y
    have hL : Tendsto (fun n => inner ℝ x (GN root (NE n) omega y)) atTop
        (𝓝 (inner ℝ x (G y))) := tendsto_const_nhds.inner (hconv_pt y)
    have hR : Tendsto (fun n => inner ℝ x (GN root (NE n) omega y)) atTop
        (𝓝 (inner ℝ y (G x))) := by
      have hR0 : Tendsto (fun n => inner ℝ y (GN root (NE n) omega x)) atTop
          (𝓝 (inner ℝ y (G x))) := tendsto_const_nhds.inner (hconv_pt x)
      exact hR0.congr (fun n => (hpair_symm n x y).symm)
    have hxy : inner ℝ x (G y) = inner ℝ y (G x) := tendsto_nhds_unique hL hR
    exact (real_inner_comm y (G x)).trans hxy.symm
  have hpos : ∀ x : DomainL2 (centeredCube (z root) (r root) (hr root)), 0 ≤ inner ℝ x (G x) := by
    intro x
    have hbound : ∀ᶠ n in (atTop : Filter ℕ), (0 : ℝ) ≤ inner ℝ x (GN root (NE n) omega x) :=
      Filter.Eventually.of_forall (fun n => hpair_nonneg n x)
    have htend : Tendsto (fun n => inner ℝ x (GN root (NE n) omega x)) atTop
        (𝓝 (inner ℝ x (G x))) := tendsto_const_nhds.inner (hconv_pt x)
    exact ge_of_tendsto htend hbound
  -- Finiteness of `limitFormEnergy G` on `E.domain`.
  have hfin_top : ∀ u ∈ E.domain, limitFormEnergy G u ≠ ⊤ := by
    intro u hu
    have hu' : u ∈ limitFormDomain G := by rw [← hEdom]; exact hu
    exact hu'.ne
  have hfin_bot : ∀ u : DomainL2 (centeredCube (z root) (r root) (hr root)),
      limitFormEnergy G u ≠ ⊥ := fun u =>
    (limitFormEnergy_nonneg G u).trans_lt' (by
      simp) |>.ne'
  -- Step A: `G f ∈ E.domain`.
  have hval : limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) :=
    iSup_quadraticDual_apply_image G hsym hpos f
  have hGfdom : G f ∈ E.domain := by
    have hmem : G f ∈ limitFormDomain G := by
      show limitFormEnergy G (G f) < (⊤ : EReal)
      rw [hval]
      exact EReal.coe_lt_top _
    rwa [← hEdom] at hmem
  refine ⟨hGfdom, ?_⟩
  intro φ hφ
  have hnφ : -φ ∈ E.domain := E.domain.neg_mem hφ
  have hGfpφ : G f + φ ∈ E.domain := E.domain.add_mem hGfdom hφ
  have hGfmφ : G f - φ ∈ E.domain := E.domain.sub_mem hGfdom hφ
  -- The common base value `E.form φ φ = (limitFormEnergy G φ).toReal
  --   = (limitFormEnergy G (-φ)).toReal`.
  have hbase_eq : (limitFormEnergy G φ).toReal = (limitFormEnergy G (-φ)).toReal := by
    rw [← hEenergy φ hφ, ← hEenergy (-φ) hnφ,
      E.form_neg_left hφ hnφ, E.form_neg_right hφ hφ, neg_neg]
  -- Shift identity at `G f + φ`, via `quadraticDual_sub_image` with base `φ`, image point `-f`.
  have hA : limitFormEnergy G (G f + φ) =
      limitFormEnergy G φ -
        ((2 * inner ℝ (-f) φ - inner ℝ (-f) (G (-f)) : ℝ) : EReal) := by
    have h := quadraticDual_sub_image G hsym φ (-f)
    have hGf' : G (-f) = -(G f) := map_neg G f
    have heq : φ - G (-f) = G f + φ := by rw [hGf']; abel
    rwa [heq] at h
  have hB : limitFormEnergy G (G f - φ) =
      limitFormEnergy G (-φ) -
        ((2 * inner ℝ (-f) (-φ) - inner ℝ (-f) (G (-f)) : ℝ) : EReal) := by
    have h := quadraticDual_sub_image G hsym (-φ) (-f)
    have hGf' : G (-f) = -(G f) := map_neg G f
    have heq : (-φ) - G (-f) = G f - φ := by rw [hGf']; abel
    rwa [heq] at h
  have hinner_simp1 : inner ℝ (-f) φ = -inner ℝ f φ := inner_neg_left f φ
  have hinner_simp2 : inner ℝ (-f) (-φ) = inner ℝ f φ := inner_neg_neg f φ
  have hinner_simp3 : inner ℝ (-f) (G (-f)) = inner ℝ f (G f) := by
    have hGf' : G (-f) = -(G f) := map_neg G f
    rw [hGf', inner_neg_neg]
  rw [hinner_simp1, hinner_simp3] at hA
  rw [hinner_simp2, hinner_simp3] at hB
  have hAr : (limitFormEnergy G (G f + φ)).toReal =
      (limitFormEnergy G φ).toReal - (2 * (-inner ℝ f φ) - inner ℝ f (G f)) := by
    rw [hA, EReal.toReal_sub (hfin_top φ hφ) (hfin_bot φ)
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hBr : (limitFormEnergy G (G f - φ)).toReal =
      (limitFormEnergy G (-φ)).toReal - (2 * inner ℝ f φ - inner ℝ f (G f)) := by
    rw [hB, EReal.toReal_sub (hfin_top (-φ) hnφ) (hfin_bot (-φ))
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hdiff : (limitFormEnergy G (G f + φ)).toReal -
      (limitFormEnergy G (G f - φ)).toReal = 4 * inner ℝ f φ := by
    rw [hAr, hBr, hbase_eq]; ring
  have hpolar : E.form (G f + φ) (G f + φ) - E.form (G f - φ) (G f - φ) =
      4 * E.form (G f) φ := by
    have h1 := E.form_add_self hGfdom hφ
    have h2 := E.form_add_smul_self (-1 : ℝ) hGfdom hφ
    simp only [neg_one_smul] at h2
    have hsub : G f + (-φ) = G f - φ := by abel
    rw [hsub] at h2
    linarith [h1, h2]
  have hE1 : E.form (G f + φ) (G f + φ) = (limitFormEnergy G (G f + φ)).toReal :=
    hEenergy _ hGfpφ
  have hE2 : E.form (G f - φ) (G f - φ) = (limitFormEnergy G (G f - φ)).toReal :=
    hEenergy _ hGfmφ
  have : 4 * E.form (G f) φ = 4 * inner ℝ f φ := by
    rw [← hpolar, hE1, hE2, hdiff]
  linarith [this]


/-- **Gap 5**: elementary real-analysis choice of `h0`, given the source bound
`K h^{2s} ‖f‖² ≤ eps` (Gap 3): the function `h0` used at `h → 0` in the third
clause. Self-contained (no Dirichlet-form
content), independent of Gaps 1-4. -/
theorem aux_lem_replace_gap_epsilon_choice (s K normf_sq : ℝ)
    (hs1 : 1 / 2 < s) (_hs2 : s < 1) (hK : 0 < K) (hnf : 0 ≤ normf_sq) :
    ∃ h0 : ℝ → ℝ, (∀ eps : ℝ, 0 < eps → 0 < h0 eps) ∧
      ∀ eps : ℝ, 0 < eps → ∀ h : ℝ, 0 < h → h ≤ h0 eps →
        K * h ^ (2 * s) * normf_sq < eps := by
  classical
  set h0 : ℝ → ℝ := fun eps => min 1 (eps / (K * normf_sq + 1)) with h0_def
  refine ⟨h0, fun eps heps => lt_min one_pos (by positivity), ?_⟩
  intro eps heps h hh hh0
  have hhle1 : h ≤ 1 := hh0.trans (min_le_left _ _)
  have hhle2 : h ≤ eps / (K * normf_sq + 1) := hh0.trans (min_le_right _ _)
  have h2s1 : (1 : ℝ) ≤ 2 * s := by linarith
  have hpow_le : h ^ (2 * s) ≤ h ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hh hhle1 h2s1
  rw [Real.rpow_one] at hpow_le
  have hKnf : 0 ≤ K * normf_sq := by positivity
  have hstep1 : K * h ^ (2 * s) * normf_sq ≤ K * h * normf_sq := by
    nlinarith [mul_nonneg hKnf (sub_nonneg.mpr hpow_le)]
  have hden_pos : (0 : ℝ) < K * normf_sq + 1 := by positivity
  have hstep2 : K * h * normf_sq ≤ K * (eps / (K * normf_sq + 1)) * normf_sq := by
    nlinarith [mul_le_mul_of_nonneg_left hhle2 hKnf]
  have hstep3 : K * (eps / (K * normf_sq + 1)) * normf_sq < eps := by
    have heq : K * (eps / (K * normf_sq + 1)) * normf_sq
        = (K * normf_sq) * eps / (K * normf_sq + 1) := by ring
    rw [heq, div_lt_iff₀ hden_pos]
    nlinarith [heps, hKnf]
  linarith [hstep1, hstep2, hstep3]

/-- Lemma `mfd:lem-replace`, 
the source bound and the cell coercivity are at the fixed exponent `h^(3/2)` (fractional Poincare at `H^(3/4)`), i.e. the old
`exists s in (1/2,1)` with `h^(2s)` is replaced by `s = 3/4`.  `K` is the (omega-, root-, form-dependent) constant of
`(eq:mfd-1)`, chosen before `f` and the family `C`; `h0` depends only on `eps`, `K`, `f`, so the limit `h -> 0` is uniform in the
choice of the family.  Clause 2 (uniform cell-sum coercivity `‖v‖² ≤ K h^(3/2) E(v)`) is the proof's intermediate inequality and is
kept as an extra conclusion. -/
theorem lem_replace
    (d : ℕ) (hd : 2 ≤ d)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE : ℕ → ℕ),
      in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GE NE NE →
      ∀ᵐ omega ∂P, ∀ root : ℕ,
        let Q := centeredCube (z root) (r root) (hr root)
        ∀ (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
          (_hEdom : E.domain = limitFormDomain (GE root omega))
          (_hEenergy : ∀ u ∈ E.domain,
            E.form u u = (limitFormEnergy (GE root omega) u).toReal)
          (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
          (_hsupport : ∀ u ∈ E.domain,
            Gamma.measure u (Q : Set (SpatialCoordinates d)).compl = 0),
          ∃ K : ℝ,
            0 < K ∧
            (∀ (u : DomainL2 Q), u ∈ E.domain →
                ∀ (n : ℕ) (zc : Fin n → SpatialCoordinates d)
                  (rc : Fin n → ℝ) (hrc : ∀ i, 0 < rc i),
                  let q : Fin n → Opens (SpatialCoordinates d) :=
                    fun i => centeredCube (zc i) (rc i) (hrc i)
                  ∀ (h : ℝ) (_hh : 0 < h)
                    (_hside : ∀ i, rc i ≤ h)
                    (_hinside : ∀ i, (q i : Set (SpatialCoordinates d)) ⊆
                      (Q : Set (SpatialCoordinates d)))
                    (_hdisjoint : Pairwise (fun i j =>
                      Disjoint (q i : Set (SpatialCoordinates d))
                        (q j : Set (SpatialCoordinates d))))
                    (Vi : Fin n → Submodule ℝ (DomainL2 Q))
                    (_hVi : ∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
                      (q i : Set (SpatialCoordinates d)) (Vi i)),
                    let Vsum : Submodule ℝ (DomainL2 Q) := ⨆ i, Vi i
                    let cellUnion : Set (SpatialCoordinates d) :=
                      ⋃ i : Fin n, (q i : Set (SpatialCoordinates d))
                    let Lambda : Fin n → ℝ := fun i =>
                      sInf {t : ℝ | ∃ v : DomainL2 Q, v ∈ Vi i ∧
                        t = (Gamma.measure (u + v)
                          (q i : Set (SpatialCoordinates d))).toReal}
                    ∃ (uC : DomainL2 Q),
                      uC ∈ E.domain ∧
                      u - uC ∈ Vsum ∧
                      (∀ v ∈ Vsum, E.form uC v = 0) ∧
                      E.form u u = E.form uC uC + E.form (u - uC) (u - uC) ∧
                      (∀ i, (Gamma.measure uC (q i : Set (SpatialCoordinates d))).toReal =
                        Lambda i) ∧
                      ((uC : SpatialCoordinates d → ℝ) =ᵐ[
                        volume.restrict ((Q : Set (SpatialCoordinates d)) \ cellUnion)]
                        (u : SpatialCoordinates d → ℝ)) ∧
                      (∑ i : Fin n,
                        ((Gamma.measure u (q i : Set (SpatialCoordinates d))).toReal -
                          Lambda i)) = E.form (u - uC) (u - uC)) ∧
            (∀ (n : ℕ) (zc : Fin n → SpatialCoordinates d)
                  (rc : Fin n → ℝ) (hrc : ∀ i, 0 < rc i),
                  let q : Fin n → Opens (SpatialCoordinates d) :=
                    fun i => centeredCube (zc i) (rc i) (hrc i)
                  ∀ (h : ℝ) (_hh : 0 < h)
                    (_hside : ∀ i, rc i ≤ h)
                    (_hinside : ∀ i, (q i : Set (SpatialCoordinates d)) ⊆
                      (Q : Set (SpatialCoordinates d)))
                    (_hdisjoint : Pairwise (fun i j =>
                      Disjoint (q i : Set (SpatialCoordinates d))
                        (q j : Set (SpatialCoordinates d))))
                    (Vi : Fin n → Submodule ℝ (DomainL2 Q))
                    (_hVi : ∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
                      (q i : Set (SpatialCoordinates d)) (Vi i)),
                    let Vsum : Submodule ℝ (DomainL2 Q) := ⨆ i, Vi i
                    ∀ v ∈ Vsum, ‖v‖ ^ 2 ≤ K * h ^ ((3 : ℝ) / 2) * E.form v v) ∧
            ∀ (f : DomainL2 Q),
              let u := GE root omega f
              ∃ (h0 : ℝ → ℝ),
                (∀ eps : ℝ, 0 < eps → 0 < h0 eps) ∧
                ∀ (n : ℕ) (zc : Fin n → SpatialCoordinates d)
                  (rc : Fin n → ℝ) (hrc : ∀ i, 0 < rc i),
                  let q : Fin n → Opens (SpatialCoordinates d) :=
                    fun i => centeredCube (zc i) (rc i) (hrc i)
                  ∀ (h : ℝ) (_hh : 0 < h)
                    (_hside : ∀ i, rc i ≤ h)
                    (_hinside : ∀ i, (q i : Set (SpatialCoordinates d)) ⊆
                      (Q : Set (SpatialCoordinates d)))
                    (_hdisjoint : Pairwise (fun i j =>
                      Disjoint (q i : Set (SpatialCoordinates d))
                        (q j : Set (SpatialCoordinates d))))
                    (Vi : Fin n → Submodule ℝ (DomainL2 Q))
                    (_hVi : ∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
                      (q i : Set (SpatialCoordinates d)) (Vi i)),
                    let Vsum : Submodule ℝ (DomainL2 Q) := ⨆ i, Vi i
                    let cellUnion : Set (SpatialCoordinates d) :=
                      ⋃ i : Fin n, (q i : Set (SpatialCoordinates d))
                    let Lambda : Fin n → ℝ := fun i =>
                      sInf {t : ℝ | ∃ v : DomainL2 Q, v ∈ Vi i ∧
                        t = (Gamma.measure (u + v)
                          (q i : Set (SpatialCoordinates d))).toReal}
                    ∃ (uC : DomainL2 Q),
                      uC ∈ E.domain ∧
                      u - uC ∈ Vsum ∧
                      (∀ v ∈ Vsum, E.form uC v = 0) ∧
                      E.form u u = E.form uC uC + E.form (u - uC) (u - uC) ∧
                      E.form (u - uC) (u - uC) ≤ K * h ^ ((3 : ℝ) / 2) * ‖f‖ ^ 2 ∧
                      (∀ i, (Gamma.measure uC (q i : Set (SpatialCoordinates d))).toReal =
                        Lambda i) ∧
                      ((uC : SpatialCoordinates d → ℝ) =ᵐ[
                        volume.restrict ((Q : Set (SpatialCoordinates d)) \ cellUnion)]
                        (u : SpatialCoordinates d → ℝ)) ∧
                      (∑ i : Fin n,
                        ((Gamma.measure u (q i : Set (SpatialCoordinates d))).toReal -
                          Lambda i)) = E.form (u - uC) (u - uC) ∧
                      (∀ eps : ℝ, 0 < eps → h ≤ h0 eps →
                        (∑ i : Fin n,
                          ((Gamma.measure u (q i : Set (SpatialCoordinates d))).toReal -
                            Lambda i)) < eps)
    := by
  -- RESTATE DRAFT (exponent fixed to 3/2): helpers `_v2` carry the fixed exponent; old helpers untouched.
  obtain ⟨delta0, hdelta0_pos, hSK⟩ := aux_lem_replace_gap_coercivity_v2 d hd I Pin _Sob
  refine ⟨delta0, hdelta0_pos, ?_⟩
  intro _ _ model hmodel Rm H Ω _ P field z r hr Sspace GN GE NE hjoint
  have hSK_event := hSK model hmodel Rm H Ω P field z r hr Sspace GN GE NE hjoint
  have hconv_all : ∀ᵐ omega ∂P, ∀ i,
      Tendsto (fun n => GN i (NE n) omega) atTop (𝓝 (GE i omega)) := by
    filter_upwards [hjoint.2.2.2.2.2.2.2] with omega hi
    exact fun i => (hi i).1
  filter_upwards [hconv_all, hSK_event] with omega hconv hSKω
  intro root _Q E hEdom hEenergy Gamma hsupport
  obtain ⟨K, hKpos, hcoer⟩ := hSKω root E hEdom hEenergy Gamma
  refine ⟨K, hKpos, ?_, ?_, ?_⟩
  · -- clause 1: cellwise projection assembly, existence of `p i` from Gap 1
    intro u hu n zc rc hrc _q h hh hside hinside hdisjoint Vi hVi
    choose p hpmem hporth using
      fun i => aux_lem_replace_gap_projection_exists (GE root omega) E hEdom hEenergy
        (centeredCube (zc i) (rc i) (hrc i)).isOpen (hVi i) u hu
    exact ⟨u - ∑ i, p i,
      aux_lem_replace_projection_assembly E Gamma (fun i => centeredCube (zc i) (rc i) (hrc i))
        hdisjoint Vi hVi u hu p hpmem hporth⟩
  · -- clause 2: exactly Gap 2's coercivity conclusion
    intro n zc rc hrc _q h hh hside hinside hdisjoint Vi hVi
    exact hcoer n zc rc hrc h hh hside hinside hdisjoint Vi hVi
  · -- clause 3: clause 1's construction again for `u = GE root omega f`, plus
    -- Gaps 3-5 for the source bound and the `h → 0` limit
    intro f u
    have e32 : (2 * (3 / 4 : ℝ)) = (3 : ℝ) / 2 := by norm_num
    obtain ⟨hu, hweak⟩ := aux_lem_replace_gap_weak_solution_needs d hd model H Ω P field z r hr
      Sspace GN GE NE hjoint omega root (hconv root) E hEdom hEenergy Gamma hsupport f
    obtain ⟨h0, h0pos, h0bound⟩ :=
      aux_lem_replace_gap_epsilon_choice (3 / 4) K (‖f‖ ^ 2) (by norm_num) (by norm_num)
        hKpos (sq_nonneg _)
    refine ⟨h0, h0pos, ?_⟩
    intro n zc rc hrc _q h hh hside hinside hdisjoint Vi hVi
    choose p hpmem hporth using
      fun i => aux_lem_replace_gap_projection_exists (GE root omega) E hEdom hEenergy
        (centeredCube (zc i) (rc i) (hrc i)).isOpen (hVi i) u hu
    obtain ⟨huC, hVsum, horth, hpyth, hLam, hae, hsum⟩ :=
      aux_lem_replace_projection_assembly E Gamma (fun i => centeredCube (zc i) (rc i) (hrc i))
        hdisjoint Vi hVi u hu p hpmem hporth
    have hVsum_coer : ∀ v ∈ (⨆ i, Vi i), ‖v‖ ^ 2 ≤ K * h ^ ((3 : ℝ) / 2) * E.form v v :=
      hcoer n zc rc hrc h hh hside hinside hdisjoint Vi hVi
    have herr_dom : u - (u - ∑ i, p i) ∈ E.domain := E.domain.sub_mem hu huC
    have hsrc0 : E.form (u - (u - ∑ i, p i)) (u - (u - ∑ i, p i)) ≤
        K * h ^ (2 * (3 / 4 : ℝ)) * ‖f‖ ^ 2 :=
      aux_lem_replace_gap_source_bound E (3 / 4) K hKpos (⨆ i, Vi i) f u (u - ∑ i, p i) hu huC
        hweak (horth (u - (u - ∑ i, p i)) hVsum) hVsum herr_dom h hh
        (by simpa only [e32] using hVsum_coer)
    have hsrc : E.form (u - (u - ∑ i, p i)) (u - (u - ∑ i, p i)) ≤
        K * h ^ ((3 : ℝ) / 2) * ‖f‖ ^ 2 := by
      rw [e32] at hsrc0
      exact hsrc0
    refine ⟨u - ∑ i, p i, huC, hVsum, horth, hpyth, hsrc, hLam, hae, hsum, ?_⟩
    intro eps heps hh0
    rw [hsum]
    refine lt_of_le_of_lt hsrc ?_
    have hb := h0bound eps heps h hh hh0
    rw [e32] at hb
    exact hb

end SubdiffusiveProcess.Paper
