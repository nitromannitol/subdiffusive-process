module

public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.prop_density
public import SubdiffusiveProcess.Paper.represented_bounds_subseq
public import SubdiffusiveProcess.Paper.reference_coefficients
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.thm_c1_response_positive_moment
public import SubdiffusiveProcess.Paper.thm_c1_response_negative_moment

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.Paper
noncomputable section


/- Proof of `thm_C0` (`mfd:thm-C0`). Route: `aux_thm_C0_main`.
   * `aux_thm_C0_density_inputs`: prop_density applied to the jointly extracted pair after a
     further extraction (reference_coefficients) along which the deterministic kappa ratios
     converge; the limits GE, GF are unchanged by the extraction.
   * `aux_thm_C0_moment_event`: the carried uniform response moments (binder `hResp`) on the
     unit cube, the laws of the represented environments, Markov, and passage of open tails to
     the almost-sure limits give a deterministic A with P[A⁻¹ ≤ Y_E, Y_F ≤ A] > 0.
   * `aux_thm_C0_comparison_core`: dual-formula exclusion of both extreme ratio sets and the
     middle set, C0 = 2 Cstar² A²; `aux_thm_C0_assemble`: one common event inside Gcatalog. -/

theorem aux_thm_C0_common_event {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (p : Ω → Prop) (hp : ∀ᵐ ω ∂P, p ω) (Gcatalog : Set Ω) (hGmeas : MeasurableSet Gcatalog) (hGfull : P Gcatalogᶜ = 0) : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ G ⊆ Gcatalog ∧ ∀ ω ∈ G, p ω := by
  rw [ae_iff] at hp
  obtain ⟨B, hsub, hBmeas, hB0⟩ := exists_measurable_superset_of_null hp
  refine ⟨Bᶜ ∩ Gcatalog, hBmeas.compl.inter hGmeas, ?_, Set.inter_subset_right, ?_⟩
  · rw [Set.compl_inter, compl_compl]
    exact measure_union_null hB0 hGfull
  · intro ω hω
    rw [Set.mem_inter_iff] at hω
    by_contra hp'
    exact hω.1 (hsub hp')

/-- Finite dual energies on D(E) (`mfd:thm-C0`). -/
theorem aux_thm_C0_energy_coe_toReal {d : ℕ} {Q : Opens (SpatialCoordinates d)} (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) (hu : u ∈ limitFormDomain G) : (((limitFormEnergy G u).toReal : ℝ) : EReal) = limitFormEnergy G u ∧ 0 ≤ (limitFormEnergy G u).toReal := by
  have htop : limitFormEnergy G u < (⊤ : EReal) := by
    simpa [limitFormDomain] using hu
  have h0 := limitFormEnergy_nonneg G u
  have hbot : limitFormEnergy G u ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero h0)
  exact ⟨EReal.coe_toReal htop.ne hbot, EReal.toReal_nonneg h0⟩

/-- `mfd:thm-C0`: the comparison with C = 2 Cstar^2 A^2 persists for any larger C0 (used to get 1 ≤ C0 := max 1 C). -/
theorem aux_thm_C0_widen_constant (C C0 e f : ℝ) (hC : 0 < C) (hCC0 : C ≤ C0) (he : 0 ≤ e) (h1 : C⁻¹ * e ≤ f) (h2 : f ≤ C * e) : C0⁻¹ * e ≤ f ∧ f ≤ C0 * e := by
  have hinv : C0⁻¹ ≤ C⁻¹ := inv_anti₀ hC hCC0
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_right hinv he) h1
  · exact le_trans h2 (mul_le_mul_of_nonneg_right hCC0 he)

theorem aux_thm_C0_symm_nonneg_of_tendsto
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hlim : Tendsto GN atTop (𝓝 G))
    (hsym : ∀ n (x y : DomainL2 Q), inner ℝ (GN n x) y = inner ℝ x (GN n y))
    (hpos : ∀ n (x : DomainL2 Q), 0 ≤ inner ℝ x (GN n x)) :
    (∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) := by
  have h_apply_tendsto (x : DomainL2 Q) : Tendsto (fun n => GN n x) atTop (𝓝 (G x)) := by
    have h0 : Tendsto (fun n => GN n - G) atTop (𝓝 0) := by
      have h := hlim.sub (tendsto_const_nhds (x := G))
      rwa [sub_self] at h
    have h_norm : Tendsto (fun n => ‖GN n - G‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds] at h0 ⊢
      simp only [dist_eq_norm, sub_zero, norm_norm] at h0 ⊢
      exact h0
    have h_bound : ∀ n, ‖(GN n - G) x‖ ≤ ‖GN n - G‖ * ‖x‖ := fun n => (GN n - G).le_opNorm x
    have h_zero : Tendsto (fun n => (GN n - G) x) atTop (𝓝 0) := by
      apply squeeze_zero_norm' (Eventually.of_forall h_bound)
      have h := h_norm.mul_const ‖x‖
      rwa [zero_mul] at h
    have h := h_zero.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => G x) atTop (𝓝 (G x)))
    rw [zero_add] at h
    simpa only [sub_apply, sub_add_cancel] using h
  have h_symm : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y) := by
    intro x y
    have hL : Tendsto (fun n => inner ℝ (GN n x) y) atTop (𝓝 (inner ℝ (G x) y)) :=
      (continuous_inner.tendsto _).comp
        ((h_apply_tendsto x).prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop _))
    have hR : Tendsto (fun n => inner ℝ x (GN n y)) atTop (𝓝 (inner ℝ x (G y))) :=
      (continuous_inner.tendsto _).comp
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop _).prodMk_nhds (h_apply_tendsto y))
    have hEq : (fun n => inner ℝ (GN n x) y) = (fun n => inner ℝ x (GN n y)) :=
      funext fun n => hsym n x y
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR
  have h_nonneg : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x) := by
    intro x
    have h_tendsto : Tendsto (fun n => inner ℝ (GN n x) x) atTop (𝓝 (inner ℝ (G x) x)) :=
      (continuous_inner (𝕜 := ℝ) (E := DomainL2 Q)).tendsto (G x, x) |>.comp
        ((h_apply_tendsto x).prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop _))
    have h_nonneg' : ∀ n, 0 ≤ inner ℝ (GN n x) x := fun n => by
      rw [real_inner_comm]; exact hpos n x
    have h_nonneg'' : 0 ≤ inner ℝ (G x) x := ge_of_tendsto h_tendsto (Eventually.of_forall h_nonneg')
    rw [real_inner_comm]; exact h_nonneg''
  exact ⟨h_symm, h_nonneg⟩

theorem aux_thm_C0_energy_smul_apply
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) (s : ℝ) (f : DomainL2 Q) :
    limitFormEnergy G (s • G f) = ((s ^ 2 * inner ℝ f (G f) : ℝ) : EReal) := by
  have hkey : ∀ g : DomainL2 Q, ((2 * inner ℝ g (s • G f) - inner ℝ g (G g) : ℝ) : EReal) ≤
      ((s ^ 2 * inner ℝ f (G f) : ℝ) : EReal) := by
    intro g
    have e2 : inner ℝ g (s • G f) = s * inner ℝ g (G f) := by
      simp [inner_smul_right]
    have hcalc : (2 * inner ℝ g (s • G f) - inner ℝ g (G g) : ℝ) =
        (s ^ 2 * inner ℝ f (G f) : ℝ) - inner ℝ (g - s • f) (G (g - s • f)) := by
      have h_expand : inner ℝ (g - s • f) (G (g - s • f)) =
          inner ℝ g (G g) - 2 * s * inner ℝ g (G f) + s ^ 2 * inner ℝ f (G f) := by
        have e1 : G (g - s • f) = G g - s • G f := by
          simp [map_sub, map_smul]
        rw [e1, inner_sub_left, inner_sub_right, inner_sub_right]
        have hcomm : inner ℝ f (G g) = inner ℝ g (G f) := by
          rw [real_inner_comm]; exact hsym g f
        have e3 : inner ℝ (s • f) (G g) = s * inner ℝ g (G f) := by
          simp [inner_smul_left, hcomm]
        have e4 : inner ℝ (s • f) (s • G f) = s * (s * inner ℝ f (G f)) := by
          simp [inner_smul_left, inner_smul_right]
        rw [e2, e3, e4]
        ring
      rw [h_expand, e2]
      ring
    have h_nonneg : 0 ≤ inner ℝ (g - s • f) (G (g - s • f)) := hpos (g - s • f)
    rw [hcalc]
    have hle : ((s ^ 2 * inner ℝ f (G f) : ℝ) - inner ℝ (g - s • f) (G (g - s • f)) : ℝ) ≤
        (s ^ 2 * inner ℝ f (G f) : ℝ) := by
      linarith
    exact_mod_cast hle
  apply le_antisymm
  · rw [limitFormEnergy]
    exact ciSup_le hkey
  · have h_at_sf : (2 * inner ℝ (s • f) (s • G f) - inner ℝ (s • f) (G (s • f)) : ℝ) =
        (s ^ 2 * inner ℝ f (G f) : ℝ) := by
      have e1 : G (s • f) = s • G f := by simp [map_smul]
      have e2 : inner ℝ (s • f) (s • G f) = s * (s * inner ℝ f (G f)) := by
        simp [inner_smul_left, inner_smul_right]
      rw [e1, e2]
      ring
    have hmem : ((2 * inner ℝ (s • f) (s • G f) - inner ℝ (s • f) (G (s • f)) : ℝ) : EReal) ≤
        limitFormEnergy G (s • G f) := by
      rw [limitFormEnergy]
      exact le_iSup (fun (g : DomainL2 Q) =>
        ((2 * inner ℝ g (s • G f) - inner ℝ g (G g) : ℝ) : EReal)) (s • f)
    rw [h_at_sf] at hmem
    exact hmem

theorem aux_thm_C0_response_le_of_form_le
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsymE : ∀ x y : DomainL2 Q, inner ℝ (GE x) y = inner ℝ x (GE y))
    (hposE : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (GE x))
    (c : ℝ) (hc : 0 < c)
    (hdom : limitFormDomain GE ⊆ limitFormDomain GF)
    (hle : ∀ u ∈ limitFormDomain GE,
      (limitFormEnergy GF u).toReal ≤ c * (limitFormEnergy GE u).toReal)
    (f : DomainL2 Q) :
    inner ℝ f (GE f) ≤ c * inner ℝ f (GF f) := by
  have h_energy_eq : limitFormEnergy GE (GE f) = (inner ℝ f (GE f) : EReal) := by
    have := aux_thm_C0_energy_smul_apply GE hsymE hposE 1 f
    simpa [one_smul] using this
  have hGE_in_dom : GE f ∈ limitFormDomain GE := by
    rw [limitFormDomain, mem_ofPred_eq]
    rw [h_energy_eq]
    exact EReal.coe_lt_top _
  have h_ineq1 : (limitFormEnergy GF (GE f)).toReal ≤ c * inner ℝ f (GE f) := by
    have htemp := hle (GE f) hGE_in_dom
    rw [h_energy_eq] at htemp
    simpa [EReal.toReal_coe] using htemp
  have heq : (2 * inner ℝ (c • f) (GE f) - inner ℝ (c • f) (GF (c • f)) : ℝ) =
      2 * c * inner ℝ f (GE f) - c ^ 2 * inner ℝ f (GF f) := by
    rw [map_smul]
    simp [inner_smul_left, inner_smul_right]
    ring
  have h_lower : ((2 * c * inner ℝ f (GE f) - c ^ 2 * inner ℝ f (GF f) : ℝ) : EReal) ≤
      limitFormEnergy GF (GE f) := by
    rw [← heq, limitFormEnergy]
    exact le_iSup (fun (g : DomainL2 Q) =>
      ((2 * inner ℝ g (GE f) - inner ℝ g (GF g) : ℝ) : EReal)) (c • f)
  have h_nonbot : ((2 * c * inner ℝ f (GE f) - c ^ 2 * inner ℝ f (GF f) : ℝ) : EReal) ≠ ⊥ :=
    EReal.coe_ne_bot _
  have h_nottop : limitFormEnergy GF (GE f) ≠ ⊤ := by
    have hGE_in_domF : GE f ∈ limitFormDomain GF := hdom hGE_in_dom
    rw [limitFormDomain, mem_ofPred_eq] at hGE_in_domF
    exact ne_of_lt hGE_in_domF
  have h_ineq2 : (2 * c * inner ℝ f (GE f) - c ^ 2 * inner ℝ f (GF f) : ℝ) ≤
      (limitFormEnergy GF (GE f)).toReal :=
    EReal.toReal_le_toReal h_lower h_nonbot h_nottop
  have hfin : c * inner ℝ f (GE f) ≤ c * (c * inner ℝ f (GF f)) := by nlinarith [h_ineq1, h_ineq2]
  exact le_of_mul_le_mul_left hfin hc

/-- Consumer B (rebuilt for the envE/envF joint form): both jointly extracted
candidates are a.s. symmetric and nonnegative on every killed cube. Unlike the
older single-field version, the defining identity for `GNE`/`GNF` only holds
`∀ᵐ ω`, so the proof works inside the `filter_upwards` block rather than
globally. -/
theorem aux_thm_C0_candidates_symm_nonneg
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hGNdef : ∀ᵐ omega ∂P, ∀ i n f,
      GNE i n omega f =
        (responseSolution (S i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
          ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
      GNF i n omega f =
        (responseSolution (S i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
          ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1)
    (hconv : ∀ᵐ omega ∂P, ∀ i,
      Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
      Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) :
    ∀ᵐ ω ∂P, ∀ i : ℕ,
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GE i ω x) y = inner ℝ x (GE i ω y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)), 0 ≤ inner ℝ x (GE i ω x))) ∧
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GF i ω x) y = inner ℝ x (GF i ω y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)), 0 ≤ inner ℝ x (GF i ω x))) := by
  filter_upwards [hGNdef, hconv] with ω hGNω hconvω i
  have hsymNE : ∀ n (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GNE i n ω x) y = inner ℝ x (GNE i n ω y) := by
    intro n x y
    rw [(hGNω i n x).1, (hGNω i n y).1, real_inner_comm]
    exact volumeResponse_pairing_symm _ _ y x
  have hposNE : ∀ n (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      0 ≤ inner ℝ x (GNE i n ω x) := by
    intro n x
    rw [(hGNω i n x).1]
    exact volumeResponse_pairing_nonneg _ _ x
  have hsymNF : ∀ n (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GNF i n ω x) y = inner ℝ x (GNF i n ω y) := by
    intro n x y
    rw [(hGNω i n x).2, (hGNω i n y).2, real_inner_comm]
    exact volumeResponse_pairing_symm _ _ y x
  have hposNF : ∀ n (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      0 ≤ inner ℝ x (GNF i n ω x) := by
    intro n x
    rw [(hGNω i n x).2]
    exact volumeResponse_pairing_nonneg _ _ x
  exact ⟨aux_thm_C0_symm_nonneg_of_tendsto _ _ (hconvω i).1 hsymNE hposNE,
    aux_thm_C0_symm_nonneg_of_tendsto _ _ (hconvω i).2 hsymNF hposNF⟩

/-- Consumer A (`mfd:thm-C0`): the density-exclusion argument. From the two
applications of the positive-density comparison (prop_density, and its E/F swap),
a positive-probability bounded-response event for one fixed source excludes both
extreme ratio sets, and the middle set yields the two-sided comparison with
`C0 = 2 Cstar^2 A^2`. -/
theorem aux_thm_C0_comparison_core
    {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : ℕ → Opens (SpatialCoordinates d))
    (GE GF : (i : ℕ) → Ω → DomainL2 (Q i) →L[ℝ] DomainL2 (Q i))
    (hsymE : ∀ᵐ ω ∂P, ∀ i (x y : DomainL2 (Q i)), inner ℝ (GE i ω x) y = inner ℝ x (GE i ω y))
    (hposE : ∀ᵐ ω ∂P, ∀ i (x : DomainL2 (Q i)), 0 ≤ inner ℝ x (GE i ω x))
    (hsymF : ∀ᵐ ω ∂P, ∀ i (x y : DomainL2 (Q i)), inner ℝ (GF i ω x) y = inner ℝ x (GF i ω y))
    (hposF : ∀ᵐ ω ∂P, ∀ i (x : DomainL2 (Q i)), 0 ≤ inner ℝ x (GF i ω x))
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (Cstar : ℝ) (hCstar : 0 < Cstar)
    (ratio : ℕ → ℝ) (_hratio : ∀ n, 0 < ratio n)
    (hEF : ∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity Sset →
      (∀ n, Sset n → ratio n ≤ a) →
      ∀ᵐ ω ∂P, ∀ i : ℕ,
        limitFormDomain (GE i ω) ⊆ limitFormDomain (GF i ω) ∧
        ∀ u : DomainL2 (Q i), u ∈ limitFormDomain (GE i ω) →
          (limitFormEnergy (GF i ω) u).toReal ≤
            Cstar * a * (limitFormEnergy (GE i ω) u).toReal)
    (hFE : ∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity Sset →
      (∀ n, Sset n → (ratio n)⁻¹ ≤ a) →
      ∀ᵐ ω ∂P, ∀ i : ℕ,
        limitFormDomain (GF i ω) ⊆ limitFormDomain (GE i ω) ∧
        ∀ u : DomainL2 (Q i), u ∈ limitFormDomain (GF i ω) →
          (limitFormEnergy (GE i ω) u).toReal ≤
            Cstar * a * (limitFormEnergy (GF i ω) u).toReal)
    (i0 : ℕ) (f0 : DomainL2 (Q i0)) (A : ℝ) (hA : 1 ≤ A)
    (hmom : P {ω | A⁻¹ ≤ inner ℝ f0 (GE i0 ω f0) ∧ inner ℝ f0 (GE i0 ω f0) ≤ A ∧
      A⁻¹ ≤ inner ℝ f0 (GF i0 ω f0) ∧ inner ℝ f0 (GF i0 ω f0) ≤ A} ≠ 0) :
    ∀ᵐ ω ∂P, ∀ i : ℕ,
      limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
      ∀ u : DomainL2 (Q i), u ∈ limitFormDomain (GE i ω) →
        (2 * Cstar ^ 2 * A ^ 2)⁻¹ * (limitFormEnergy (GE i ω) u).toReal ≤
          (limitFormEnergy (GF i ω) u).toReal ∧
        (limitFormEnergy (GF i ω) u).toReal ≤
          (2 * Cstar ^ 2 * A ^ 2) * (limitFormEnergy (GE i ω) u).toReal := by
  classical
  have hA0 : 0 < A := by linarith
  set a0 : ℝ := (2 * Cstar * A ^ 2)⁻¹ with ha0_def
  have ha0 : 0 < a0 := by positivity
  have hc : Cstar * a0 = (2 * A ^ 2)⁻¹ := by
    rw [ha0_def]
    field_simp
  have hhalf : (2 * A ^ 2)⁻¹ * A < A⁻¹ := by
    have h1 : (2 * A ^ 2)⁻¹ * A = A⁻¹ / 2 := by
      field_simp
    rw [h1]
    have : 0 < A⁻¹ := inv_pos.2 hA0
    linarith
  have hcontra : ∀ X Y : Ω → ℝ, (∀ᵐ ω ∂P, X ω ≤ (2 * A ^ 2)⁻¹ * Y ω) →
      (∀ ω, (A⁻¹ ≤ inner ℝ f0 (GE i0 ω f0) ∧ inner ℝ f0 (GE i0 ω f0) ≤ A ∧
        A⁻¹ ≤ inner ℝ f0 (GF i0 ω f0) ∧ inner ℝ f0 (GF i0 ω f0) ≤ A) →
          A⁻¹ ≤ X ω ∧ Y ω ≤ A) → False := by
    intro X Y hXY hev
    apply hmom
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hXY] with ω hω hmem
    obtain ⟨h1, h2⟩ := hev ω hmem
    have h3 : (2 * A ^ 2)⁻¹ * Y ω ≤ (2 * A ^ 2)⁻¹ * A :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hlow : _root_.SubdiffusiveProcess.ResponseMoments.upperDensity (fun n => ratio n ≤ a0) < eta0 := by
    by_contra hge
    push Not at hge
    have hcmp := hEF _ a0 ha0 hge (fun n hn => hn)
    refine hcontra (fun ω => inner ℝ f0 (GE i0 ω f0)) (fun ω => inner ℝ f0 (GF i0 ω f0))
      ?_ (fun ω h => ⟨h.1, h.2.2.2⟩)
    filter_upwards [hcmp, hsymE, hposE] with ω hω hs hp
    have key := aux_thm_C0_response_le_of_form_le (GE i0 ω) (GF i0 ω) (hs i0) (hp i0)
      (Cstar * a0) (by positivity) (hω i0).1 (hω i0).2 f0
    rwa [hc] at key
  have hhigh : _root_.SubdiffusiveProcess.ResponseMoments.upperDensity (fun n => a0⁻¹ ≤ ratio n) < eta0 := by
    by_contra hge
    push Not at hge
    have hcmp := hFE _ a0 ha0 hge (fun n hn => by
      calc (ratio n)⁻¹ ≤ (a0⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 ha0) hn
        _ = a0 := inv_inv a0)
    refine hcontra (fun ω => inner ℝ f0 (GF i0 ω f0)) (fun ω => inner ℝ f0 (GE i0 ω f0))
      ?_ (fun ω h => ⟨h.2.2.1, h.2.1⟩)
    filter_upwards [hcmp, hsymF, hposF] with ω hω hs hp
    have key := aux_thm_C0_response_le_of_form_le (GF i0 ω) (GE i0 ω) (hs i0) (hp i0)
      (Cstar * a0) (by positivity) (hω i0).1 (hω i0).2 f0
    rwa [hc] at key
  have hmid : eta0 ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity (fun n => ratio n ≤ a0⁻¹ ∧ (ratio n)⁻¹ ≤ a0⁻¹) :=
    _root_.SubdiffusiveProcess.ResponseMoments.le_upperDensity_of_compl _ _ _ eta0 heta0 heta03 hlow hhigh (fun n h1 h2 => by
      push Not at h1 h2
      exact ⟨h2.le, inv_anti₀ ha0 h1.le⟩)
  have hE := hEF _ a0⁻¹ (inv_pos.2 ha0) hmid (fun n hn => hn.1)
  have hF := hFE _ a0⁻¹ (inv_pos.2 ha0) hmid (fun n hn => hn.2)
  have hC : Cstar * a0⁻¹ = 2 * Cstar ^ 2 * A ^ 2 := by
    rw [ha0_def, inv_inv]
    ring
  have hC0 : 0 < 2 * Cstar ^ 2 * A ^ 2 := by positivity
  filter_upwards [hE, hF] with ω hωE hωF i
  obtain ⟨hdEF, hleF⟩ := hωE i
  obtain ⟨hdFE, hleE⟩ := hωF i
  refine ⟨Set.Subset.antisymm hdEF hdFE, fun u hu => ⟨?_, ?_⟩⟩
  · have h1 := hleE u (hdEF hu)
    rw [hC] at h1
    rw [inv_mul_le_iff₀ hC0]
    exact h1
  · have h2 := hleF u hu
    rwa [hC] at h2

/-- Generic assembly (rebuilt for the envE/envF joint form; `mfd:thm-C0`): an almost-sure two-sided comparison with constant `C`, together
with the almost-sure operator limits of the two SEPARATE cutoff families
`GNE`/`GNF` (rather than one `GN` family sampled along `NE`/`NF`), is carried
by one measurable full event inside `Gcatalog`, with any larger constant `C0`. -/
theorem aux_thm_C0_assemble
    {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : ℕ → Opens (SpatialCoordinates d))
    (GNE GNF : (i : ℕ) → ℕ → Ω → DomainL2 (Q i) →L[ℝ] DomainL2 (Q i))
    (GE GF : (i : ℕ) → Ω → DomainL2 (Q i) →L[ℝ] DomainL2 (Q i))
    (Gcatalog : Set Ω) (hGmeas : MeasurableSet Gcatalog) (hGfull : P Gcatalogᶜ = 0)
    (hconv : ∀ᵐ ω ∂P, ∀ i,
      Tendsto (fun n => GNE i n ω) atTop (𝓝 (GE i ω)) ∧
      Tendsto (fun n => GNF i n ω) atTop (𝓝 (GF i ω)))
    (C C0 : ℝ) (hC : 0 < C) (hCC0 : C ≤ C0)
    (hcore : ∀ᵐ ω ∂P, ∀ i : ℕ,
      limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
      ∀ u : DomainL2 (Q i), u ∈ limitFormDomain (GE i ω) →
        C⁻¹ * (limitFormEnergy (GE i ω) u).toReal ≤ (limitFormEnergy (GF i ω) u).toReal ∧
        (limitFormEnergy (GF i ω) u).toReal ≤ C * (limitFormEnergy (GE i ω) u).toReal) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ G ⊆ Gcatalog ∧
      ∀ omega ∈ G, ∀ i : ℕ,
        Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
        Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega)) ∧
        limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
        ∀ u : DomainL2 (Q i), u ∈ limitFormDomain (GE i omega) →
          C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
            (limitFormEnergy (GF i omega) u).toReal ∧
          (limitFormEnergy (GF i omega) u).toReal ≤
            C0 * (limitFormEnergy (GE i omega) u).toReal := by
  have hae : ∀ᵐ ω ∂P, ∀ i : ℕ,
      (Tendsto (fun n => GNE i n ω) atTop (𝓝 (GE i ω)) ∧
        Tendsto (fun n => GNF i n ω) atTop (𝓝 (GF i ω))) ∧
      (limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
        ∀ u : DomainL2 (Q i), u ∈ limitFormDomain (GE i ω) →
          C⁻¹ * (limitFormEnergy (GE i ω) u).toReal ≤ (limitFormEnergy (GF i ω) u).toReal ∧
          (limitFormEnergy (GF i ω) u).toReal ≤ C * (limitFormEnergy (GE i ω) u).toReal) := by
    filter_upwards [hconv, hcore] with ω h1 h2 i
    exact ⟨h1 i, h2 i⟩
  obtain ⟨G, hGm, hG0, hGsub, hG⟩ :=
    aux_thm_C0_common_event P _ hae Gcatalog hGmeas hGfull
  refine ⟨G, hGm, hG0, hGsub, fun omega homega i => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hG omega homega i
  refine ⟨h1, h2, h3, fun u hu => ?_⟩
  obtain ⟨h5, h6⟩ := h4 u hu
  exact aux_thm_C0_widen_constant C C0 _ _ hC hCC0
    (aux_thm_C0_energy_coe_toReal (GE i omega) u hu).2 h5 h6



def aux_thm_C0_JointHyp_old
    (d : ℕ) (hd : 2 ≤ d) (alpha eta : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (S i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext beta t : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey))
/-- Legacy form of `aux_thm_C0_JointHypU` (existential `beta t`). -/
def aux_thm_C0_JointHypU_old
    (d : ℕ) (hd : 2 ≤ d) (alpha eta : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (_hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (S i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext beta t : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey))

/-- The joint-extraction hypothesis package of `thm_C0` (verbatim the premise of the frozen
header, also the premise of `prop_density`), wrapped as a definition so that auxiliary
statements stay small. -/
def aux_thm_C0_JointHyp
    (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (S i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey))
/-- Variant of `aux_thm_C0_JointHyp` with the unit cube inside the catalogue root; formerly the package of `thm_C0` (verbatim the premise of the frozen
header, also the premise of `prop_density`), wrapped as a definition so that auxiliary
statements stay small. -/
def aux_thm_C0_JointHypU
    (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (_hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (S i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey))


/-- The package with explicit `beta t` implies the legacy package with existential `beta t`. -/
theorem aux_thm_C0_JointHyp_old_of_new
    (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (h : aux_thm_C0_JointHyp d hd alpha eta beta t model H Ω P field envE envF catalogResponse catalogConstant responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF) :
    aux_thm_C0_JointHyp_old d hd alpha eta model H Ω P field envE envF catalogResponse catalogConstant responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, root, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hEF⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, root, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, beta, t, I, coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hEF⟩

/-- The package with explicit `beta t` implies the legacy package with existential `beta t`. -/
theorem aux_thm_C0_JointHypU_old_of_new
    (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (h : aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field envE envF catalogResponse catalogConstant responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF) :
    aux_thm_C0_JointHypU_old d hd alpha eta model H Ω P field envE envF catalogResponse catalogConstant responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hEF⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, beta, t, I, coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hEF⟩

/-- Carried input (manuscript M: positivity of killed inverse responses;
coarse coercivity (positive moments via the energy identity); boundary
extension and crude grid bounds (negative moments via the mesh test); the
deterministic bound uniform over labels and over the disorder interval): a fixed source on
the unit cube whose killed inverse response at every cutoff is positive and has first
positive and negative moments bounded by one constant `C`, chosen together with `delta0`
before the model. -/
def aux_thm_C0_unitResponseMoments (d : ℕ) : Prop :=
  ∃ delta0 C : ℝ, 0 < delta0 ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
    ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization model H →
    ∀ (S : ResponseSpace (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
      S.space = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) →
    ∃ f0 : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ∀ N : ℕ,
        (∀ om : BilateralField d, 0 < inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N 0 one_pos)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL)) ∧
        MemLp (fun om : BilateralField d => inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N 0 one_pos)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om : BilateralField d => inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N 0 one_pos)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal C ∧
        MemLp (fun om : BilateralField d => (inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N 0 one_pos)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om : BilateralField d => (inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N 0 one_pos)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal C

/-- The input transported to any cube equal to the unit cube (for catalogue indices). -/
theorem aux_thm_C0_unitResponseMoments_at {d : ℕ} (hin : aux_thm_C0_unitResponseMoments d) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
    ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization model H →
    ∀ (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0), z0 = 0 → r0 = 1 →
    ∀ (S : ResponseSpace (centeredCube z0 r0 hr0)),
      S.space = killedSobolevGraph (centeredCube z0 r0 hr0) →
    ∃ f0 : DomainL2 (centeredCube z0 r0 hr0),
      ∀ N : ℕ,
        (∀ om : BilateralField d, 0 < inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL)) ∧
        MemLp (fun om : BilateralField d => inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om : BilateralField d => inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal C ∧
        MemLp (fun om : BilateralField d => (inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om : BilateralField d => (inverseResponse S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal C := by
  obtain ⟨delta0, C, hdelta0, hmain⟩ := hin
  refine ⟨delta0, C, hdelta0, ?_⟩
  intro _ _ model hmodel H hH z0 r0 hr0 hz0 hr1 S hS
  subst hz0
  subst hr1
  exact hmain model hmodel H hH S hS

/-- The volume pairing of the weak solution is the inverse response. -/
theorem aux_thm_C0_pairing_eq_inverseResponse
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : PositiveCoefficient Q) (f : DomainL2 Q) :
    inner ℝ f (responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 =
      inverseResponse S a ((sobolevVolumeLoad f).comp S.space.subtypeL) := by
  rw [inverseResponse_eq_load]
  rfl

/-- Markov with a first-moment bound: `μ {A < Y} ≤ 1/8` once `8 C ≤ A`. -/
theorem aux_thm_C0_markov_eighth {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (Y : α → ℝ) (C A : ℝ) (hA : 0 < A) (hCA : 8 * C ≤ A)
    (_hY : MemLp Y 1 μ) (hbound : eLpNorm Y 1 μ ≤ ENNReal.ofReal C) :
    μ {x | A < Y x} ≤ 1 / 8 := by
  have hA0 : ENNReal.ofReal A ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hA
  have hmk := meas_ge_le_mul_pow_eLpNorm_enorm (f := Y) μ one_ne_zero ENNReal.one_ne_top
    hA0 (fun h => absurd h ENNReal.ofReal_ne_top)
  simp only [ENNReal.toReal_one, ENNReal.rpow_one] at hmk
  have hsub : {x | A < Y x} ⊆ {x | ENNReal.ofReal A ≤ ‖Y x‖ₑ} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_trans hx.le (le_abs_self _))
  calc μ {x | A < Y x} ≤ μ {x | ENNReal.ofReal A ≤ ‖Y x‖ₑ} := measure_mono hsub
    _ ≤ (ENNReal.ofReal A)⁻¹ * eLpNorm Y 1 μ := hmk
    _ ≤ (ENNReal.ofReal A)⁻¹ * ENNReal.ofReal C := by gcongr
    _ = ENNReal.ofReal (C / A) := by
      rw [ENNReal.ofReal_div_of_pos hA, div_eq_mul_inv, mul_comm]
    _ ≤ ENNReal.ofReal (1 / 8) := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ hA]
      linarith
    _ = 1 / 8 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)]
      simp

/-- Tails pass to almost-sure limits through open sets, without measurability. -/
theorem aux_thm_C0_limit_open_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (Yn : ℕ → Ω → ℝ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Yn n ω) atTop (𝓝 (X ω)))
    (U : Set ℝ) (hU : IsOpen U) (b : ℝ≥0∞) (hb : ∀ n, P {ω | Yn n ω ∈ U} ≤ b) :
    P {ω | X ω ∈ U} ≤ b := by
  let T : ℕ → Set Ω := fun m => ⋂ n ∈ Set.Ici m, {ω | Yn n ω ∈ U}
  have hmono : Monotone T := by
    intro m m' hmm' ω hω
    simp only [T, Set.mem_iInter, Set.mem_Ici] at hω ⊢
    exact fun n hn => hω n (le_trans hmm' hn)
  have hae : {ω | X ω ∈ U} ≤ᵐ[P] (⋃ m, T m : Set Ω) := by
    filter_upwards [hconv] with ω hω hX
    have hX' : X ω ∈ U := hX
    have hev : ∀ᶠ n in atTop, Yn n ω ∈ U := hω (hU.mem_nhds hX')
    obtain ⟨m, hm⟩ := eventually_atTop.1 hev
    change ω ∈ ⋃ m, T m
    rw [Set.mem_iUnion]
    refine ⟨m, ?_⟩
    simp only [T, Set.mem_iInter, Set.mem_Ici]
    exact fun n hn => hm n hn
  calc P {ω | X ω ∈ U} ≤ P (⋃ m, T m) := measure_mono_ae hae
    _ = ⨆ m, P (T m) := hmono.measure_iUnion
    _ ≤ b := by
      refine iSup_le fun m => le_trans (measure_mono ?_) (hb m)
      intro ω hω
      simp only [T, Set.mem_iInter, Set.mem_Ici] at hω
      exact hω m le_rfl

/-- `mfd:thm-C0`: choosing A with each of the four tail probabilities < 1/8 gives P[A^{-1} ≤ Y_E, Y_F ≤ A] > 0 without independence. -/
theorem aux_thm_C0_pos_of_tails {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (A : ℝ) (hXlo : P {ω | X ω < A⁻¹} ≤ 1 / 8) (hXhi : P {ω | A < X ω} ≤ 1 / 8) (hYlo : P {ω | Y ω < A⁻¹} ≤ 1 / 8) (hYhi : P {ω | A < Y ω} ≤ 1 / 8) : P {ω | A⁻¹ ≤ X ω ∧ X ω ≤ A ∧ A⁻¹ ≤ Y ω ∧ Y ω ≤ A} ≠ 0 := by
  intro h0
  have hcover : ({ω | A⁻¹ ≤ X ω ∧ X ω ≤ A ∧ A⁻¹ ≤ Y ω ∧ Y ω ≤ A} : Set Ω)ᶜ ⊆
      {ω | X ω < A⁻¹} ∪ {ω | A < X ω} ∪ {ω | Y ω < A⁻¹} ∪ {ω | A < Y ω} := by
    intro ω hω
    simp only [Set.mem_compl_iff, mem_ofPred_eq, Set.mem_union, not_and_or, not_le] at hω ⊢
    tauto
  have hcomp : P ({ω | A⁻¹ ≤ X ω ∧ X ω ≤ A ∧ A⁻¹ ≤ Y ω ∧ Y ω ≤ A} : Set Ω)ᶜ
      ≤ (1 : ℝ≥0∞) / 8 + 1 / 8 + 1 / 8 + 1 / 8 := by
    calc P ({ω | A⁻¹ ≤ X ω ∧ X ω ≤ A ∧ A⁻¹ ≤ Y ω ∧ Y ω ≤ A} : Set Ω)ᶜ
        ≤ P ({ω | X ω < A⁻¹} ∪ {ω | A < X ω} ∪ {ω | Y ω < A⁻¹} ∪ {ω | A < Y ω}) :=
          measure_mono hcover
      _ ≤ P ({ω | X ω < A⁻¹} ∪ {ω | A < X ω} ∪ {ω | Y ω < A⁻¹}) + P {ω | A < Y ω} :=
          measure_union_le _ _
      _ ≤ (P ({ω | X ω < A⁻¹} ∪ {ω | A < X ω}) + P {ω | Y ω < A⁻¹}) + P {ω | A < Y ω} :=
          add_le_add (measure_union_le _ _) (le_refl _)
      _ ≤ ((P {ω | X ω < A⁻¹} + P {ω | A < X ω}) + P {ω | Y ω < A⁻¹}) + P {ω | A < Y ω} :=
          add_le_add (add_le_add (measure_union_le _ _) (le_refl _)) (le_refl _)
      _ ≤ (((1 : ℝ≥0∞) / 8 + 1 / 8) + 1 / 8) + 1 / 8 :=
          add_le_add (add_le_add (add_le_add hXlo hXhi) hYlo) hYhi
  have hle : (1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞) / 8 + 1 / 8 + 1 / 8 + 1 / 8 := by
    calc (1 : ℝ≥0∞) = P Set.univ := (measure_univ : P Set.univ = 1).symm
      _ = P ({ω | A⁻¹ ≤ X ω ∧ X ω ≤ A ∧ A⁻¹ ≤ Y ω ∧ Y ω ≤ A} ∪
              ({ω | A⁻¹ ≤ X ω ∧ X ω ≤ A ∧ A⁻¹ ≤ Y ω ∧ Y ω ≤ A} : Set Ω)ᶜ) := by
            rw [Set.union_compl_self]
      _ ≤ P ({ω | A⁻¹ ≤ X ω ∧ X ω ≤ A ∧ A⁻¹ ≤ Y ω ∧ Y ω ≤ A} : Set Ω) +
            P ({ω | A⁻¹ ≤ X ω ∧ X ω ≤ A ∧ A⁻¹ ≤ Y ω ∧ Y ω ≤ A} : Set Ω)ᶜ :=
          measure_union_le _ _
      _ ≤ 0 + ((1 : ℝ≥0∞) / 8 + 1 / 8 + 1 / 8 + 1 / 8) :=
          add_le_add (le_of_eq h0) hcomp
      _ = (1 : ℝ≥0∞) / 8 + 1 / 8 + 1 / 8 + 1 / 8 := zero_add _
  have hlt : (1 : ℝ≥0∞) / 8 + 1 / 8 + 1 / 8 + 1 / 8 < 1 := by
    rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (8 : ℝ≥0∞) ≠ 0))
          (Or.inl (by norm_num : (8 : ℝ≥0∞) ≠ ⊤))]
    norm_num
  exact absurd hlt (not_lt.mpr hle)

/-- On one cube: tails of the finite-cutoff inverse responses
(bounded through the laws of the represented environments) pass to the limiting responses,
and the four tails `≤ 1/8` give a positive-probability two-sided event. -/
theorem aux_thm_C0_cube_moment_event
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (envE envF : ℕ → Ω → BilateralField d)
    (hMP : ∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
      MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S0 : ResponseSpace (centeredCube z0 r0 hr0))
    (GNE GNF : ℕ → Ω → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (GE GF : Ω → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (NE NF : ℕ → ℕ)
    (hGNdef : ∀ᵐ omega ∂P, ∀ n f,
      GNE n omega f =
        (responseSolution S0
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) z0 hr0)
          ((sobolevVolumeLoad f).comp S0.space.subtypeL)).val.1 ∧
      GNF n omega f =
        (responseSolution S0
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) z0 hr0)
          ((sobolevVolumeLoad f).comp S0.space.subtypeL)).val.1)
    (hconv : ∀ᵐ omega ∂P,
      Tendsto (fun n => GNE n omega) atTop (𝓝 (GE omega)) ∧
      Tendsto (fun n => GNF n omega) atTop (𝓝 (GF omega)))
    (f0 : DomainL2 (centeredCube z0 r0 hr0)) (C A : ℝ) (hA : 0 < A) (hCA : 8 * C ≤ A)
    (hmom : ∀ N : ℕ,
        (∀ om : BilateralField d, 0 < inverseResponse S0
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S0.space.subtypeL)) ∧
        MemLp (fun om : BilateralField d => inverseResponse S0
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S0.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om : BilateralField d => inverseResponse S0
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S0.space.subtypeL)) 1 (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal C ∧
        MemLp (fun om : BilateralField d => (inverseResponse S0
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S0.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om : BilateralField d => (inverseResponse S0
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
          ((sobolevVolumeLoad f0).comp S0.space.subtypeL))⁻¹) 1 (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal C) :
    P {ω | A⁻¹ ≤ inner ℝ f0 (GE ω f0) ∧ inner ℝ f0 (GE ω f0) ≤ A ∧
      A⁻¹ ≤ inner ℝ f0 (GF ω f0) ∧ inner ℝ f0 (GF ω f0) ≤ A} ≠ 0 := by
  -- the finite-cutoff inverse response as a function of the environment
  set Y : ℕ → BilateralField d → ℝ := fun N om => inverseResponse S0
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z0 hr0)
    ((sobolevVolumeLoad f0).comp S0.space.subtypeL) with hYdef
  -- law bounds for one environment
  have hlaw : ∀ (e : Ω → BilateralField d), MeasurePreserving e P (chaosSampleLaw model).toMeasure →
      ∀ N, P {ω | Y N (e ω) ∈ Set.Ioi A} ≤ 1 / 8 ∧ P {ω | Y N (e ω) ∈ Set.Iio A⁻¹} ≤ 1 / 8 := by
    intro e he N
    obtain ⟨hpos, hm1, hb1, hm2, hb2⟩ := hmom N
    have hmap : ∀ s : Set (BilateralField d),
        P (e ⁻¹' s) ≤ (chaosSampleLaw model).toMeasure s := by
      intro s
      have h := Measure.le_map_apply (μ := P) he.measurable.aemeasurable s
      rwa [he.map_eq] at h
    constructor
    · calc P {ω | Y N (e ω) ∈ Set.Ioi A}
          = P (e ⁻¹' {om | A < Y N om}) := rfl
        _ ≤ (chaosSampleLaw model).toMeasure {om | A < Y N om} := hmap _
        _ ≤ 1 / 8 := aux_thm_C0_markov_eighth _ (Y N) C A hA hCA hm1 hb1
    · calc P {ω | Y N (e ω) ∈ Set.Iio A⁻¹}
          ≤ P (e ⁻¹' {om | A < (Y N om)⁻¹}) := by
            apply measure_mono
            intro ω hω
            simp only [mem_ofPred_eq, Set.mem_Iio, Set.mem_preimage] at hω ⊢
            exact (lt_inv_comm₀ hA (hpos (e ω))).2 hω
        _ ≤ (chaosSampleLaw model).toMeasure {om | A < (Y N om)⁻¹} := hmap _
        _ ≤ 1 / 8 := aux_thm_C0_markov_eighth _ (fun om => (Y N om)⁻¹) C A hA hCA hm2 hb2
  -- almost-sure convergence of the fixed-source pairings
  have hlimE : ∀ᵐ ω ∂P, Tendsto (fun n => Y (NE n) (envE n ω)) atTop
      (𝓝 (inner ℝ f0 (GE ω f0))) := by
    filter_upwards [hGNdef, hconv] with ω hdef hc
    have happ : Tendsto (fun n => GNE n ω f0) atTop (𝓝 (GE ω f0)) :=
      ((ContinuousLinearMap.apply ℝ (DomainL2 (centeredCube z0 r0 hr0)) f0).continuous.tendsto
        (GE ω)).comp hc.1
    have hin := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := f0)) happ
    refine hin.congr (fun n => ?_)
    show inner ℝ f0 (GNE n ω f0) = _
    rw [(hdef n f0).1]
    exact aux_thm_C0_pairing_eq_inverseResponse S0 _ f0
  have hlimF : ∀ᵐ ω ∂P, Tendsto (fun n => Y (NF n) (envF n ω)) atTop
      (𝓝 (inner ℝ f0 (GF ω f0))) := by
    filter_upwards [hGNdef, hconv] with ω hdef hc
    have happ : Tendsto (fun n => GNF n ω f0) atTop (𝓝 (GF ω f0)) :=
      ((ContinuousLinearMap.apply ℝ (DomainL2 (centeredCube z0 r0 hr0)) f0).continuous.tendsto
        (GF ω)).comp hc.2
    have hin := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := f0)) happ
    refine hin.congr (fun n => ?_)
    show inner ℝ f0 (GNF n ω f0) = _
    rw [(hdef n f0).2]
    exact aux_thm_C0_pairing_eq_inverseResponse S0 _ f0
  have hEhi := aux_thm_C0_limit_open_tail P _ _ hlimE (Set.Ioi A) isOpen_Ioi (1 / 8)
    (fun n => (hlaw (envE n) (hMP n).1 (NE n)).1)
  have hElo := aux_thm_C0_limit_open_tail P _ _ hlimE (Set.Iio A⁻¹) isOpen_Iio (1 / 8)
    (fun n => (hlaw (envE n) (hMP n).1 (NE n)).2)
  have hFhi := aux_thm_C0_limit_open_tail P _ _ hlimF (Set.Ioi A) isOpen_Ioi (1 / 8)
    (fun n => (hlaw (envF n) (hMP n).2 (NF n)).1)
  have hFlo := aux_thm_C0_limit_open_tail P _ _ hlimF (Set.Iio A⁻¹) isOpen_Iio (1 / 8)
    (fun n => (hlaw (envF n) (hMP n).2 (NF n)).2)
  exact aux_thm_C0_pos_of_tails P (fun ω => inner ℝ f0 (GE ω f0))
    (fun ω => inner ℝ f0 (GF ω f0)) A hElo hEhi hFlo hFhi




/-- The represented-sequence convention is stable under passing to a subsequence. -/
theorem aux_thm_C0_crs_reindex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*}
    (resp : ι → ℕ → Ω → ℝ) (respLim : ι → Ω → ℝ) (const : ι → ℕ → Ω → ℝ) (G : Set Ω)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (h : conv_represented_sequence P resp respLim const G) :
    conv_represented_sequence P (fun i N => resp i (s N)) respLim
      (fun i N => const i (s N)) G := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := h
  refine ⟨h1, h2, h3, fun i ω hω => (h4 i ω hω).comp hs.tendsto_atTop, ?_⟩
  · intro i ω hω
    obtain ⟨M, hM⟩ := h6 i ω hω
    exact ⟨M, fun N => hM (s N)⟩

/-- The represented estimates of one candidate are stable under passing to a subsequence of
the cutoffs, reindexing the environments, the source/cell solutions and the catalogue
responses and constants together. -/
theorem aux_thm_C0_cre_reindex
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (root : ℕ) (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (Dcat : ∀ i, Submodule ℚ (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcat : ∀ i, Countable (Dcat i)]
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (usrc : ∀ i, Dcat i → ℕ → Ω → (S i).space)
    (srcRep : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (Cext beta alpha eta t : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (response : ℕ → Ω → ℝ) (event : Set Ω)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (h : conv_represented_estimates d hd model H Ω P cutoff env
      ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
      usrc srcRep ucell Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (cutoff n) (env n omega)) response
      (fun i n omega => catalogConstant i (cutoff n) (env n omega)) event
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey) :
    conv_represented_estimates d hd model H Ω P (fun n => cutoff (s n)) (fun n => env (s n))
      ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
      (fun i g n => usrc i g (s n)) (fun i g n => srcRep i g (s n))
      (fun i h n => ucell i h (s n)) Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (cutoff (s n)) (env (s n) omega)) response
      (fun i n omega => catalogConstant i (cutoff (s n)) (env (s n) omega)) event
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey := by
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hB1, hB2, hB3, hB4, hB5, hC1, hC2, hC3, hC4, hC5, hC6,
    hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD8, hD9, hE1, hE2, hE3, hF, hG, hH, hI, hJ, hK, hL⟩ := h
  refine ⟨hA1, hA2, hA3, hA4, hA5, hB1.comp hs, hB2, fun n => hB3 (s n), fun n => hB4 (s n),
    aux_thm_C0_crs_reindex P _ _ _ _ s hs hB5, hC1, hC2, hC3, hC4, hC5, hC6,
    hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD8, hD9, fun i n => hE1 i (s n), ?_,
    fun i om hom n => hE3 i om hom (s n),
    fun j n om hom => hF j (s n) om hom, fun j n om hom => hG j (s n) om hom,
    fun j n om hom => hH j (s n) om hom, fun j n om hom => hI j (s n) om hom,
    fun g n k j om hom => hJ g (s n) k j om hom, fun j g n om hom => hK j g (s n) om hom,
    fun j h n om hom => hL j h (s n) om hom⟩
  intro i p hp
  obtain ⟨B, hB0, hB⟩ := hE2 i p hp
  exact ⟨B, hB0, fun n => hB (s n)⟩

/-- The joint hypothesis package passes to subsequences `sE`, `sF` of the two candidates; the
limits `GE`, `GF` are unchanged. -/
theorem aux_thm_C0_joint_reindex
    (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (sE sF : ℕ → ℕ) (hsE : StrictMono sE) (hsF : StrictMono sF)
    (h : aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field envE envF
      catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
      GNE GNF GE GF NE NF) :
    aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field
      (fun n => envE (sE n)) (fun n => envF (sF n))
      catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
      (fun i n => GNE i (sE n)) (fun i n => GNF i (sF n)) GE GF
      (fun n => NE (sE n)) (fun n => NF (sF n)) := by
  obtain ⟨hP, hMeasF, hMap, hInfra, hNEmono, hNFmono, hMP, hEnvTend, hSdef, hGNdef, hGconv,
    hCat⟩ := h
  obtain ⟨root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey,
    origin, gridRoot, gridKey, hCatE, hCatF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  refine ⟨hP, hMeasF, hMap, hInfra, hNEmono.comp hsE, hNFmono.comp hsF,
    fun n => ⟨(hMP (sE n)).1, (hMP (sF n)).2⟩,
    hEnvTend.mono fun ω h => ⟨h.1.comp hsE.tendsto_atTop, h.2.comp hsF.tendsto_atTop⟩,
    hSdef, hGNdef.mono fun ω h i n f => ⟨(h i (sE n) f).1, (h i (sF n) f).2⟩,
    hGconv.mono fun ω h i => ⟨(h i).1.comp hsE.tendsto_atTop, (h i).2.comp hsF.tendsto_atTop⟩,
    root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1,
    fun i g n => usrcE i g (sE n), fun i g n => usrcF i g (sF n),
    fun i g n => srcRepE i g (sE n), fun i g n => srcRepF i g (sF n),
    fun i h n => ucellE i h (sE n), fun i h n => ucellF i h (sF n),
    Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey,
    aux_thm_C0_cre_reindex d hd model H Ω P NE envE root z r hr S Dcat fcat trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t I catalogResponse catalogConstant responseE
      eventE coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey
      sE hsE hCatE,
    aux_thm_C0_cre_reindex d hd model H Ω P NF envF root z r hr S Dcat fcat trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t I catalogResponse catalogConstant responseF
      eventF coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey
      sF hsF hCatF⟩

/-- The joint hypothesis package is symmetric under exchanging the two candidates. -/
theorem aux_thm_C0_joint_swap
    (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (h : aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field envE envF
      catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
      GNE GNF GE GF NE NF) :
    aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field envF envE
      catalogResponse catalogConstant responseF responseE eventF eventE z r hr S
      GNF GNE GF GE NF NE := by
  obtain ⟨hP, hMeasF, hMap, hInfra, hNEmono, hNFmono, hMP, hEnvTend, hSdef, hGNdef, hGconv,
    hCat⟩ := h
  obtain ⟨root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey,
    origin, gridRoot, gridKey, hCatE, hCatF⟩ := hCat
  exact ⟨hP, hMeasF, hMap, hInfra, hNFmono, hNEmono,
    fun n => ⟨(hMP n).2, (hMP n).1⟩,
    hEnvTend.mono (fun omega h => ⟨h.2, h.1⟩), hSdef,
    hGNdef.mono (fun omega h => fun i n f => ⟨(h i n f).2, (h i n f).1⟩),
    hGconv.mono (fun omega h => fun i => ⟨(h i).2, (h i).1⟩),
    root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcF, usrcE, srcRepF, srcRepE, ucellF,
    ucellE, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey,
    origin, gridRoot, gridKey, hCatF, hCatE⟩

/-- The normalization `kappa_N = exp((N+1) tau^2) ahom_N` of `prop_density`. -/
def aux_thm_C0_kappa {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) : ℝ :=
  Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom model N

/-- `mfd:thm-C0`: the two positive-density comparisons consumed by
`aux_thm_C0_comparison_core`. The deterministic reference ratios are extracted along further
subsequences of `NE`, `NF` (`reference_coefficients`); `prop_density` is applied to the
correspondingly reindexed pair, whose limiting candidates `GE`, `GF` are the given ones, once
directly and once with the two candidates exchanged. -/
theorem aux_thm_C0_density_inputs
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Ddet : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha)
    (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8))
    (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
        ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
            (3 * (R / (3 : ℝ) ^ H1) / 2) ⊆
          (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
        Cd * ((3 : ℝ) ^ H1) ^ ((d : ℝ) - 1)) :
    ∃ delta0 Cstar : ℝ, 0 < delta0 ∧ 0 < Cstar ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (envE envF : ℕ → Ω → BilateralField d)
        (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
        (responseE responseF : ℕ → Ω → ℝ)
        (eventE eventF : Set Ω)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
      aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field envE envF
        catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
        GNE GNF GE GF NE NF →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr S GE GF NE NF →
      ∃ ratio : ℕ → ℝ, (∀ n, 0 < ratio n) ∧
        (∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity Sset →
          (∀ n, Sset n → ratio n ≤ a) →
          ∀ᵐ ω ∂P, ∀ i : ℕ,
            limitFormDomain (GE i ω) ⊆ limitFormDomain (GF i ω) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i ω) →
              (limitFormEnergy (GF i ω) u).toReal ≤
                Cstar * a * (limitFormEnergy (GE i ω) u).toReal) ∧
        (∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity Sset →
          (∀ n, Sset n → (ratio n)⁻¹ ≤ a) →
          ∀ᵐ ω ∂P, ∀ i : ℕ,
            limitFormDomain (GF i ω) ⊆ limitFormDomain (GE i ω) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GF i ω) →
              (limitFormEnergy (GE i ω) u).toReal ≤
                Cstar * a * (limitFormEnergy (GF i ω) u).toReal) := by
  obtain ⟨delta0, Cstar, hdelta0, hCstar, hrest⟩ :=
    prop_density d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp eta0 heta0 heta03 D theta alpha eta hD htheta htheta8 halpha
      halpha1 heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  refine ⟨delta0, Cstar, hdelta0, hCstar, ?_⟩
  intro _ _ model hmodel Rm Sreg It H Ω _ P _ field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF hjoint hBnd
  have hNEmono : StrictMono NE := hjoint.2.2.2.2.1
  have hNFmono : StrictMono NF := hjoint.2.2.2.2.2.1
  let lo : ℕ → ℝ := fun k => Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P))
  let hi : ℕ → ℝ := fun k => Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)
  have hlo : ∀ k, 0 < lo k := fun k => Real.exp_pos _
  have hlohi : ∀ k, lo k ≤ hi k := by
    intro k
    simp only [lo, hi, Real.exp_le_exp]
    exact neg_le_self (mul_nonneg (by positivity) model.G4.tauSq_pos.le)
  have hratio_bound : ∀ N k, k ≤ N →
      lo k ≤ aux_thm_C0_kappa model (N - k) / aux_thm_C0_kappa model N ∧
        aux_thm_C0_kappa model (N - k) / aux_thm_C0_kappa model N ≤ hi k :=
    fun N k hkn => aux_reference_coefficients_kappa_ratio_bounds d model
      (aux_thm_C0_kappa model) (fun _ => rfl) N k hkn
  obtain ⟨sE, hsE, eE, heE, hlimE⟩ :=
    aux_reference_coefficients_extract_bounded NE hNEmono
      (fun N k => aux_thm_C0_kappa model (N - k) / aux_thm_C0_kappa model N) lo hi hlo hlohi
      hratio_bound
  obtain ⟨sF, hsF, eF, heF, hlimF⟩ :=
    aux_reference_coefficients_extract_bounded NF hNFmono
      (fun N k => aux_thm_C0_kappa model (N - k) / aux_thm_C0_kappa model N) lo hi hlo hlohi
      hratio_bound
  have hj' := aux_thm_C0_joint_reindex d hd alpha eta beta t model H Ω P field envE envF
    catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
    GNE GNF GE GF NE NF sE sF hsE hsF hjoint
  have hsw := aux_thm_C0_joint_swap d hd alpha eta beta t model H Ω P field
    (fun n => envE (sE n)) (fun n => envF (sF n))
    catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
    (fun i n => GNE i (sE n)) (fun i n => GNF i (sF n)) GE GF
    (fun n => NE (sE n)) (fun n => NF (sF n)) hj'
  have hBnd' : aux_conv_represented_env_interface_bounds d hd model H Ω P (fun n => envE (sE n))
      (fun n => envF (sF n)) z r hr S GE GF (fun n => NE (sE n)) (fun n => NF (sF n)) :=
    hBnd.mono fun ω h i => ⟨represented_bounds_subseq d hd (z i) (r i) (hr i) (S i)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n ω) (NE n) (z i) (hr i)) (GE i ω)
      (h i).1 sE hsE.tendsto_atTop, represented_bounds_subseq d hd (z i) (r i) (hr i) (S i)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n ω) (NF n) (z i) (hr i)) (GF i ω)
      (h i).2 sF hsF.tendsto_atTop⟩
  have hBndsw : aux_conv_represented_env_interface_bounds d hd model H Ω P (fun n => envF (sF n))
      (fun n => envE (sE n)) z r hr S GF GE (fun n => NF (sF n)) (fun n => NE (sE n)) :=
    hBnd'.mono fun ω h i => ⟨(h i).2, (h i).1⟩
  refine ⟨fun n => eF (H1 * n) / eE (H1 * n), fun n => div_pos (heF _) (heE _), ?_, ?_⟩
  · intro Sset a ha hdens hle
    exact hrest model hmodel Rm Sreg It H Ω P field (fun n => envE (sE n)) (fun n => envF (sF n))
      catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
      (fun i n => GNE i (sE n)) (fun i n => GNF i (sF n)) GE GF
      (fun n => NE (sE n)) (fun n => NF (sF n)) hj' hBnd' eE eF (fun k => ⟨heE k, heF k⟩)
      hlimE hlimF Sset a ha hdens hle
  · intro Sset a ha hdens hle
    refine hrest model hmodel Rm Sreg It H Ω P field (fun n => envF (sF n)) (fun n => envE (sE n))
      catalogResponse catalogConstant responseF responseE eventF eventE z r hr S
      (fun i n => GNF i (sF n)) (fun i n => GNE i (sE n)) GF GE
      (fun n => NF (sF n)) (fun n => NE (sE n)) hsw hBndsw eF eE (fun k => ⟨heF k, heE k⟩)
      hlimF hlimE Sset a ha hdens (fun n hn => ?_)
    have h := hle n hn
    rwa [inv_div] at h


/-- Clause C (completeness) of the catalogue: if the root contains the unit cube, the unit cube
is a killed cube of the family. -/
theorem aux_thm_C0_unit_index
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (root : ℕ) (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (Dcat : ∀ i, Submodule ℚ (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcat : ∀ i, Countable (Dcat i)]
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (usrc : ∀ i, Dcat i → ℕ → Ω → (S i).space)
    (srcRep : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (Cext beta alpha eta t : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (resp : ℕ → ℕ → Ω → ℝ) (response : ℕ → Ω → ℝ) (consts : ℕ → ℕ → Ω → ℝ)
    (event : Set Ω)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ)
    (h : conv_represented_estimates d hd model H Ω P cutoff env
      ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
      usrc srcRep ucell Cext beta alpha eta t {1} I
      ℕ resp response consts event
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)
    (hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d))) :
    ∃ i0 : ℕ, z i0 = 0 ∧ r i0 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hC4, -⟩ := h
  obtain ⟨j, hj1, hj2⟩ := hC4 0 1 one_pos (fun _ => ⟨0, by simp⟩) ⟨0, by simp⟩ hunitRoot
  exact ⟨j, hj1, hj2⟩

/-- For the author-specified `Gcatalog` tie: the two represented-sequence events of the joint
catalogue are measurable and of full probability, so their intersection can serve as the
supplied event. -/
theorem aux_thm_C0_catalog_events_full
    (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (h : aux_thm_C0_JointHyp d hd alpha eta beta t model H Ω P field envE envF
      catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
      GNE GNF GE GF NE NF) :
    MeasurableSet (eventE ∩ eventF) ∧ P (eventE ∩ eventF)ᶜ = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hCat⟩ := h
  obtain ⟨root, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE,
    ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey,
    origin, gridRoot, gridKey, hCatE, hCatF⟩ := hCat
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, hEm, hE0, -⟩, -⟩ := hCatE
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, hFm, hF0, -⟩, -⟩ := hCatF
  refine ⟨hEm.inter hFm, ?_⟩
  rw [Set.compl_inter]
  exact measure_union_null hE0 hF0

/-- `mfd:thm-C0` on the determining family: with the unit cube in the family, the carried
uniform response moments give a deterministic `A`, chosen before the model and the pair, and a
cube/source whose two-sided bounded-response event has positive probability. -/
theorem aux_thm_C0_moment_event (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    (hin : aux_thm_C0_unitResponseMoments d) :
    ∃ delta0 A : ℝ, 0 < delta0 ∧ 1 ≤ A ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (envE envF : ℕ → Ω → BilateralField d)
        (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
        (responseE responseF : ℕ → Ω → ℝ)
        (eventE eventF : Set Ω)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
      aux_thm_C0_JointHyp d hd alpha eta beta t model H Ω P field envE envF
        catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
        GNE GNF GE GF NE NF →
      (∃ i0 : ℕ, z i0 = 0 ∧ r i0 = 1) →
      ∃ (i0 : ℕ) (f0 : DomainL2 (centeredCube (z i0) (r i0) (hr i0))),
        P {ω | A⁻¹ ≤ inner ℝ f0 (GE i0 ω f0) ∧ inner ℝ f0 (GE i0 ω f0) ≤ A ∧
          A⁻¹ ≤ inner ℝ f0 (GF i0 ω f0) ∧ inner ℝ f0 (GF i0 ω f0) ≤ A} ≠ 0 := by
  obtain ⟨delta0, C, hdelta0, hmain⟩ := aux_thm_C0_unitResponseMoments_at hin
  refine ⟨delta0, max 1 (8 * C), hdelta0, le_max_left _ _, ?_⟩
  intro _ _ model hmodel H Ω _ P _ field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF hjoint hunit
  obtain ⟨i0, hz, hr1⟩ := hunit
  obtain ⟨-, -, -, hInfra, -, -, hMP, -, hSdef, hGNdef, hGconv, -⟩ := hjoint
  obtain ⟨f0, hmom⟩ := hmain model hmodel H hInfra (z i0) (r i0) (hr i0) hz hr1 (S i0) (hSdef i0)
  exact ⟨i0, f0, aux_thm_C0_cube_moment_event d model H Ω P envE envF hMP (z i0) (r i0) (hr i0)
    (S i0) (GNE i0) (GNF i0) (GE i0) (GF i0) NE NF (hGNdef.mono fun _ h n f => h i0 n f)
    (hGconv.mono fun _ h => h i0) f0 C (max 1 (8 * C))
    (lt_of_lt_of_le one_pos (le_max_left _ _)) (le_max_right _ _) hmom⟩

/-- The unit-root package splits into the plain package and a unit-cube index. -/
theorem aux_thm_C0_jointU_split
    (d : ℕ) (hd : 2 ≤ d) (alpha eta beta t : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (envE envF : ℕ → Ω → BilateralField d)
    (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (h : aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field envE envF
      catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
      GNE GNF GE GF NE NF) :
    aux_thm_C0_JointHyp d hd alpha eta beta t model H Ω P field envE envF
      catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
      GNE GNF GE GF NE NF ∧ ∃ i0 : ℕ, z i0 = 0 ∧ r i0 = 1 := by
  obtain ⟨hP, hMeasF, hMap, hInfra, hNEmono, hNFmono, hMP, hEnvTend, hSdef, hGNdef, hGconv,
    hCat⟩ := h
  obtain ⟨root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey,
    origin, gridRoot, gridKey, hCatE, hCatF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  exact ⟨⟨hP, hMeasF, hMap, hInfra, hNEmono, hNFmono, hMP, hEnvTend, hSdef, hGNdef, hGconv,
    root, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF,
    Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hCatE, hCatF⟩,
    aux_thm_C0_unit_index d hd model H Ω P NE envE root z r hr S Dcat fcat trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t I _ responseE _ eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey hCatE hunitRoot⟩

/-- The whole of `thm_C0` for a jointly extracted pair whose determining family contains the
unit cube (`mfd:thm-C0`): density exclusion of both extreme ratio sets, the middle set, and
one common event inside `Gcatalog`. -/
theorem aux_thm_C0_main
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Ddet : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha)
    (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8))
    (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
        ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
            (3 * (R / (3 : ℝ) ^ H1) / 2) ⊆
          (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
        Cd * ((3 : ℝ) ^ H1) ^ ((d : ℝ) - 1))
    (hin : aux_thm_C0_unitResponseMoments d) :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (envE envF : ℕ → Ω → BilateralField d)
        (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
        (responseE responseF : ℕ → Ω → ℝ)
        (eventE eventF : Set Ω)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (Gcatalog : Set Ω)
        (_hGcatalogMeas : MeasurableSet Gcatalog)
        (_hGcatalogFull : P Gcatalogᶜ = 0),
      aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field envE envF
        catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
        GNE GNF GE GF NE NF →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr S GE GF NE NF →
      ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ G ⊆ Gcatalog ∧
        ∀ omega ∈ G, ∀ i : ℕ,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega)) ∧
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
              (limitFormEnergy (GF i omega) u).toReal ∧
            (limitFormEnergy (GF i omega) u).toReal ≤
              C0 * (limitFormEnergy (GE i omega) u).toReal := by
  obtain ⟨delta1, Cstar, hdelta1, hCstar, hDcmp⟩ :=
    aux_thm_C0_density_inputs d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp eta0 heta0 heta03 D theta alpha eta hD htheta htheta8
      halpha halpha1 heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  obtain ⟨delta2, A, hdelta2, hA, hM⟩ := aux_thm_C0_moment_event d hd alpha eta beta t hin
  refine ⟨min delta1 delta2, max 1 (2 * Cstar ^ 2 * A ^ 2), lt_min hdelta1 hdelta2,
    le_max_left _ _, ?_⟩
  intro _ _ model hmodel Rm Sreg It H Ω _ P _ field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF
    Gcatalog hGcatalogMeas hGcatalogFull hjointU hBndM
  obtain ⟨hj, hunit⟩ := aux_thm_C0_jointU_split d hd alpha eta beta t model H Ω P field envE envF
    catalogResponse catalogConstant responseE responseF eventE eventF z r hr S
    GNE GNF GE GF NE NF hjointU
  obtain ⟨ratio, hratio, hEF, hFE⟩ :=
    hDcmp model (le_trans hmodel (min_le_left _ _)) Rm Sreg It H Ω P field envE envF catalogResponse
      catalogConstant responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF hjointU hBndM
  obtain ⟨i0, f0, hmom⟩ :=
    hM model (le_trans hmodel (min_le_right _ _)) H Ω P field envE envF catalogResponse
      catalogConstant responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF hj hunit
  obtain ⟨-, -, -, -, -, -, -, -, -, hGNdef, hGconv, -⟩ := hj
  have hsn := aux_thm_C0_candidates_symm_nonneg d model H Ω P envE envF z r hr S GNE GNF GE GF
    NE NF hGNdef hGconv
  have hcore := aux_thm_C0_comparison_core P (fun i => centeredCube (z i) (r i) (hr i)) GE GF
    (hsn.mono fun _ h i => (h i).1.1) (hsn.mono fun _ h i => (h i).1.2)
    (hsn.mono fun _ h i => (h i).2.1) (hsn.mono fun _ h i => (h i).2.2)
    eta0 heta0 heta03 Cstar hCstar ratio hratio hEF hFE i0 f0 A hA hmom
  exact aux_thm_C0_assemble P (fun i => centeredCube (z i) (r i) (hr i)) GNE GNF GE GF
    Gcatalog hGcatalogMeas hGcatalogFull hGconv (2 * Cstar ^ 2 * A ^ 2) _
    (by positivity) (le_max_right _ _) hcore



theorem aux_thm_C0_unitResponseMoments_of_inputs (d : ℕ) (hd : 2 ≤ d)
    (E : in_J d) (X : in_extension d hd E) (P : in_poincare d hd E) :
    aux_thm_C0_unitResponseMoments d := by
  let measContinuous : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  let borelContinuous : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨deltaP, CP, hdeltaP, _hCP, hpos⟩ :=
    thm_c1_response_positive_moment hd E P (testL2 (unitResponseTest d))
  obtain ⟨deltaN, CN, hdeltaN, _hCN, hneg⟩ :=
    thm_c1_response_negative_moment hd E X
  refine ⟨min deltaP deltaN, max CP CN, lt_min hdeltaP hdeltaN, ?_⟩
  intro ms bs
  have hms : ms = measContinuous := @BorelSpace.measurable_eq _ _ ms bs
  subst ms
  intro M hdelta H hH S hS
  refine ⟨testL2 (unitResponseTest d), ?_⟩
  intro N
  obtain ⟨hp, hpb⟩ := hpos M H hH (hdelta.trans (min_le_left _ _)) S hS N
  obtain ⟨hpositive, hn, hnb⟩ := hneg M H hH (hdelta.trans (min_le_right _ _)) S hS N
  exact ⟨hpositive, hp, hpb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
    hn, hnb.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩



theorem thm_C0
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Ddet : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (_hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8))
      (_hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
          ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
              (3 * (R / L) / 2) ⊆
            (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
          Cd * L ^ ((d : ℝ) - 1)),
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (envE envF : ℕ → Ω → BilateralField d)
        (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
        (responseE responseF : ℕ → Ω → ℝ)
        (eventE eventF : Set Ω)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (Gcatalog : Set Ω)
        (_hGcatalogMeas : MeasurableSet Gcatalog)
        (_hGcatalogFull : P Gcatalogᶜ = 0),
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (S i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (_hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (S i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)) →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr S GE GF NE NF →
      ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ G ⊆ Gcatalog ∧
        ∀ omega ∈ G, ∀ i : ℕ,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega)) ∧
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
              (limitFormEnergy (GF i omega) u).toReal ∧
            (limitFormEnergy (GF i omega) u).toReal ≤
              C0 * (limitFormEnergy (GE i omega) u).toReal := by
  intro L hLlarge hCdPad
  obtain ⟨delta0, C0, hdelta0, hC0, hmain⟩ :=
    aux_thm_C0_main d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp eta0 heta0 heta03 D theta alpha eta hD htheta htheta8 halpha halpha1
      heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
      (aux_thm_C0_unitResponseMoments_of_inputs d hd I _X Pin)
  refine ⟨delta0, C0, hdelta0, hC0, ?_⟩
  intro _ _ model hmodel Rm Sreg It H Ω _ P _ field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr S GNE GNF GE GF NE NF
    Gcatalog hGcatalogMeas hGcatalogFull hjoint hBndP
  exact hmain model hmodel Rm Sreg It H Ω P field envE envF catalogResponse catalogConstant responseE
    responseF eventE eventF z r hr S GNE GNF GE GF NE NF Gcatalog hGcatalogMeas hGcatalogFull
    hjoint hBndP

end
end SubdiffusiveProcess.Paper
