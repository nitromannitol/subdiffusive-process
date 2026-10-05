module

public import SubdiffusiveProcess.Paper.goodext_padded_oscillation
public import SubdiffusiveProcess.Paper.goodext_good_cell_final
public import SubdiffusiveProcess.Paper.goodext_arbitrary_cell_response
public import SubdiffusiveProcess.Paper.goodext_source_bound_transport
public import SubdiffusiveProcess.Geometry.TriadicGridScale
public import SubdiffusiveProcess.Geometry.CubePowerComparison
public import SubdiffusiveProcess.Paper.goodext_response_of_root_minimizers
public import SubdiffusiveProcess.Paper.goodext_root_grid_coefficient_cap
public import SubdiffusiveProcess.Paper.goodext_catalog_root_absolute_cap
public import SubdiffusiveProcess.Paper.goodext_represented_root_trace_controls
public import SubdiffusiveProcess.Sobolev.GoodCellTraceAssembly
public import SubdiffusiveProcess.Sobolev.TriadicTraceEnergyBudget
public import SubdiffusiveProcess.Paper.goodext_represented_padded_lower
public import SubdiffusiveProcess.Sobolev.PaddedPoincareScaling
public import SubdiffusiveProcess.Sobolev.HolderAffinePullback
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RepresentativeReadout
public import SubdiffusiveProcess.Paper.goodext_parent_oscillation_from_graph
public import SubdiffusiveProcess.Sobolev.NormalizedBoundaryHolder
public import SubdiffusiveProcess.Sobolev.GoodCellEnergyScaling
public import SubdiffusiveProcess.Paper.goodext_represented_local_trace
public import SubdiffusiveProcess.Paper.goodext_cutoff_local_trace
public import SubdiffusiveProcess.Analysis.NormalizedCoefficientLimits
public import SubdiffusiveProcess.Paper.goodext_represented_source_representative
public import SubdiffusiveProcess.Paper.candidate_represented_source_bank
public import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_support
public import SubdiffusiveProcess.Paper.goodext_represented_local_trace_controls
public import SubdiffusiveProcess.Paper.inputs_classical_e4_cube_norms
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.candidate_good_event
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.candidate_good_estimates
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.reference_coefficients
public import SubdiffusiveProcess.Paper.parameter_chain
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.frozen_ae_bounded_subsequence
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.GoodextHolderLimit
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Equal physical coordinates identify the literal cutoff lower coefficient. -/
theorem aux_lem_goodext_lower_coefficient_congr
    {d : ℕ} (I : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (xi : BilateralField d) (N : ℕ)
    (z1 z2 : SpatialCoordinates d) (r1 r2 : ℝ) (h1 : 0 < r1) (h2 : 0 < r2)
    (hz : z1 = z2) (hr : r1 = r2) (sigma : ℝ) :
    I.lam z1 r1 h1 (cutoffPositiveCoefficient M H xi N z1 h1) z1 r1 sigma 2 =
      I.lam z2 r2 h2 (cutoffPositiveCoefficient M H xi N z2 h2) z2 r2 sigma 2 := by
  cases hz
  cases hr
  rfl

/-- The response-space solution with zero boundary data solves the weak Dirichlet problem. -/
theorem aux_lem_goodext_responseSolution_solvesDirichlet
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : PositiveCoefficient Q) (fL2 : DomainL2 Q) (f : SpatialCoordinates d → ℝ)
    (hf : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f) :
    SolvesDirichlet a f (0 : weakSobolevGraph Q)
      (⟨(responseSolution S a ((sobolevVolumeLoad fL2).comp S.space.subtypeL) : SobolevData Q),
        S.le_weak (responseSolution S a ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).property⟩ :
        weakSobolevGraph Q) := by
  let uS := responseSolution S a ((sobolevVolumeLoad fL2).comp S.space.subtypeL)
  refine ⟨?_, ?_⟩
  · change ((uS : SobolevData Q) - (0 : SobolevData Q)) ∈ killedSobolevGraph Q
    have hu : (uS : SobolevData Q) ∈ S.space := uS.property
    have huKilled : (uS : SobolevData Q) ∈ killedSobolevGraph Q := hS ▸ hu
    simpa only [sub_zero] using huKilled
  · intro ψ
    let ψS : S.space := ⟨(ψ : SobolevData Q), by rw [hS]; exact ψ.property⟩
    have hs := responseSolution_spec S a
      ((sobolevVolumeLoad fL2).comp S.space.subtypeL) ψS
    calc
      sobolevCoefficientForm a (uS : SobolevData Q) (ψ : SobolevData Q) =
          responseForm S a uS ψS := by
        rw [sobolevCoefficientForm_eq_sum_integral, responseForm_apply]
      _ = ((sobolevVolumeLoad fL2).comp S.space.subtypeL) ψS := hs
      _ = ∫ x in (Q : Set (SpatialCoordinates d)), f x * (ψ : SobolevData Q).1 x := by
        rw [ContinuousLinearMap.comp_apply, sobolevVolumeLoad_apply]
        refine integral_congr_ae (hf.mono fun x hx => ?_)
        change (fL2 : DomainL2 Q) x * (ψS : SobolevData Q).1 x =
          f x * (ψ : SobolevData Q).1 x
        rw [hx]

theorem aux_lem_goodext_ae_and {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : α → Prop} (hp : ∀ᵐ x ∂μ, p x) (hq : ∀ᵐ x ∂μ, q x) :
    ∀ᵐ x ∂μ, p x ∧ q x := by
  exact hp.and hq

theorem aux_lem_goodext_ae_subseq_exists {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hfg : TendstoInMeasure P f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ omega ∂P, Tendsto (fun i => f (ns i) omega) atTop (𝓝 (g omega)) := by
  exact hfg.exists_seq_tendsto_ae

theorem aux_lem_goodext_le_of_eventually_le {f : ℕ → ℝ} {L c : ℝ}
    {ns : ℕ → ℕ}
    (hlim : Tendsto (fun i => f (ns i)) atTop (𝓝 L))
    (hbound : ∀ᶠ i in atTop, f (ns i) ≤ c) : L ≤ c := by
  exact le_of_tendsto hlim hbound

theorem aux_lem_goodext_icc_of_eventually_icc {f : ℕ → ℝ} {L a b : ℝ}
    {ns : ℕ → ℕ}
    (hlim : Tendsto (fun i => f (ns i)) atTop (𝓝 L))
    (hbound : ∀ᶠ i in atTop, f (ns i) ∈ Set.Icc a b) : L ∈ Set.Icc a b := by
  exact ⟨ge_of_tendsto hlim (hbound.mono fun _ h => h.1),
    le_of_tendsto hlim (hbound.mono fun _ h => h.2)⟩

theorem aux_lem_goodext_sq_add_le (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem aux_lem_goodext_ratio_common_factor (c d e : ℝ) (hc : c ≠ 0) (he : e ≠ 0) :
    (d * e) / (c * e) = d / c := by
  field_simp

theorem aux_lem_goodext_sRef_ratio_eRef_ratio (eRef0 eRef1 E : ℝ)
    (heRef0 : eRef0 ≠ 0) (hE : E ≠ 0) :
    (eRef1 * E) / (eRef0 * E) = eRef1 / eRef0 := by
  exact aux_lem_goodext_ratio_common_factor eRef0 eRef1 E heRef0 hE

theorem aux_lem_goodext_sq_rpow_le (r alpha M w : ℝ)
    (hr : 0 < r) (hw0 : 0 ≤ w) (hw : w ≤ r ^ alpha * M) :
    w ^ 2 ≤ r ^ (2 * alpha) * M ^ 2 := by
  have hsq : w ^ 2 ≤ (r ^ alpha * M) ^ 2 := pow_le_pow_left₀ hw0 hw 2
  have hcalc : (r ^ alpha * M) ^ 2 = r ^ (2 * alpha) * M ^ 2 := by
    calc
      (r ^ alpha * M) ^ 2 = (r ^ alpha) ^ 2 * M ^ 2 := by ring_nf
      _ = (r ^ alpha * r ^ alpha) * M ^ 2 := by ring_nf
      _ = r ^ (alpha + alpha) * M ^ 2 := by rw [Real.rpow_add hr alpha alpha]
      _ = r ^ (2 * alpha) * M ^ 2 := by ring_nf
  rw [hcalc] at hsq
  exact hsq

theorem aux_lem_goodext_nonneg_set_isGLB (S : Set ℝ)
    (h0 : ∀ e ∈ S, 0 ≤ e) (hne : S.Nonempty) :
    IsGLB S (sInf S) ∧ 0 ≤ sInf S := by
  have hbdd : BddBelow S := ⟨0, fun _ he => h0 _ he⟩
  have hglb : IsGLB S (sInf S) := Real.isGLB_sInf hne hbdd
  have hzero : (0 : ℝ) ∈ lowerBounds S := fun _ he => h0 _ he
  exact ⟨hglb, hglb.2 hzero⟩

theorem aux_lem_goodext_sInf_le_of_mem_le {S : Set ℝ} {b : ℝ}
    (hne : S.Nonempty) (hbdd : BddBelow S) {e : ℝ} (he : e ∈ S) (heb : e ≤ b) :
    sInf S ≤ b := by
  exact (Real.isGLB_sInf hne hbdd).1 he |>.trans heb

/-- A controlled local trace-extension witness gives the response infimum bound. -/
theorem aux_lem_goodext_response_glb_of_controlled_witness
    {S : Set ℝ} {b : ℝ} (hS : ∀ e ∈ S, 0 ≤ e)
    (hw : ∃ e ∈ S, e ≤ b) : IsGLB S (sInf S) ∧ sInf S ≤ b := by
  rcases hw with ⟨e, heS, heb⟩
  obtain ⟨hglb, _⟩ := aux_lem_goodext_nonneg_set_isGLB S hS ⟨e, heS⟩
  exact ⟨hglb, (hglb.1 heS).trans heb⟩

/-- The killed Dirichlet minimizer costs no more energy than any admissible datum. -/
theorem aux_lem_goodext_dirichlet_minimizer_le
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (b : weakSobolevGraph Ω)
    (w : S.space) :
    dirichletResponse S a b ≤
      sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) := by
  exact (dirichletResponse_isLeast S a b).2 ⟨w, rfl⟩

theorem aux_lem_goodext_exponent_algebra (d : ℕ) (C Kc Cd h r alpha eta : ℝ)
    (hr : 0 < r) :
    C * (Kc * r ^ (-eta)) * r ^ ((d : ℝ) - 2) * (Cd * r ^ alpha * h) ^ 2 =
      (C * Kc * Cd ^ 2 * h ^ 2) * r ^ ((d : ℝ) - 2 + 2 * alpha - eta) := by
  calc
    C * (Kc * r ^ (-eta)) * r ^ ((d : ℝ) - 2) * (Cd * r ^ alpha * h) ^ 2 =
        C * Kc * Cd ^ 2 * h ^ 2 *
          (r ^ (-eta) * r ^ ((d : ℝ) - 2) * (r ^ alpha) ^ 2) := by ring_nf
    _ = C * Kc * Cd ^ 2 * h ^ 2 *
          (r ^ (-eta) * r ^ ((d : ℝ) - 2) * r ^ (2 * alpha)) := by
      have hpow : (r ^ alpha) ^ 2 = r ^ (2 * alpha) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
        congr 1; ring_nf
      rw [hpow]
    _ = C * Kc * Cd ^ 2 * h ^ 2 *
          r ^ (-eta + ((d : ℝ) - 2) + 2 * alpha) := by
      rw [← Real.rpow_add hr (-eta) ((d : ℝ) - 2),
        ← Real.rpow_add hr (-eta + ((d : ℝ) - 2)) (2 * alpha)]
    _ = (C * Kc * Cd ^ 2 * h ^ 2) *
          r ^ ((d : ℝ) - 2 + 2 * alpha - eta) := by ring_nf

theorem aux_lem_goodext_sequence_event
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (resp : ι → ℕ → Ω → ℝ) (respLim : ι → Ω → ℝ)
    (constants : ι → ℕ → Ω → ℝ) (G : Set Ω)
    (h : conv_represented_sequence P resp respLim constants G) :
    MeasurableSet G ∧ P Gᶜ = 0 := by
  unfold conv_represented_sequence at h
  exact ⟨h.2.1, h.2.2.1⟩

theorem aux_lem_goodext_sequence_response_tendsto
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (resp : ι → ℕ → Ω → ℝ) (respLim : ι → Ω → ℝ)
    (constants : ι → ℕ → Ω → ℝ) (G : Set Ω)
    (h : conv_represented_sequence P resp respLim constants G) :
    ∀ i : ι, ∀ omega ∈ G,
      Tendsto (fun N : ℕ => resp i N omega) atTop (𝓝 (respLim i omega)) := by
  unfold conv_represented_sequence at h
  exact h.2.2.2.1

theorem aux_lem_goodext_sequence_constant_bounded
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (resp : ι → ℕ → Ω → ℝ) (respLim : ι → Ω → ℝ)
    (constants : ι → ℕ → Ω → ℝ) (G : Set Ω)
    (h : conv_represented_sequence P resp respLim constants G) :
    ∀ i : ι, ∀ omega ∈ G, ∃ B : ℝ, ∀ N : ℕ,
      |constants i N omega| ≤ B := by
  unfold conv_represented_sequence at h
  exact h.2.2.2.2

theorem aux_lem_goodext_limit_sym_pos
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGN : ∀ n f,
      GN n f =
        (responseSolution S (a n)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : Tendsto GN atTop (𝓝 G)) :
    (∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) := by
  have happ : ∀ x : DomainL2 Q, Tendsto (fun n => GN n x) atTop (𝓝 (G x)) :=
    fun x => ((continuous_id.clm_apply continuous_const).tendsto G).comp hlim
  constructor
  · intro x y
    have h1 : Tendsto (fun n => inner ℝ (GN n x) y) atTop
        (𝓝 (inner ℝ (G x) y)) := (happ x).inner tendsto_const_nhds
    have h2 : Tendsto (fun n => inner ℝ x (GN n y)) atTop
        (𝓝 (inner ℝ x (G y))) := tendsto_const_nhds.inner (happ y)
    have heq : ∀ n, inner ℝ (GN n x) y = inner ℝ x (GN n y) := by
      intro n
      rw [hGN, hGN, real_inner_comm]
      exact volumeResponse_pairing_symm S (a n) y x
    exact tendsto_nhds_unique (h1.congr heq) h2
  · intro x
    have h1 : Tendsto (fun n => inner ℝ x (GN n x)) atTop
        (𝓝 (inner ℝ x (G x))) := tendsto_const_nhds.inner (happ x)
    refine ge_of_tendsto' h1 (fun n => ?_)
    rw [hGN]
    exact volumeResponse_pairing_nonneg S (a n) x

theorem aux_lem_goodext_limit_range_mem_domain
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hGN : ∀ n f,
      GN n f =
        (responseSolution S (a n)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : Tendsto GN atTop (𝓝 G))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∀ f : DomainL2 Q, G f ∈ E.domain := by
  obtain ⟨hsym, hpos⟩ := aux_lem_goodext_limit_sym_pos S a GN G hGN hlim
  intro f
  apply _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.mem_domain_of_energy_lt_top
  rw [hE]
  have hval : limitFormEnergy G (G f) =
      ((inner ℝ f (G f) : ℝ) : EReal) :=
    iSup_quadraticDual_apply_image G hsym hpos f
  rw [hval]
  exact EReal.coe_lt_top _

/-- Restriction and normalization preserve a smaller Holder exponent on a cell boundary. -/
theorem aux_lem_goodext_source_trace_class
    {d : ℕ} [NeZero d] (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (alpha beta : ℝ) (hbetaLtAlpha : beta < alpha) :
    ∀ (U : SpatialCoordinates d → ℝ),
      ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) U →
      ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
        Metric.ball z' (r' / 2) ⊆
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
        IsCellBoundaryClass beta z' r' U := by
  intro U hUcont hUholder z' r' hr' hball
  have hclosed : closure (Metric.ball z' (r' / 2)) ⊆
      closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) :=
    closure_mono hball
  have hlocal := FiniteStopping.isHolderOn_mono hclosed alpha U hUholder
  have hpull := isHolderOn_normalized_cube alpha z' r' 0 hr' U hlocal
  have hdiam : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ∀ y ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d := by
    intro x hx y hy
    have hxball : dist x 0 ≤ 1 / 2 := Metric.mem_closedBall.mp hx
    have hyball : dist y 0 ≤ 1 / 2 := Metric.mem_closedBall.mp hy
    have hdist : dist x y ≤ 1 := by
      have ht := dist_triangle x 0 y
      rw [dist_comm (0 : SpatialCoordinates d) y] at ht
      linarith
    calc
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y :=
        aux_lem_goodext_euclid_le x y
      _ ≤ Real.sqrt d * 1 := mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg _)
      _ = Real.sqrt d := mul_one _
  have hdrop := aux_lem_goodext_holder_drop hbetaLtAlpha hdiam hpull
  apply FiniteStopping.reg_to_boundary_class z' r' hr' beta U 0 ?_ hdrop
  have hc := hUcont.mono hclosed
  change ContinuousOn U (Metric.closedBall z' (r' / 2))
  rw [closure_ball z' (by positivity : r' / 2 ≠ 0)] at hc
  exact hc



theorem lem_goodext
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hbetaLtAlpha : beta < alpha)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (_hepshom : 0 < epshom)
    (etaGrid : ℝ) (_hetaGrid : 0 < etaGrid)
    (H1 : ℕ) (_hH1 : 0 < H1)
    (moment : ℝ) (_hmoment : 1 ≤ moment)
    :
    ∃ Cbound eps0 lam0 delta0 : ℝ,
      1 ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hMH : InfraredCharacterization M H)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (_hfield_meas : Measurable field)
        (_hfield_law : Measure.map field P = (chaosSampleLaw M).toMeasure)
        (env : Fin 2 → ℕ → Ω → BilateralField d)
        (_henv_meas : ∀ (a : Fin 2) (n : ℕ), Measurable (env a n))
        (_henv_law : ∀ (a : Fin 2) (n : ℕ),
          Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
        (_hEnvConv : ∀ᵐ omega ∂P, ∀ a : Fin 2,
          Tendsto (fun n => env a n omega) atTop (𝓝 (field omega)))
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ)
        (_hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (_hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (_hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (_hfactor : factor selfE = 0)
        (padE : Enl) (_hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (_hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (_hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (_hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (_hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (_hGridCover : ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (_hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (_hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (_hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre :
          ∀ (_U : Enl × Shift) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
              SpatialCoordinates d)
        (_hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (_hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (_hepsSmall : eps ≤ eps0)
        (_hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (_hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (_hcdet : 0 < cdet) (_hcdetSmall : cdet ≤ Cbound⁻¹)
        (_hlamSmall : lambdaDet ≤ lam0)
        (_hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (_hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (_hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (_hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤))
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (_hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) *
                  _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (_hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (_hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (_hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (_hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (_hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (phi : Fin 2 → ℕ → ℕ)
        (_hphi : ∀ (a : Fin 2), StrictMono (phi a))
        (prefixZLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            Ω → ℝ)
        (prefixDLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            Ω → ℝ)
        (ellLoLim ellHiLim : Fin 2 → (Enl × Shift) → Ω → ℝ)
        (AE_Lim : Fin 2 → (Enl × Shift) → Ω → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → Cmp → Ω → ℝ)
        (_hPrefixZLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixZ (phi a n) U D code (env a n omega)) atTop
            (prefixZLim a U D code))
        (_hPrefixDLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixD (phi a n) U D code (env a n omega)) atTop
            (prefixDLim a U D code))
        (_hEllLoLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellLoN (phi a n) U (env a n omega)) atTop
            (ellLoLim a U))
        (_hEllHiLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellHiN (phi a n) U (env a n omega)) atTop
            (ellHiLim a U))
        (_hAELim : ∀ (a : Fin 2) (U : Enl × Shift) (i j : Fin d),
          TendstoInMeasure P
            (fun n omega => AEN (phi a n) U (env a n omega) i j) atTop
            (fun omega => AE_Lim a U omega i j))
        (_hErrLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure P
            (fun n omega => errN (phi a n) c (env a n omega)) atTop
            (errLim a c))
        (_hRatioLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure P
            (fun n omega => ratioN (phi a n) c (env a n omega)) atTop
            (ratioLim a c))
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (RootIndex : Type) [Countable RootIndex] [DecidableEq RootIndex]
        (root0 : RootIndex)
        (zCat : RootIndex → SpatialCoordinates d) (rCat : RootIndex → ℝ)
        (hrCat : ∀ j, 0 < rCat j)
        (SCat : ∀ j, ResponseSpace (centeredCube (zCat j) (rCat j) (hrCat j)))
        (DCat : ∀ j, Submodule ℚ (DomainL2 (centeredCube (zCat j) (rCat j) (hrCat j))))
        [_hDCat : ∀ j, Countable (DCat j)]
        (fCat : ∀ j, (DCat j) → SpatialCoordinates d → ℝ)
        (TCat : RootIndex → Type) [_hTCat : ∀ j, Countable (TCat j)]
        (thetaCat : ∀ j, TCat j → SpatialCoordinates d → ℝ)
        (thetaH1Cat : ∀ j, TCat j →
          Homogenization.H1Function
            (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
        (usrc : Fin 2 → ∀ j, (DCat j) → ℕ → Ω → (SCat j).space)
        (srcRep : Fin 2 → ∀ j, (DCat j) → ℕ → Ω → SpatialCoordinates d → ℝ)
        (ucell : Fin 2 → ∀ j, TCat j → ℕ → Ω →
          Homogenization.H1Function
            (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
        (Cext : ℝ) (etaCat : ℝ) (t : ℝ) (orders : Finset ℝ)
        (_hetaCatGrid : etaCat ≤ etaGrid)
        (Index : Type) [Countable Index]
        (resp : Fin 2 → Index → ℕ → Ω → ℝ) (respLim : Fin 2 → Index → Ω → ℝ)
        (constants : Fin 2 → Index → ℕ → Ω → ℝ) (Gcat : Set Ω)
        (coercivityKey extensionKey lambdaKey : RootIndex → Index)
        (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (DCat j) → Index)
        (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, TCat j → Index)
        (Grid : Type) [Countable Grid]
        (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → RootIndex)
        (gridKey : Grid → Index)
        (_hRootCatalogue : zCat root0 = Qcentre ∧ rCat root0 = Qside)
        (_hRepEstimates : ∀ a : Fin 2,
          conv_represented_estimates d hd M H Ω P (phi a) (env a) RootIndex root0
            zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
            (usrc a) (srcRep a) (ucell a) Cext beta alpha etaCat t orders I
            Index (resp a) (respLim a) (constants a) Gcat
            coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
            sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
            Grid origin gridRoot gridKey)
        (_hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (S : ResponseSpace (centeredCube Qcentre Qside hQside))
        (_hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
        (GN : ℕ → BilateralField d →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (_hGN : ∀ N omega f, GN N omega f =
          (responseSolution S
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Fin 2 → Ω →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (_hGE : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            Tendsto (fun n => GN (phi a n) (env a n omega)) atTop (𝓝 (G a omega)))
        (Form : Fin 2 → Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (_hE : ∀ (a : Fin 2) omega u,
          (Form a omega).energy u = limitFormEnergy (G a omega) u)
        (Gamma : ∀ (a : Fin 2) omega,
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Form a omega))
        (_hGammaRecovery : ∀ a : Fin 2, ∀ᵐ omega ∂P,
          ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
          ∀ test : SpatialCoordinates d → ℝ,
            Continuous test → HasCompactSupport test →
            Tendsto (fun n =>
              let coeff := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H
                (env a n omega) (phi a n) Qcentre hQside
              let un := responseSolution S coeff
                ((sobolevVolumeLoad f).comp S.space.subtypeL)
              ∫ x in (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
                test x * coeff.val x *
                  ∑ i : Fin d, ((sobolevGradient un.val i) x) ^ 2)
              atTop (𝓝 (∫ x, test x ∂((Gamma a omega).measure (G a omega f)))))
        (sRef : Fin 2 → Ω → ℝ)
        (sCmp : Fin 2 → Cmp → Ω → ℝ)
        (_hsRef : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            0 < sRef a omega ∧
            Tendsto (fun n => sN (phi a n) (k : ℤ) z (env a n omega)) atTop
              (𝓝 (sRef a omega)))
        (_hsCmp : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P, ∀ c : Cmp,
            0 < sCmp a c omega ∧
            Tendsto (fun n => sN (phi a n) (cmpLevel c) (cmpCentre c) (env a n omega))
              atTop (𝓝 (sCmp a c omega)))
        (eRef : Fin 2 → ℕ → ℝ)
        (_heRef_pos : ∀ (a : Fin 2) (j : ℕ), 0 < eRef a j)
        (_heRef_lim : ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a n - j) / kappa (phi a n)) atTop
            (𝓝 (eRef a j)))
        (_hsRef_eq : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            sRef a omega = eRef a k *
              Real.exp (H (field omega) z +
                ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)),
      let Q := centeredCube Qcentre Qside hQside
      let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      let _q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let Good : Fin 2 → Set Ω := fun a =>
        {omega |
          (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              prefixZLim a U D code omega < lambdaLim * (D : ℝ) ∧
              prefixDLim a U D code omega < lambdaLim * (D : ℝ)) ∧
          (∀ U : Enl × Shift,
            cell ≤ ellLoLim a U omega ∧ ellHiLim a U omega ≤ cell⁻¹) ∧
          errLim a chosen omega ≤ epshom * cdet ∧
          (∀ c : Cmp, ratioLim a c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
      let L : ℝ := (3 : ℝ) ^ H1
      let unitClosed : Set (SpatialCoordinates d) :=
        closedCube (0 : SpatialCoordinates d) 1 one_pos
      ∀ᵐ omega ∂P,
        let responseSet : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → Set ℝ :=
          fun r' z' b =>
            {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
              v ∈ (Form 1 omega).domain ∧
              ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
              ((v : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
              (∀ x ∈ frontier (Metric.ball z' (r' / 2)), V x = b x) ∧
              e = ((Gamma 1 omega).measure v
                (Metric.ball z' (r' / 2))).toReal}
        let responseF : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → ℝ :=
          fun r' z' b => sInf (responseSet r' z' b)
        (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
          ∀ (fL2 : DomainL2 Q),
            ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] f) →
          let u := G 0 omega fL2
          let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
            ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] U) ∧
            (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
            ((omega ∈ Good 0 ∧ omega ∈ Good 1) →
              ∀ (zP : SpatialCoordinates d)
                (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
                let nuP : ℝ := ((Gamma 0 omega).measure u parentCell).toReal
                ∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha unitClosed (fun x => U (z + r • x) - cq) ∧
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) ≤
                    Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef 0 omega) ^ (-(1 : ℝ) / 2) *
                      Real.sqrt nuP +
                      Ctotal * r ^ (2 : ℝ) * (sRef 0 omega)⁻¹ * fsup ∧
                  (responseSet r z U).Nonempty ∧
                  IsGLB (responseSet r z U) (responseF r z U) ∧
                  responseF r z U ≤ Ctotal * (eRef 1 k / eRef 0 k) *
                    (nuP + (sRef 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
            (∃ K : ℝ, 0 ≤ K ∧
              ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
                Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                  (responseSet r' z' U).Nonempty ∧
                  IsGLB (responseSet r' z' U) (responseF r' z' U) ∧
                  responseF r' z' U ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)))
  := by
  have halpha' : alpha ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [halpha.1], halpha.2⟩
  obtain ⟨Cbase, hCGE⟩ := candidate_good_estimates.{0} d hd I _X _Sob Pin
    _MeyersMorrey _Step D Cp alpha beta s sigma cell halpha' hbeta hs hsSmall
    hsigma_eq hsigma hcell
  let tGrowth : ℝ := (d : ℝ) - 1 / 2
  have htGrowthLower : (d : ℝ) - 1 < tGrowth := by
    dsimp [tGrowth]
    linarith only [show (0 : ℝ) < 1 / 2 by norm_num]
  have htGrowthUpper : tGrowth < (d : ℝ) := by
    dsimp [tGrowth]
    linarith only [show (0 : ℝ) < 1 / 2 by norm_num]
  obtain ⟨Ctrace, deltaTrace, hCtrace, hdeltaTrace, hSharpTrace⟩ :=
    goodext_represented_local_trace d hd I Pin _X _MeyersMorrey Cp _Sob
      (inputs_classical_e4_cube_norms d hd) tGrowth alpha beta
      htGrowthLower htGrowthUpper (by linarith only [halpha.1]) halpha.2 hbeta
  obtain ⟨deltaRep, hdeltaRep, hGlobalSource⟩ :=
    candidate_good_estimates_trace_support d hd I Pin _X _MeyersMorrey Cp _Sob alpha
      ⟨by linarith only [halpha.1], halpha.2⟩
  obtain ⟨deltaRoot, hdeltaRoot, hRootTraceControls⟩ :=
    goodext_represented_root_trace_controls d hd I Pin _X _MeyersMorrey Cp _Sob
      (inputs_classical_e4_cube_norms d hd) tGrowth alpha
      htGrowthLower htGrowthUpper (by linarith only [halpha.1]) halpha.2
  obtain ⟨eps0, lam0, deltaCGE, heps0, hlam0, hdeltaCGE, hCGEatOne⟩ :=
    hCGE.2 1 (by norm_num) (by norm_num)
  have hsigmaPos : 0 < sigma := hsigma.1
  let discount : ℝ := Homogenization.Book.Ch02.geometricDiscount sigma 2 /
    Homogenization.Book.Ch02.geometricDiscount 1 1
  have hdiscount : 0 < discount := div_pos
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by positivity))
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by norm_num))
  let Kp : ℝ := Real.sqrt (Pin.C ^ 2 * 18 / (discount * cell * (3 : ℝ) ^ d))
  have hKp : 0 ≤ Kp := Real.sqrt_nonneg _
  have hCbase : 0 < Cbase := lt_of_lt_of_le zero_lt_one hCGE.1
  let Dtrace : ℝ := (Real.sqrt d) ^ (alpha - beta)
  let CeTrace : ℝ := 2 * Ctrace * cell⁻¹
  have hDtrace : 0 ≤ Dtrace := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hCeTrace : 0 ≤ CeTrace :=
    mul_nonneg (mul_nonneg (by norm_num) hCtrace.le) (inv_nonneg.mpr hcell.1.le)
  obtain ⟨Cbound, hCbound, hCbaseBound, hCminBound, hBudget⟩ :=
    exists_triadic_trace_energy_budget Cbase Kp CeTrace Dtrace (Cbase * max 1 epshom)
      hCbase.le hKp hCeTrace hDtrace
  let delta0 : ℝ := min 1 (min (min deltaCGE (min deltaTrace deltaRep)) deltaRoot)
  have hdelta0 : 0 < delta0 :=
    lt_min zero_lt_one (lt_min (lt_min hdeltaCGE (lt_min hdeltaTrace hdeltaRep)) hdeltaRoot)
  refine ⟨Cbound, eps0, lam0, delta0, hCbound, heps0, hlam0, hdelta0, ?_⟩
  intros cbuf k0 M Rm Sreg It H hMH Ω instΩ P instP field hfield_meas hfield_law env
    henv_meas henv_law hEnvConv k z qside hqside qcenter hqcenter Enl Shift Cmp
    instEnl instShift instCmp selfE selfShift qRoot hqRoot factor hfactor padE hpad
    shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos
    hGridCover parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide
    cmpPos chosen observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hdisorder prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard
    sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN phi hphi
    prefixZLim prefixDLim ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim
    hPrefixDLim hEllLoLim hEllHiLim hAELim hErrLim hRatioLim Qcentre Qside hQside
    RootIndex instRootCount instRootDec root0 zCat rCat hrCat SCat DCat instDCat fCat
    TCat instTCat thetaCat thetaH1Cat usrc srcRep ucell Cext etaCat t orders hetaCatGrid
    Index instIndex resp respLim constants Gcat coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid instGrid origin gridRoot gridKey hRootCatalogue hRepEstimates
    hRootsQ S hS GN hGN G hGE Form hE Gamma hGammaRecovery sRef sCmp hsRef hsCmp eRef
    heRef_pos heRef_lim hsRef_eq
  have hrep0 := hRepEstimates 0
  unfold conv_represented_estimates at hrep0
  obtain ⟨hrepA, hrepB, hrepC, hrepD, hrepE, hrepF, hrepG, hrepH, hrepI, hrepJ, hrepRest⟩ := hrep0
  have hsequence : conv_represented_sequence P (resp 0) (respLim 0) (constants 0) Gcat := hrepJ
  rcases hrepRest with ⟨hgeom, hcent, hside, hcomplete, hgridorig, hgridroot,
    hS_space, hD_dense, hfcat, hsmoothtest, htheta, hsrcTrace, hparentTrace,
    hboundaryApprox, hplateau, hconstMeas, hconstBound, hconstNonneg,
    hActual, hCoeff, hCoercive, hTrace, hGridEstimate, hSource, hCell⟩
  have hdisorderOne : M.delta ≤ 1 := hdisorder.trans (min_le_left _ _)
  have hdisorderRoot : M.delta ≤ deltaRoot :=
    hdisorder.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdisorderOld : M.delta ≤ min deltaCGE (min deltaTrace deltaRep) :=
    hdisorder.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdisorderTrace : M.delta ≤ deltaTrace :=
    hdisorderOld.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdisorderRep : M.delta ≤ deltaRep :=
    hdisorderOld.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdisorderCGE : M.delta ≤ deltaCGE := hdisorderOld.trans (min_le_left _ _)
  have htauOne : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ 1 := by
    have hlog : Real.log 2 / 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [h]
    have hdeltaSq : M.delta ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ M.shellPrefix.delta_pos.le zero_le_one).mpr hdisorderOne
    have hTau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 :=
      (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M).trans
        (mul_le_of_le_one_left (sq_nonneg _) hlog)
    simpa only [one_pow] using hTau.trans hdeltaSq
  have hCboundPos : 0 < Cbound := lt_of_lt_of_le zero_lt_one hCbound
  have hcdetRescale : max 1 epshom * cdet ≤ Cbase⁻¹ := by
    have hm : 0 < max 1 epshom := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hCbase).2
    calc
      max 1 epshom * cdet * Cbase = (Cbase * max 1 epshom) * cdet := by ring
      _ ≤ Cbound * cdet := mul_le_mul_of_nonneg_right hCminBound hcdet.le
      _ ≤ Cbound * Cbound⁻¹ := mul_le_mul_of_nonneg_left hcdetSmall hCboundPos.le
      _ = 1 := mul_inv_cancel₀ hCboundPos.ne'
  have hEnvConv0 : ∀ᵐ om ∂P, ∀ a : PUnit,
      Tendsto (fun n => env 0 n om) atTop (𝓝 (field om)) :=
    hEnvConv.mono (fun om h a => h 0)
  have hCGEEvent := hCGEatOne cbuf k0 M Rm Sreg It H hMH Ω P field
    hfield_meas hfield_law (fun (_ : PUnit) => env 0)
    (fun (_ : PUnit) => henv_meas 0) (fun (_ : PUnit) => henv_law 0) hEnvConv0
    k z qside hqside qcenter hqcenter Enl Shift Cmp selfE selfShift qRoot hqRoot
    factor hfactor padE hpad shift hshift rootLevel hrootLevel rootSide hrootSide
    rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre hcmpCentre
    cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre hObservationCentre
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet (max 1 epshom * cdet) hThresholds
    (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hcdet)
    hcdetRescale hlamSmall hdisorderCGE prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard
    sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN
    (phi 0) (hphi 0) (prefixZLim 0) (prefixDLim 0) (ellLoLim 0) (ellHiLim 0)
    (AE_Lim 0) (errLim 0) (ratioLim 0) (hPrefixZLim 0) (hPrefixDLim 0)
    (hEllLoLim 0) (hEllHiLim 0) (hAELim 0) (hErrLim 0) (hRatioLim 0)
    Qcentre Qside hQside hRootsQ S hS GN hGN (G 0) (hGE 0) (Form 0) (hE 0)
    (Gamma 0) (sRef 0) (sCmp 0) (hsRef 0) (hsCmp 0)
  have hevent := aux_lem_goodext_sequence_event P (resp 0) (respLim 0) (constants 0) Gcat hsequence
  have hGcat : ∀ᵐ omega ∂P, omega ∈ Gcat := by
    rw [MeasureTheory.ae_iff]
    simpa only [Set.mem_compl_iff, not_not] using! hevent.2
  have hGE0event : ∀ᵐ omega ∂P,
      Tendsto (fun n => GN (phi 0 n) (env 0 n omega)) atTop (𝓝 (G 0 omega)) := hGE 0
  have hGE1event : ∀ᵐ omega ∂P,
      Tendsto (fun n => GN (phi 1 n) (env 1 n omega)) atTop (𝓝 (G 1 omega)) := hGE 1
  obtain ⟨Krep1, Crep1, hCrep1, hKrepMem1, hKrepNorm1, _, hRepSource1⟩ :=
    hGlobalSource M Rm Sreg It H hMH hdisorderRep Qcentre Qside hQside
  let CrepNN : ℝ≥0 := ⟨Crep1, hCrep1⟩
  have hCrepNN : (CrepNN : ℝ≥0∞) = ENNReal.ofReal Crep1 :=
    (ENNReal.ofReal_eq_coe_nnreal hCrep1).symm
  have hPadLevel : rootLevel (padE, selfShift) = (k : ℤ) - 1 := by
    rw [hrootLevel, hpad]
    norm_num
  have hPadCentre : rootCentre (padE, selfShift) = z := by
    rw [hrootCentre, hshift, smul_zero, add_zero, hqcenter]
  have hPadSide : rootSide (padE, selfShift) = (3 : ℝ) ^ (-((k : ℤ) - 1)) := by
    rw [hrootSide, hPadLevel]
  have hPadObservation : observationCentre (padE, selfShift) k0
      (Sum.inr (padE, selfShift)) = z := by
    rw [hObservationCentre]
    exact hPadCentre
  have hPadPrefix : ∀ N xi,
      prefixD N (padE, selfShift) k0 (Sum.inr (padE, selfShift)) xi =
        if (k : ℤ) - 1 + (k0 : ℤ) ≤ (N : ℤ) then
          ∑ j ∈ Finset.Icc ((k : ℤ) - 1 - (cbuf : ℤ)) ((k : ℤ) - 1 + (k0 : ℤ)),
            if 0 ≤ (N : ℤ) - j then
              (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • z) xi).toReal else 0
        else 0 := by
    intro N xi
    rw [hPrefixD, hPadLevel, hPadObservation]
  have hFinitePad : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      (k : ℤ) - 1 + (k0 : ℤ) ≤ (N : ℤ) →
        Draw N ((N : ℤ) - ((k : ℤ) - 1)).toNat (((3 : ℝ) ^ N) • z) xi ≠ ⊤ := by
    filter_upwards [hFiniteScoreGuard] with xi hxi
    intro N hN
    have h := hxi N (padE, selfShift) k0 (Sum.inr (padE, selfShift))
    rw [hPadLevel, hPadObservation] at h
    exact h hN ((k : ℤ) - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hNormPad : TendstoInMeasure P
      (fun n om => I.lam z ((3 : ℝ) ^ (-((k : ℤ) - 1))) (by positivity)
        (cutoffPositiveCoefficient M H (env 0 n om) (phi 0 n) z (by positivity))
        z ((3 : ℝ) ^ (-((k : ℤ) - 1))) sigma 2 /
          sN (phi 0 n) ((k : ℤ) - 1) z (env 0 n om)) atTop (ellLoLim 0 (padE, selfShift)) := by
    have hEq : (fun n om => ellLoN (phi 0 n) (padE, selfShift) (env 0 n om)) =
        (fun n om => I.lam z ((3 : ℝ) ^ (-((k : ℤ) - 1))) (by positivity)
          (cutoffPositiveCoefficient M H (env 0 n om) (phi 0 n) z (by positivity))
          z ((3 : ℝ) ^ (-((k : ℤ) - 1))) sigma 2 /
            sN (phi 0 n) ((k : ℤ) - 1) z (env 0 n om)) := by
      funext n om
      rw [hEllLoN, aux_lem_goodext_lower_coefficient_congr I M H
        (env 0 n om) (phi 0 n) _ _ _ _ _ (by positivity) hPadCentre hPadSide sigma,
        hPadLevel, hPadCentre]
    rw [← hEq]
    exact hEllLoLim 0 (padE, selfShift)
  obtain ⟨rhoPad, hRhoPad, hLowerPad⟩ := goodext_represented_padded_lower
    I M Rm H k k0 cbuf z s eps sigma cell (lambdaLim * (k0 : ℝ)) hs hcell.1
    eta hEta F Praw Rraw Draw Z rawGood hPrimitive
    (fun N xi => prefixD N (padE, selfShift) k0 (Sum.inr (padE, selfShift)) xi)
    hPadPrefix hFinitePad sN hsN P (phi 0) (hphi 0) (env 0) (henv_meas 0) (henv_law 0)
    (prefixDLim 0 (padE, selfShift) k0 (Sum.inr (padE, selfShift)))
    (ellLoLim 0 (padE, selfShift))
    (hPrefixDLim 0 (padE, selfShift) k0 (Sum.inr (padE, selfShift))) hNormPad
  have hFormBank (a : Fin 2) := goodext_represented_source_representative
    (chaosSampleLaw M).toMeasure P (env a) (henv_meas a) (henv_law a) (phi a)
    Qcentre Qside hQside alpha ⟨hbeta.1.trans hbetaLtAlpha, halpha.2⟩ S hS
    (fun n xi => cutoffPositiveCoefficient M H xi n Qcentre hQside) GN hGN
    (G a) (hGE a) Krep1 CrepNN hKrepMem1
    (fun n => (hKrepNorm1 n).trans_eq hCrepNN.symm) hRepSource1
  have hSourceBank0 := candidate_represented_source_bank
    (chaosSampleLaw M).toMeasure P (fun n => env 0 (rhoPad n))
    (fun n => henv_meas 0 (rhoPad n)) (fun n => henv_law 0 (rhoPad n))
    (fun n => phi 0 (rhoPad n))
    Qcentre Qside hQside alpha ⟨hbeta.1.trans hbetaLtAlpha, halpha.2⟩ S hS
    (fun n xi => cutoffPositiveCoefficient M H xi n Qcentre hQside) GN hGN
    (G 0) ((hGE 0).mono (fun om h => h.comp hRhoPad.tendsto_atTop))
    Krep1 CrepNN hKrepMem1
    (fun n => (hKrepNorm1 n).trans_eq hCrepNN.symm) hRepSource1
  have hContinuousForm1Event : ∀ᵐ om ∂P,
      ∀ fL2 : DomainL2 (centeredCube Qcentre Qside hQside),
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
          (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] fc) →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
          (G 1 om fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U ∧
          ∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0 := by
    filter_upwards [hFormBank 1] with om hBank
    intro fL2 hfL2
    obtain ⟨fc, hfc, _, _, hfcAE⟩ := hfL2
    obtain ⟨U, hUc, hUrep, hUzero, _⟩ := hBank fc hfc fL2 hfcAE
    exact ⟨U, hUc, hUrep, hUzero⟩
  have hRootTraceEvent := hRootTraceControls M Rm Sreg It H hMH hdisorderRoot
    Qcentre Qside hQside S hS (phi 1) Ω P (env 1) (henv_meas 1) (henv_law 1)
  have hLevelSelf : rootLevel qRoot = (k : ℤ) := by
    rw [hqRoot, hrootLevel, hfactor]
    simp only [Nat.cast_zero, sub_zero]
  have hSideSelf : rootSide qRoot = (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hrootSide, hLevelSelf]
  have hCentreSelf : rootCentre qRoot = z := by
    rw [hqRoot, hrootCentre, hshift, smul_zero, add_zero, hqcenter]
  have hNorm1 : TendstoInMeasure P
      (fun n om => I.Lam z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M H (env 1 n om) (phi 1 n) z (by positivity))
        z ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 /
          sN (phi 1 n) (k : ℤ) z (env 1 n om)) atTop (ellHiLim 1 qRoot) := by
    have hEq : (fun n om => ellHiN (phi 1 n) qRoot (env 1 n om)) =
        (fun n om => I.Lam z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
          (cutoffPositiveCoefficient M H (env 1 n om) (phi 1 n) z (by positivity))
          z ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 /
            sN (phi 1 n) (k : ℤ) z (env 1 n om)) := by
      funext n om
      rw [hEllHiN, aux_goodext_represented_local_trace_coefficient_congr I M H
        (env 1 n om) (phi 1 n) _ _ _ _ _ (by positivity) sigma ((beta - 1 / 2) / 4)
        hCentreSelf hSideSelf hsigma_eq, hLevelSelf, hCentreSelf]
    rw [← hEq]
    exact hEllHiLim 1 qRoot
  have hSharpEvent := hSharpTrace M Rm Sreg It H hMH hdisorderTrace
    Qcentre Qside hQside S hS k z (phi 1) (hphi 1) Ω P (env 1)
    (henv_meas 1) (henv_law 1) GN hGN (G 1) (hGE 1) (Form 1) (hE 1) (Gamma 1)
    hContinuousForm1Event (fun n om => sN (phi 1 n) (k : ℤ) z (env 1 n om))
    (sRef 1) (ellHiLim 1 qRoot) (hsRef 1) hNorm1 cell⁻¹ (inv_pos.mpr hcell.1)
  filter_upwards [hGcat, hCGEEvent, hGE0event, hGE1event, hSharpEvent,
      hRootTraceEvent, hContinuousForm1Event,
      hSourceBank0, hLowerPad, hsRef 0, hsRef 1, hGammaRecovery 0, hsRef_eq 0, hsRef_eq 1] with
    omega hGcat hCGE0 hGE0 hGE1 hSharp1 hRootTrace1 hContinuousForm1 hSourceBank0 hLowerPad hs0 hs1 hGamma0 hsEq0 hsEq1
  have hG0dom : ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
      G 0 omega f ∈ (Form 0 omega).domain := by
    apply aux_lem_goodext_limit_range_mem_domain
      S
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env 0 n omega) (phi 0 n)
        Qcentre hQside)
      (fun n => GN (phi 0 n) (env 0 n omega)) (G 0 omega) (Form 0 omega)
    · intro n f
      exact hGN (phi 0 n) (env 0 n omega) f
    · exact hGE0
    · exact hE 0 omega
  have hG1dom : ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
      G 1 omega f ∈ (Form 1 omega).domain := by
    apply aux_lem_goodext_limit_range_mem_domain
      S
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env 1 n omega) (phi 1 n)
        Qcentre hQside)
      (fun n => GN (phi 1 n) (env 1 n omega)) (G 1 omega) (Form 1 omega)
    · intro n f
      exact hGN (phi 1 n) (env 1 n omega) f
    · exact hGE1
    · exact hE 1 omega
  have hSourceTraceClass := aux_lem_goodext_source_trace_class
    Qcentre Qside hQside alpha beta hbetaLtAlpha
  show
      (let Q := centeredCube Qcentre Qside hQside
       let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
       let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
       let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
       let Good : Fin 2 → Set Ω := fun a =>
         {omega |
           (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
             ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
               prefixZLim a U D code omega < lambdaLim * (D : ℝ) ∧
               prefixDLim a U D code omega < lambdaLim * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
             cell ≤ ellLoLim a U omega ∧ ellHiLim a U omega ≤ cell⁻¹) ∧
           errLim a chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioLim a c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
       let L : ℝ := (3 : ℝ) ^ H1
       let unitClosed : Set (SpatialCoordinates d) :=
         closedCube (0 : SpatialCoordinates d) 1 one_pos
       let responseSet : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → Set ℝ :=
           fun r' z' b =>
             {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
               v ∈ (Form 1 omega).domain ∧
               ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
               ((v : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
               (∀ x ∈ frontier (Metric.ball z' (r' / 2)), V x = b x) ∧
               e = ((Gamma 1 omega).measure v
                 (Metric.ball z' (r' / 2))).toReal}
         let responseF : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → ℝ :=
           fun r' z' b => sInf (responseSet r' z' b)
         (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
           ∀ (fL2 : DomainL2 Q),
             ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
               (Q : Set (SpatialCoordinates d))] f) →
           let u := G 0 omega fL2
           let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
           ∃ U : SpatialCoordinates d → ℝ,
             ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
             ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
               (Q : Set (SpatialCoordinates d))] U) ∧
             (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
             _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
             ((omega ∈ Good 0 ∧ omega ∈ Good 1) →
               ∀ (zP : SpatialCoordinates d)
                 (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                 z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                 Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                 Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                 let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
                 let nuP : ℝ := ((Gamma 0 omega).measure u parentCell).toReal
                 ∃ cq : ℝ,
                   _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha unitClosed (fun x => U (z + r • x) - cq) ∧
                   _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) ≤
                     Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef 0 omega) ^ (-(1 : ℝ) / 2) *
                       Real.sqrt nuP +
                     Ctotal * r ^ (2 : ℝ) * (sRef 0 omega)⁻¹ * fsup ∧
                   (responseSet r z U).Nonempty ∧
                   IsGLB (responseSet r z U) (responseF r z U) ∧
                   responseF r z U ≤ Ctotal * (eRef 1 k / eRef 0 k) *
                     (nuP + (sRef 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
             (∃ K : ℝ, 0 ≤ K ∧
               ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
                 Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                   (responseSet r' z' U).Nonempty ∧
                   IsGLB (responseSet r' z' U) (responseF r' z' U) ∧
                   responseF r' z' U ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid))))
  intro Q r q Ctotal Good L unitClosed responseSet responseF f hf fL2 hfL2
  let fsup : ℝ := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
  have hfsup : 0 ≤ fsup := by
    apply Real.sSup_nonneg
    rintro v ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hfbdd : BddAbove {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|} := by
    obtain ⟨B, hB⟩ :=
      (centeredCube_isBounded Qcentre hQside).isCompact_closure.exists_bound_of_continuousOn
        hf.continuous.continuousOn
    refine ⟨B, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    simpa only [Real.norm_eq_abs] using hB x hx
  have hfbound : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |f x| ≤ fsup :=
    ae_restrict_of_forall_mem Q.isOpen.measurableSet
      (fun x hx => le_csSup hfbdd ⟨x, subset_closure hx, rfl⟩)
  obtain ⟨U, ns, UN, hns, hUc, hUr, hUb, hUh, hUniform, hUN⟩ :=
    hSourceBank0 f fsup hf hfsup hfbound fL2 hfL2
  refine ⟨U, hUc, hUr, hUb, hUh, ?_, ?_⟩
  · intro hGood zP idx hzP hPadParent hParentQ
    have hr : 0 < r := by dsimp only [r]; positivity
    have h3qQ : Metric.ball z (3 * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) :=
      Metric.ball_subset_closedBall.trans (hPadParent.trans hParentQ)
    have hqQ : q ⊆ (Q : Set (SpatialCoordinates d)) :=
      (Metric.ball_subset_ball (by linarith only [hr.le] : r / 2 ≤ 3 * r / 2)).trans h3qQ
    have hGoodCGE := hCGE0 ⟨hGood.1.1, hGood.1.2.1, ?_, hGood.1.2.2.2⟩
    swap
    ·
      rw [one_mul]
      exact hGood.1.2.2.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hcdet.le)
    obtain ⟨Ucge, hcgeC, hcgeRep, hcge0, hcgeHolder, ⟨cq, hcgeNorm⟩, hcgeHarm⟩ :=
      hGoodCGE.1 f hf fL2 hfL2
    have hSourceBound := goodext_source_bound_transport Q z r alpha _ (sRef 0 omega) fsup cq hr
      U Ucge (G 0 omega fL2) hcgeC hcgeRep hUc hUr hUh h3qQ hcgeNorm
    have hPadPower : (3 : ℝ) ^ (-((k : ℤ) - 1)) = 3 * r := by
      change (3 : ℝ) ^ (-((k : ℤ) - 1)) = 3 * (3 : ℝ) ^ (-(k : ℤ))
      rw [show -((k : ℤ) - 1) = (1 : ℤ) + -(k : ℤ) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    let rr : ℕ → ℕ := rhoPad ∘ ns
    have hrr : StrictMono rr := hRhoPad.comp hns
    have hSourcePos (n : ℕ) : 0 < sN (phi 0 (rr n)) (k : ℤ) z (env 0 (rr n) omega) := by
      rw [hsN]
      split_ifs
      · exact aux_in_deterministic_onestep_sref_pos M H _ _ _ _
      · norm_num
    have hPadLowerRaw := hns.tendsto_atTop.eventually
      (hLowerPad (hGood.1.2.1 (padE, selfShift)).1
        (hGood.1.1 (padE, selfShift) k0 le_rfl (Sum.inr (padE, selfShift))).2)
    have hPadLower : ∀ᶠ n in atTop,
        (cell / (2 * Real.exp (_root_.SubdiffusiveProcess.Model.tauSq M.P + 2 * (lambdaLim * (k0 : ℝ))))) *
          sN (phi 0 (rr n)) (k : ℤ) z (env 0 (rr n) omega) ≤
        I.lam z (3 * r) (by positivity)
          (cutoffPositiveCoefficient M H (env 0 (rr n) omega) (phi 0 (rr n)) z (by positivity))
          z (3 * r) sigma 2 := by
      filter_upwards [hPadLowerRaw] with n hn
      rw [aux_lem_goodext_lower_coefficient_congr I M H
        (env 0 (rhoPad (ns n)) omega) (phi 0 (rhoPad (ns n))) z z
        ((3 : ℝ) ^ (-((k : ℤ) - 1))) (3 * r) (by positivity)
        (show 0 < 3 * r by positivity) rfl hPadPower sigma] at hn
      exact hn
    let tauBudget : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P + 2 * (lambdaLim * (k0 : ℝ))
    let nu := (Gamma 0 omega).measure (G 0 omega fL2)
    have hParentOsc := goodext_padded_oscillation hd I Pin M H Qcentre Qside hQside S
      (fun n => env 0 (rr n) omega) (fun n => phi 0 (rr n)) GN hGN fL2 U UN
      (fun n => (hUN n).2) hUniform (G 0 omega) hUr z r hr h3qQ sigma cell tauBudget hsigma.1
      (by rw [hsigma_eq]; linarith only [hbeta.2]) hcell.1
      (fun n => sN (phi 0 (rr n)) (k : ℤ) z (env 0 (rr n) omega)) (sRef 0 omega)
      hSourcePos hs0.1 (hs0.2.comp hrr.tendsto_atTop) hPadLower (Form 0 omega) (Gamma 0 omega)
      (hG0dom fL2)
      (fun chi hc hcompact => (hGamma0 fL2 chi hc hcompact).comp hrr.tendsto_atTop)
      zP (L * r) hPadParent
    have htime : lambdaLim * (k0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by
      have hll : lambdaLim ≤ 1 := hThresholds.2.2.1.le.trans hThresholds.2.2.2.le
      have h := mul_le_mul_of_nonneg_right hll (Nat.cast_nonneg k0 : (0 : ℝ) ≤ k0)
      linarith only [h, (Nat.cast_nonneg cbuf : (0 : ℝ) ≤ cbuf)]
    have hCostBudget := hBudget ((k0 : ℝ) + (cbuf : ℝ))
      (_root_.SubdiffusiveProcess.Model.tauSq M.P) (lambdaLim * (k0 : ℝ))
      (by positivity) htauOne htime
    have hUqBoundary : ContinuousOn U (frontier q) :=
      hUc.mono (frontier_subset_closure.trans (closure_mono hqQ))
    have hTraceExtension : IsHolderOn beta (frontier q) U →
        ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ (Form 1 omega).domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
          (∀ x ∈ frontier q, V x = U x) ∧
          ((Gamma 1 omega).measure v q).toReal ≤
            CeTrace * (sRef 1 omega) * r ^ ((d : ℝ) - 2) *
              (r ^ beta * holderSeminorm beta (frontier q) U) ^ 2 := by
      intro hBetaTrace
      obtain ⟨v, V, hv, hVc, hVrep, hVtrace, hVe⟩ :=
        hSharp1 (hGood.2.2.1 qRoot).2 h3qQ U hUqBoundary hBetaTrace
      refine ⟨v, V, hv, hVc, hVrep, hVtrace, hVe.trans_eq ?_⟩
      dsimp only [CeTrace]
      ring
    have hRatioRef : sRef 1 omega / sRef 0 omega = eRef 1 k / eRef 0 k := by
      rw [hsEq1, hsEq0]
      exact aux_lem_goodext_sRef_ratio_eRef_ratio _ _ _
        (heRef_pos 0 k).ne' (Real.exp_pos _).ne'
    exact goodext_good_cell_final (Gamma 1 omega)
      (closure (Q : Set (SpatialCoordinates d))) z r alpha beta (sRef 0 omega) (sRef 1 omega)
      (nu (Metric.ball zP (L * r / 2))).toReal fsup _ (eRef 0 k) (eRef 1 k)
      Cbase Kp tauBudget ((k0 : ℝ) + (cbuf : ℝ)) CeTrace Ctotal hr hbetaLtAlpha.le
      (by linarith only [hbeta.1]) hs0.1 hs1.1.le ENNReal.toReal_nonneg hfsup hCbase hKp
      hCeTrace hCostBudget U hUqBoundary hSourceBound hParentOsc hTraceExtension hRatioRef
  · obtain ⟨ellRoot, hEllRoot⟩ := hside root0
    have hQScale : Qside = (3 : ℝ) ^ ellRoot := hRootCatalogue.2.symm.trans hEllRoot
    obtain ⟨seqRoot, hSeqRoot, ⟨ARoot⟩, hRootCells, hRootReg⟩ := hRootTrace1
    obtain ⟨Kgrid, hKgrid, hKgridCap⟩ := goodext_catalog_root_absolute_cap d hd M H Ω P
      (phi 1) (env 1) RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat
      thetaH1Cat (usrc 1) (srcRep 1) (ucell 1) Cext beta alpha etaCat t orders I Index
      (resp 1) (respLim 1) (constants 1) Gcat coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
      cellHolderKey Grid origin gridRoot gridKey (hRepEstimates 1)
      Qcentre Qside hQside hRootCatalogue omega hGcat
    exact goodext_arbitrary_cell_response hd I _X _Sob M H Qcentre Qside hQside S hS
      (fun n => env 1 (seqRoot n) omega) (fun n => phi 1 (seqRoot n)) ((hphi 1).comp hSeqRoot)
      tGrowth alpha beta etaCat etaGrid (by linarith only [halpha.1]) hbeta hbetaLtAlpha.le
      hrepB.2.2 hetaCatGrid ARoot hRootCells hRootReg GN hGN (G 1 omega)
      (hGE1.comp hSeqRoot.tendsto_atTop) (Form 1 omega) (hE 1 omega) hContinuousForm1
      (Gamma 1 omega) ellRoot hQScale Kgrid hKgrid
      (fun n k idx hk => hKgridCap (seqRoot n) k idx hk) U hUc hUh hUb

end SubdiffusiveProcess.Paper
end
