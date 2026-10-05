module

public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph
public import SubdiffusiveProcess.Paper.lem_weighted_cluster_form_bounds
public import SubdiffusiveProcess.Paper.lem_weighted_cluster_inverse_bounds
public import SubdiffusiveProcess.Paper.lem_weighted_cluster_limit_cluster
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.prop_regularity
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.conv_catalog_cutoffs
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.weighted_killed_form

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ## Helpers for `lem_weighted_cluster` (general candidate) -/

/-- Pointwise a.e. coefficient order `c ≤ K b` gives the response-energy order. -/
theorem aux_lem_weighted_cluster_responseForm_le_mul {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (c b : PositiveCoefficient Ω) (K : ℝ)
    (hcb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c.val x ≤ K * b.val x)
    (u : S.space) :
    responseForm S c u u ≤ K * responseForm S b u u := by
  change weightedGradientForm c.val (subspaceGradient S.space u) (subspaceGradient S.space u) ≤
    K * weightedGradientForm b.val (subspaceGradient S.space u) (subspaceGradient S.space u)
  exact weightedGradientForm_le_mul c b K hcb _

/-- Pointwise a.e. coefficient order `c ≤ K b` gives the energy-measure order on every set. -/
theorem aux_lem_weighted_cluster_withDensity_le_mul {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (c b s : SpatialCoordinates d → ℝ) (K : ℝ) (hK : 0 ≤ K) (hs : ∀ x, 0 ≤ s x)
    (hcb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c x ≤ K * b x)
    (A : Set (SpatialCoordinates d)) :
    ((volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (c y * s y))) A ≤
      ENNReal.ofReal K * ((volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (b y * s y))) A := by
  have hle : (volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (c y * s y)) ≤
      (volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
        (ENNReal.ofReal K • fun y => ENNReal.ofReal (b y * s y)) := by
    refine withDensity_mono ?_
    filter_upwards [hcb] with x hx
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul hK]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := mul_le_mul_of_nonneg_right hx (hs x)
    linarith [h1, show K * b x * s x = K * (b x * s x) by ring]
  rw [withDensity_smul' _ _ ENNReal.ofReal_ne_top] at hle
  have h2 := Measure.le_iff'.mp hle A
  simpa only [Measure.smul_apply, smul_eq_mul] using h2

/-- proved. -/
theorem aux_lem_weighted_cluster_weighted_cutoffs
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (S : ResponseSpace (centeredCube z r hr))
    (b c : ℕ → PositiveCoefficient (centeredCube z r hr)) (ι : ℕ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hbc : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (c n).val x ≤ K * (b (ι n)).val x)
    (hcutoffs : ∀ (K' O : Set (SpatialCoordinates d)),
      IsCompact K' → IsOpen O → K' ⊆ O →
        closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K' ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (b n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ,
            0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((b n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))) :
    ∀ (K' O : Set (SpatialCoordinates d)),
      IsCompact K' → IsOpen O → K' ⊆ O →
        closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K' ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (c n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ,
            0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((c n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)) := by
  intro K' O hK' hO hKO hcl
  obtain ⟨V, chi, chic, B, hVo, hKV, hVO, hB, h⟩ := hcutoffs K' O hK' hO hKO hcl
  refine ⟨V, fun n => chi (ι n), fun n => chic (ι n), K * B, hVo, hKV, hVO, mul_nonneg hK hB, ?_⟩
  intro n
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h (ι n)
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · exact (aux_lem_weighted_cluster_responseForm_le_mul S (c n) (b (ι n)) K (hbc n) _).trans
      (mul_le_mul_of_nonneg_left h6 hK)
  · intro x hx rr hr0 hr1
    have hle := aux_lem_weighted_cluster_withDensity_le_mul (Ω := centeredCube z r hr)
      (fun y => (c n).val y) (fun y => (b (ι n)).val y)
      (fun y => ∑ i : Fin d, ((chi (ι n)).val.2 i y) ^ 2) K hK
      (fun y => Finset.sum_nonneg fun i _ => sq_nonneg ((chi (ι n)).val.2 i y)) (hbc n)
      (Metric.ball x rr)
    have hfin : ENNReal.ofReal K * ENNReal.ofReal (B * rr ^ t) =
        ENNReal.ofReal ((K * B) * rr ^ t) := by
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      ring
    calc
      ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((c n).val y * ∑ i : Fin d, ((chi (ι n)).val.2 i y) ^ 2)))
          (Metric.ball x rr)
          ≤ ENNReal.ofReal K * ENNReal.ofReal (B * rr ^ t) :=
            hle.trans (mul_le_mul_right (h7 x hx rr hr0 hr1) (ENNReal.ofReal K))
      _ = ENNReal.ofReal ((K * B) * rr ^ t) := hfin

/-- proved. -/
theorem aux_lem_weighted_cluster_form_eq_zero_of_bilinear
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hF : ∀ w, F.energy w = limitFormEnergy G w)
    (u v : DomainL2 Q) (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (h0 : limitFormBilinear G u v = 0) : F.form u v = 0 := by
  unfold limitFormBilinear at h0
  rw [← hF (u + v), ← hF (u - v),
    F.energy_of_mem (F.domain.add_mem hu hv),
    F.energy_of_mem (F.domain.sub_mem hu hv)] at h0
  have h4 : (4 : EReal) = ((4 : ℝ) : EReal) := (EReal.coe_natCast (n := 4)).symm
  rw [h4, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_eq_zero] at h0
  have hA : F.form (u + v) (u + v) = F.form u u + 2 * F.form u v + F.form v v :=
    F.form_add_self hu hv
  have hB : F.form (u - v) (u - v) = F.form u u - 2 * F.form u v + F.form v v := by
    rw [F.form_sub_left hu hv (F.domain.sub_mem hu hv),
      F.form_sub_right hu hu hv, F.form_sub_right hv hu hv, F.form_symm v hv u hu]
    ring
  rw [hA, hB] at h0
  linarith

/-- proved. -/
theorem aux_lem_weighted_cluster_forms_of_limit
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hE : ∀ u, E.energy u = limitFormEnergy GE u) (hF : ∀ u, F.energy u = limitFormEnergy GF u)
    (c1 c2 : ℝ)
    (hdom : limitFormDomain GF = limitFormDomain GE)
    (hb : ∀ u ∈ limitFormDomain GE,
      (c1 : EReal) * limitFormEnergy GE u ≤ limitFormEnergy GF u ∧
      limitFormEnergy GF u ≤ (c2 : EReal) * limitFormEnergy GE u) :
    (∀ u, u ∈ F.domain ↔ u ∈ E.domain) ∧
    ∀ u ∈ E.domain, c1 * E.form u u ≤ F.form u u ∧ F.form u u ≤ c2 * E.form u u := by
  have hdomiff : ∀ u, u ∈ F.domain ↔ u ∈ E.domain := fun u => by
    rw [← F.energy_lt_top_iff, ← E.energy_lt_top_iff, hF, hE]
    exact Set.ext_iff.mp hdom u
  refine ⟨hdomiff, fun u hu => ?_⟩
  have hF' := (hdomiff u).2 hu
  have hu' : u ∈ limitFormDomain GE := by
    show limitFormEnergy GE u < ⊤
    rw [← hE]
    exact (E.energy_lt_top_iff u).2 hu
  obtain ⟨h1, h2⟩ := hb u hu'
  rw [← hE, ← hF, E.energy_of_mem hu, F.energy_of_mem hF', ← EReal.coe_mul] at h1
  rw [← hE, ← hF, E.energy_of_mem hu, F.energy_of_mem hF', ← EReal.coe_mul] at h2
  exact ⟨EReal.coe_le_coe_iff.mp h1, EReal.coe_le_coe_iff.mp h2⟩

/-- H1. A nonnegative real multiple of a finite nonnegative extended real is finite. -/
theorem aux_lem_weighted_cluster_ereal_mul_lt_top (C : ℝ) (_hC : 0 ≤ C) (x : EReal)
    (hx : x < ⊤) (hx0 : 0 ≤ x) : (C : EReal) * x < ⊤ := by
  have hx_ne_top : x ≠ ⊤ := lt_top_iff_ne_top.mp hx
  have hx_ne_bot : x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) hx0
  have hx_eq : (x.toReal : EReal) = x := EReal.coe_toReal hx_ne_top hx_ne_bot
  calc
    (C : EReal) * x = (C : EReal) * (x.toReal : EReal) := by rw [hx_eq]
    _ = ((C * x.toReal : ℝ) : EReal) := by rw [EReal.coe_mul]
    _ < ⊤ := EReal.coe_lt_top _

/-- H2. Undo a division by `c > 0` inside `EReal`. -/
theorem aux_lem_weighted_cluster_ereal_rescale (c : ℝ) (hc : 0 < c) (x y : EReal)
    (hx : 0 ≤ x) (h : x ≤ ((c⁻¹ : ℝ) : EReal) * y) : (c : EReal) * x ≤ y := by
  induction y using EReal.rec with
  | bot =>
      have hbot : ((c⁻¹ : ℝ) : EReal) * (⊥ : EReal) = (⊥ : EReal) :=
        EReal.coe_mul_bot_of_pos (inv_pos.mpr hc)
      have hx_bot : x = ⊥ := le_bot_iff.mp (h.trans_eq hbot)
      subst hx_bot
      exact absurd hx (not_le.mpr EReal.bot_lt_zero)
  | coe r =>
      induction x using EReal.rec with
      | bot =>
          exact absurd hx (not_le.mpr EReal.bot_lt_zero)
      | coe s =>
          have h_mul : ((c⁻¹ : ℝ) : EReal) * (r : EReal) = ((c⁻¹ * r : ℝ) : EReal) := by
            rw [EReal.coe_mul]
          rw [h_mul] at h
          have h_coe : (s : EReal) ≤ ((c⁻¹ * r : ℝ) : EReal) := h
          have h_le : s ≤ c⁻¹ * r := (EReal.coe_le_coe_iff.mp h_coe)
          have hc_mul : (c : EReal) * (s : EReal) = ((c * s : ℝ) : EReal) := by
            rw [EReal.coe_mul]
          rw [hc_mul]
          have h_mul_le : c * s ≤ r := by
            calc
              c * s ≤ c * (c⁻¹ * r) := mul_le_mul_of_nonneg_left h_le hc.le
              _ = (c * c⁻¹) * r := by ring
              _ = 1 * r := by field_simp [hc.ne.symm]
              _ = r := by simp
          exact (EReal.coe_le_coe_iff.mpr h_mul_le)
      | top =>
          exfalso
          have h' : (⊤ : EReal) ≤ ((c⁻¹ * r : ℝ) : EReal) := by
            rw [EReal.coe_mul]; exact h
          exact absurd h' (not_le.mpr (EReal.coe_lt_top _))
  | top =>
      exact le_top

/-- H3. One-sided Mosco transfer: `E_c ≤ C E_b` at every level, recovery sequences of `G1`
for `b` and the weak lower bound of `G2` for `c` give `E_{G2} ≤ C E_{G1}` on `D(G1)`. -/
theorem aux_lem_weighted_cluster_limit_upper
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (S : ResponseSpace Ω)
    (b c : ℕ → PositiveCoefficient Ω) (G1 G2 : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (C : ℝ) (_hC : 0 ≤ C)
    (hcmp : ∀ n (u : S.space), responseForm S (c n) u u ≤ C * responseForm S (b n) u u)
    (hrec1 : ∀ u ∈ limitFormDomain G1, ∃ w : ℕ → S.space,
      Tendsto (fun n => ((w n).val.1, ((responseForm S (b n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G1 u)))
    (hlow2 : ∀ (uN : ℕ → S.space) (u : DomainL2 Ω),
      (∀ f : DomainL2 Ω, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G2 u ≤
        liminf (fun n => ((responseForm S (c n) (uN n) (uN n) : ℝ) : EReal)) atTop) :
    ∀ u ∈ limitFormDomain G1, limitFormEnergy G2 u ≤ (C : EReal) * limitFormEnergy G1 u := by
  intro u hu
  rcases hrec1 u hu with ⟨w, hw⟩
  have hw_fst : Tendsto (fun n : ℕ => (w n).val.1) atTop (𝓝 u) :=
    Filter.Tendsto.fst_nhds hw
  have hw_weak : ∀ f : DomainL2 Ω,
      Tendsto (fun n : ℕ => inner ℝ f (w n).val.1) atTop (𝓝 (inner ℝ f u)) := by
    intro f
    exact Filter.Tendsto.inner (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f)) hw_fst
  have hlow := hlow2 w u hw_weak
  have hcmp_seq : ∀ n : ℕ,
      ((responseForm S (c n) (w n) (w n) : ℝ) : EReal) ≤ (C : EReal) * ((responseForm S (b n) (w n) (w n) : ℝ) : EReal) := by
    intro n
    have h := hcmp n (w n)
    -- h : responseForm S (c n) (w n) (w n) ≤ C * responseForm S (b n) (w n) (w n)   (in ℝ)
    -- need to lift to EReal
    exact_mod_cast h
  have h_liminf_le : liminf (fun n : ℕ => ((responseForm S (c n) (w n) (w n) : ℝ) : EReal)) atTop ≤
      liminf (fun n : ℕ => (C : EReal) * ((responseForm S (b n) (w n) (w n) : ℝ) : EReal)) atTop :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall hcmp_seq)
  have hw_snd : Tendsto (fun n : ℕ => ((responseForm S (b n) (w n) (w n) : ℝ) : EReal)) atTop
      (𝓝 (limitFormEnergy G1 u)) :=
    Filter.Tendsto.snd_nhds hw
  have h_liminf_eq : liminf (fun n : ℕ => (C : EReal) * ((responseForm S (b n) (w n) (w n) : ℝ) : EReal)) atTop =
      (C : EReal) * limitFormEnergy G1 u := by
    have h_tendsto_mul : Tendsto (fun n : ℕ => (C : EReal) * ((responseForm S (b n) (w n) (w n) : ℝ) : EReal)) atTop
        (𝓝 ((C : EReal) * limitFormEnergy G1 u)) :=
      EReal.Tendsto.const_mul hw_snd (Or.inl (EReal.coe_ne_bot C)) (Or.inl (EReal.coe_ne_top C))
    exact Filter.Tendsto.liminf_eq h_tendsto_mul
  rw [h_liminf_eq] at h_liminf_le
  exact le_trans hlow h_liminf_le



theorem aux_lem_weighted_cluster_limit_comparison
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (S : ResponseSpace Ω)
    (b c : ℕ → PositiveCoefficient Ω) (G1 G2 : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 ≤ c2)
    (hcmp : ∀ n (u : S.space), c1 * responseForm S (b n) u u ≤ responseForm S (c n) u u ∧
      responseForm S (c n) u u ≤ c2 * responseForm S (b n) u u)
    (hlow1 : ∀ (uN : ℕ → S.space) (u : DomainL2 Ω),
      (∀ f : DomainL2 Ω, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G1 u ≤
        liminf (fun n => ((responseForm S (b n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (hrec1 : ∀ u ∈ limitFormDomain G1, ∃ w : ℕ → S.space,
      Tendsto (fun n => ((w n).val.1, ((responseForm S (b n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G1 u)))
    (hlow2 : ∀ (uN : ℕ → S.space) (u : DomainL2 Ω),
      (∀ f : DomainL2 Ω, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G2 u ≤
        liminf (fun n => ((responseForm S (c n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (hrec2 : ∀ u ∈ limitFormDomain G2, ∃ w : ℕ → S.space,
      Tendsto (fun n => ((w n).val.1, ((responseForm S (c n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G2 u))) :
    limitFormDomain G2 = limitFormDomain G1 ∧
      ∀ u ∈ limitFormDomain G1,
        (c1 : EReal) * limitFormEnergy G1 u ≤ limitFormEnergy G2 u ∧
        limitFormEnergy G2 u ≤ (c2 : EReal) * limitFormEnergy G1 u := by
  have hc1inv : 0 ≤ c1⁻¹ := inv_nonneg.mpr hc1.le
  have hup1 : ∀ u ∈ limitFormDomain G1,
      limitFormEnergy G2 u ≤ (c2 : EReal) * limitFormEnergy G1 u :=
    aux_lem_weighted_cluster_limit_upper S b c G1 G2 c2 hc2 (fun n u => (hcmp n u).2) hrec1 hlow2
  have hup2 : ∀ u ∈ limitFormDomain G2,
      limitFormEnergy G1 u ≤ ((c1⁻¹ : ℝ) : EReal) * limitFormEnergy G2 u := by
    refine aux_lem_weighted_cluster_limit_upper S c b G2 G1 c1⁻¹ hc1inv (fun n u => ?_) hrec2 hlow1
    have h := (hcmp n u).1
    rw [inv_mul_eq_div, le_div_iff₀ hc1]
    linarith [h, mul_comm c1 (responseForm S (b n) u u)]
  have hsub12 : limitFormDomain G1 ⊆ limitFormDomain G2 := fun u hu =>
    lt_of_le_of_lt (hup1 u hu)
      (aux_lem_weighted_cluster_ereal_mul_lt_top c2 hc2 _ hu (limitFormEnergy_nonneg G1 u))
  have hsub21 : limitFormDomain G2 ⊆ limitFormDomain G1 := fun u hu =>
    lt_of_le_of_lt (hup2 u hu)
      (aux_lem_weighted_cluster_ereal_mul_lt_top c1⁻¹ hc1inv _ hu (limitFormEnergy_nonneg G2 u))
  refine ⟨Set.Subset.antisymm hsub21 hsub12, fun u hu => ⟨?_, hup1 u hu⟩⟩
  exact aux_lem_weighted_cluster_ereal_rescale c1 hc1 _ _ (limitFormEnergy_nonneg G1 u)
    (hup2 u (hsub12 hu))

/-- A2 (G9 pointwise). The weighted/unweighted comparison with arbitrary constants
bounding `rho` on the open cube (copy of `lem_weighted_cluster_form_bounds`). -/
theorem aux_lem_weighted_cluster_rho_form_bounds
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (S : ResponseSpace Ω)
    (a arho : PositiveCoefficient Ω) (A rho : SpatialCoordinates d → ℝ)
    (ha : a.val =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] A)
    (harho : arho.val =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      (fun x => rho x * A x))
    (c1 c2 : ℝ) (hc1 : 0 < c1)
    (hbd : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), c1 ≤ rho x ∧ rho x ≤ c2)
    (u : S.space) :
    c1 * responseForm S a u u ≤ responseForm S arho u u ∧
      responseForm S arho u u ≤ c2 * responseForm S a u u := by
  obtain ⟨c, hc, hcae⟩ := a.property
  have hlow : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      c1 * a.val x ≤ arho.val x := by
    filter_upwards [ha, harho, hcae, self_mem_ae_restrict Ω.isOpen.measurableSet]
      with x hA hArho hpos hx
    have hAnneg : 0 ≤ A x := by
      rw [← hA]
      exact hc.le.trans hpos
    rw [hA, hArho]
    exact mul_le_mul_of_nonneg_right (hbd x hx).1 hAnneg
  have hupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      arho.val x ≤ c2 * a.val x := by
    filter_upwards [ha, harho, hcae, self_mem_ae_restrict Ω.isOpen.measurableSet]
      with x hA hArho hpos hx
    have hAnneg : 0 ≤ A x := by
      rw [← hA]
      exact hc.le.trans hpos
    rw [hArho, hA]
    exact mul_le_mul_of_nonneg_right (hbd x hx).2 hAnneg
  constructor
  · change c1 * weightedGradientForm a.val
        (subspaceGradient S.space u) (subspaceGradient S.space u) ≤
      weightedGradientForm arho.val
        (subspaceGradient S.space u) (subspaceGradient S.space u)
    exact weightedGradientForm_mul_le a arho hc1 hlow (subspaceGradient S.space u)
  · change weightedGradientForm arho.val
        (subspaceGradient S.space u) (subspaceGradient S.space u) ≤
      c2 * weightedGradientForm a.val
        (subspaceGradient S.space u) (subspaceGradient S.space u)
    exact weightedGradientForm_le_mul arho a c2 hupp (subspaceGradient S.space u)

/-- H1. An upper form bound gives an energy-norm bound with constant `max 1 c`. -/
theorem aux_lem_weighted_cluster_energyNormSq_le_max {X : Type*} [MeasurableSpace X]
    {m : Measure X} (E F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (c : ℝ) (u : Lp ℝ 2 m)
    (hu : u ∈ E.domain) (hle : F.form u u ≤ c * E.form u u) :
    F.energyNormSq u ≤ max 1 c * E.energyNormSq u := by
  have hc_max : c ≤ max 1 c := le_max_right _ _
  have h1_max : (1 : ℝ) ≤ max 1 c := le_max_left _ _
  have hpos : 0 ≤ E.form u u := E.form_nonneg u hu
  have hpos_norm : 0 ≤ ‖u‖ ^ 2 := pow_two_nonneg _
  have hform : F.form u u ≤ max 1 c * E.form u u := by
    have h : c * E.form u u ≤ max 1 c * E.form u u :=
      mul_le_mul_of_nonneg_right hc_max hpos
    nlinarith
  have hnorm : ‖u‖ ^ 2 ≤ max 1 c * ‖u‖ ^ 2 := by
    have h : (1 : ℝ) * ‖u‖ ^ 2 ≤ max 1 c * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h1_max hpos_norm
    nlinarith
  rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq]
  nlinarith

/-- A7 (G5). Core and regularity transfer along an equal domain and an upper bound. -/
theorem aux_lem_weighted_cluster_core_transfer
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    (E F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (U : Set X) (hU : IsOpen U) (hmU : m Uᶜ = 0)
    (hdom : ∀ u, u ∈ F.domain ↔ u ∈ E.domain) (c : ℝ)
    (hle : ∀ u ∈ E.domain, F.form u u ≤ c * E.form u u)
    (hcore : ∃ C : Set (Lp ℝ 2 m), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E U C) :
    (∃ C : Set (Lp ℝ 2 m), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F U C) ∧ _root_.SubdiffusiveProcess.DirichletForm.IsRegular F := by
  rcases hcore with ⟨C, hC⟩
  have hpos_max : 0 < max 1 c := by
    have h1pos : (0 : ℝ) < 1 := by norm_num
    have h1le : (1 : ℝ) ≤ max 1 c := le_max_left _ _
    linarith
  have hmem : ∀ u ∈ C, F.MemCoreOn U u := by
    intro u huC
    have hE := hC.memCoreOn u huC
    have huE : u ∈ E.domain := hE.mem_domain
    have huF : u ∈ F.domain := (hdom u).mpr huE
    exact ⟨huF, hE.hasCoreRep⟩
  have hdense : ∀ u ∈ F.domain, ∀ ε : ℝ, 0 < ε → ∃ w ∈ C, F.energyNormSq (u - w) < ε := by
    intro u huF ε hε
    have huE : u ∈ E.domain := (hdom u).mp huF
    have hεdiv : 0 < ε / max 1 c := div_pos hε hpos_max
    obtain ⟨w, hwC, hw⟩ := hC.denseEnergy u huE (ε / max 1 c) hεdiv
    have hwE : w ∈ E.domain := (hC.memCoreOn w hwC).mem_domain
    have hsubE : u - w ∈ E.domain := E.domain.sub_mem huE hwE
    have hle' : F.form (u - w) (u - w) ≤ c * E.form (u - w) (u - w) := hle (u - w) hsubE
    have hH1 : F.energyNormSq (u - w) ≤ max 1 c * E.energyNormSq (u - w) :=
      aux_lem_weighted_cluster_energyNormSq_le_max E F c (u - w) hsubE hle'
    have hcalc : max 1 c * E.energyNormSq (u - w) < max 1 c * (ε / max 1 c) :=
      mul_lt_mul_of_pos_left hw hpos_max
    have hcalc2 : max 1 c * (ε / max 1 c) = ε := by
      field_simp [hpos_max.ne.symm]
    refine ⟨w, hwC, ?_⟩
    calc
      F.energyNormSq (u - w) ≤ max 1 c * E.energyNormSq (u - w) := hH1
      _ < max 1 c * (ε / max 1 c) := hcalc
      _ = ε := hcalc2
  have hdenseUniform : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      ∀ ε : ℝ, 0 < ε → ∃ w ∈ C, ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ⇑w =ᵐ[m] g ∧ ∀ x : X, |g x - f x| < ε := hC.denseUniform
  have hcoreF : _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F U C :=
    { memCoreOn := hmem
      denseEnergy := hdense
      denseUniform := hdenseUniform }
  have hisReg : _root_.SubdiffusiveProcess.DirichletForm.IsRegular F :=
    ⟨U, hU, hmU, C, hcoreF⟩
  exact ⟨⟨C, hcoreF⟩, hisReg⟩

/-- A8 (G7). Killed-domain transfer from `E` to an equivalent `F`. -/
theorem aux_lem_weighted_cluster_killed_domain_transfer
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U)
    (EU FU : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (U : Set (SpatialCoordinates d))))
    (EV FV : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (V : Set (SpatialCoordinates d))))
    (hdomU : ∀ w, w ∈ FU.domain ↔ w ∈ EU.domain) (hdomV : ∀ w, w ∈ FV.domain ↔ w ∈ EV.domain)
    (c1 c2 : ℝ) (hc1 : 0 < c1) (_hc2 : 0 ≤ c2)
    (hboundU : ∀ w ∈ EU.domain, c1 * EU.form w w ≤ FU.form w w ∧ FU.form w w ≤ c2 * EU.form w w)
    (hE : ∃ D : Submodule ℝ (DomainL2 U),
      _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EU (V : Set (SpatialCoordinates d)) D ∧
      (∀ w : DomainL2 U, w ∈ D ↔ ∃ u : DomainL2 V, u ∈ EV.domain ∧ zeroExtensionLp hVU u = w)) :
    ∃ D : Submodule ℝ (DomainL2 U),
      _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain FU (V : Set (SpatialCoordinates d)) D ∧
      (∀ w : DomainL2 U, w ∈ D ↔ ∃ u : DomainL2 V, u ∈ FV.domain ∧ zeroExtensionLp hVU u = w) := by
  rcases hE with ⟨D, hDkilled, hDiff⟩
  have hpos_max_c2 : 0 < max 1 c2 := by
    have h1pos : (0 : ℝ) < 1 := by norm_num
    have h1le : (1 : ℝ) ≤ max 1 c2 := le_max_left _ _
    linarith
  have hle_lower : ∀ w ∈ EU.domain, EU.form w w ≤ c1⁻¹ * FU.form w w := by
    intro w hw
    have hbound := hboundU w hw
    have h := hbound.1
    calc
      EU.form w w = (c1⁻¹ * c1) * EU.form w w := by field_simp [hc1.ne.symm]
      _ = c1⁻¹ * (c1 * EU.form w w) := by ring
      _ ≤ c1⁻¹ * FU.form w w := mul_le_mul_of_nonneg_left h (by positivity)
  have hle_upper : ∀ w ∈ EU.domain, FU.form w w ≤ c2 * EU.form w w := by
    intro w hw
    exact (hboundU w hw).2
  have hle_domain : D ≤ FU.domain := by
    intro w hw
    have hwEU : w ∈ EU.domain := hDkilled.le_domain hw
    exact (hdomU w).mpr hwEU
  have hmemCoreOn_mem : ∀ w, FU.MemCoreOn (V : Set (SpatialCoordinates d)) w → w ∈ D := by
    intro w hwF
    have hwEU : w ∈ EU.domain := (hdomU w).mp hwF.mem_domain
    exact hDkilled.memCoreOn_mem w ⟨hwEU, hwF.hasCoreRep⟩
  have happrox : ∀ w ∈ D, ∀ ε : ℝ, 0 < ε →
      ∃ w' : Lp ℝ 2 (volume.restrict (U : Set (SpatialCoordinates d))),
        FU.MemCoreOn (V : Set (SpatialCoordinates d)) w' ∧
        FU.energyNormSq (w - w') < ε := by
    intro w hwD ε hε
    have hεdiv : 0 < ε / max 1 c2 := div_pos hε hpos_max_c2
    obtain ⟨w', hw'core, hw'⟩ := hDkilled.approx w hwD (ε / max 1 c2) hεdiv
    have hw'EU : w' ∈ EU.domain := hw'core.mem_domain
    have hw'FU : w' ∈ FU.domain := (hdomU w').mpr hw'EU
    have hwEU : w ∈ EU.domain := (hdomU w).mp (hle_domain hwD)
    have hsub : w - w' ∈ EU.domain := EU.domain.sub_mem hwEU hw'EU
    have hle'_upper : FU.form (w - w') (w - w') ≤ c2 * EU.form (w - w') (w - w') :=
      hle_upper (w - w') hsub
    have hH1 : FU.energyNormSq (w - w') ≤ max 1 c2 * EU.energyNormSq (w - w') :=
      aux_lem_weighted_cluster_energyNormSq_le_max EU FU c2 (w - w') hsub hle'_upper
    have hcalc : max 1 c2 * EU.energyNormSq (w - w') < max 1 c2 * (ε / max 1 c2) :=
      mul_lt_mul_of_pos_left hw' hpos_max_c2
    have hcalc2 : max 1 c2 * (ε / max 1 c2) = ε := by
      field_simp [hpos_max_c2.ne.symm]
    refine ⟨w', ⟨hw'FU, hw'core.hasCoreRep⟩, ?_⟩
    calc
      FU.energyNormSq (w - w') ≤ max 1 c2 * EU.energyNormSq (w - w') := hH1
      _ < max 1 c2 * (ε / max 1 c2) := hcalc
      _ = ε := hcalc2
  have hisClosed : ∀ (u : ℕ → Lp ℝ 2 (volume.restrict (U : Set (SpatialCoordinates d))))
      (w : Lp ℝ 2 (volume.restrict (U : Set (SpatialCoordinates d)))),
      (∀ n, u n ∈ D) → w ∈ FU.domain →
      Tendsto (fun n => FU.energyNormSq (u n - w)) atTop (𝓝 0) → w ∈ D := by
    intro u_seq w hu_seqD hwFU hw_tendsto
    have hwEU : w ∈ EU.domain := (hdomU w).mp hwFU
    have h_tendsto_max : Tendsto (fun n => (max 1 c1⁻¹) * FU.energyNormSq (u_seq n - w)) atTop
        (𝓝 ((max 1 c1⁻¹) * 0)) :=
      Filter.Tendsto.const_mul (max 1 c1⁻¹) hw_tendsto
    have h_tendsto_max_zero : Tendsto (fun n => (max 1 c1⁻¹) * FU.energyNormSq (u_seq n - w)) atTop
        (𝓝 0) := by
      simpa [mul_zero] using h_tendsto_max
    have h_nonneg : ∀ n, 0 ≤ EU.energyNormSq (u_seq n - w) := by
      intro n
      have hu_n_EU : u_seq n ∈ EU.domain := hDkilled.le_domain (hu_seqD n)
      have hw_sub_EU : w ∈ EU.domain := hwEU
      have hsub : u_seq n - w ∈ EU.domain := EU.domain.sub_mem hu_n_EU hw_sub_EU
      exact EU.energyNormSq_nonneg hsub
    have h_bound : ∀ n, EU.energyNormSq (u_seq n - w) ≤ (max 1 c1⁻¹) * FU.energyNormSq (u_seq n - w) := by
      intro n
      have hu_n_FU : u_seq n ∈ FU.domain := (hdomU (u_seq n)).mpr (hDkilled.le_domain (hu_seqD n))
      have hw_sub_FU : w ∈ FU.domain := hwFU
      have hsub_FU : u_seq n - w ∈ FU.domain := FU.domain.sub_mem hu_n_FU hw_sub_FU
      have hle_sub : EU.form (u_seq n - w) (u_seq n - w) ≤ c1⁻¹ * FU.form (u_seq n - w) (u_seq n - w) :=
        hle_lower (u_seq n - w) ((hdomU (u_seq n - w)).mp hsub_FU)
      exact aux_lem_weighted_cluster_energyNormSq_le_max FU EU c1⁻¹ (u_seq n - w) hsub_FU hle_sub
    have h_tendsto_EU : Tendsto (fun n => EU.energyNormSq (u_seq n - w)) atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_bound h_tendsto_max_zero
    exact hDkilled.isClosed u_seq w hu_seqD hwEU h_tendsto_EU
  have hiff : ∀ w : DomainL2 U, w ∈ D ↔ ∃ u : DomainL2 V, u ∈ FV.domain ∧ zeroExtensionLp hVU u = w := by
    intro w
    rw [hDiff w]
    constructor
    · rintro ⟨u, huEV, hu_eq⟩
      refine ⟨u, (hdomV u).mpr huEV, hu_eq⟩
    · rintro ⟨u, huFV, hu_eq⟩
      refine ⟨u, (hdomV u).mp huFV, hu_eq⟩
  refine ⟨D, ?_, hiff⟩
  exact
    { le_domain := hle_domain
      memCoreOn_mem := hmemCoreOn_mem
      approx := happrox
      isClosed := hisClosed }

/-- Consumer: regularity and the killed domain pass from `E` to an equivalent `F`
(the shape the parent's clauses (iii) and the cross clause use). -/
theorem aux_lem_weighted_cluster_equiv_regular_killed
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U)
    (EU FU : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (U : Set (SpatialCoordinates d))))
    (EV FV : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (V : Set (SpatialCoordinates d))))
    (hdomU : ∀ w, w ∈ FU.domain ↔ w ∈ EU.domain) (hdomV : ∀ w, w ∈ FV.domain ↔ w ∈ EV.domain)
    (c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 ≤ c2)
    (hboundU : ∀ w ∈ EU.domain, c1 * EU.form w w ≤ FU.form w w ∧ FU.form w w ≤ c2 * EU.form w w)
    (hcore : ∃ C : Set (DomainL2 U),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EU (U : Set (SpatialCoordinates d)) C)
    (hE : ∃ D : Submodule ℝ (DomainL2 U),
      _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EU (V : Set (SpatialCoordinates d)) D ∧
      (∀ w : DomainL2 U, w ∈ D ↔ ∃ u : DomainL2 V, u ∈ EV.domain ∧ zeroExtensionLp hVU u = w)) :
    _root_.SubdiffusiveProcess.DirichletForm.IsRegular FU ∧
      ∃ D : Submodule ℝ (DomainL2 U),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain FU (V : Set (SpatialCoordinates d)) D ∧
        (∀ w : DomainL2 U, w ∈ D ↔ ∃ u : DomainL2 V, u ∈ FV.domain ∧ zeroExtensionLp hVU u = w) := by
  have hmU : (volume.restrict (U : Set (SpatialCoordinates d))) (U : Set (SpatialCoordinates d))ᶜ = 0 := by
    rw [Measure.restrict_apply' U.isOpen.measurableSet]
    simp
  exact ⟨(aux_lem_weighted_cluster_core_transfer EU FU (U : Set (SpatialCoordinates d)) U.isOpen hmU
      hdomU c2 (fun w hw => (hboundU w hw).2) hcore).2,
    aux_lem_weighted_cluster_killed_domain_transfer hVU EU FU EV FV hdomU hdomV c1 c2 hc1 hc2
      hboundU hE⟩

/-- The coefficient order `arho ≤ c₂ a` a.e. from `rho ≤ c₂` on the cube
(the upper half of the A2 argument). -/
theorem aux_lem_weighted_cluster_coeff_le {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a arho : PositiveCoefficient Ω) (A rho : SpatialCoordinates d → ℝ)
    (ha : a.val =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] A)
    (harho : arho.val =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      (fun x => rho x * A x))
    (c2 : ℝ) (hbd : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), rho x ≤ c2) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), arho.val x ≤ c2 * a.val x := by
  obtain ⟨c, hc, hcae⟩ := a.property
  filter_upwards [ha, harho, hcae, self_mem_ae_restrict Ω.isOpen.measurableSet]
    with x hA hArho hpos hx
  have hAnneg : 0 ≤ A x := by
    rw [← hA]
    exact hc.le.trans hpos
  rw [hArho, hA]
  exact mul_le_mul_of_nonneg_right (hbd x hx) hAnneg

/-- Coercivity for `a` plus `lo · E_a ≤ E_arho` gives coercivity for `arho` with `K / lo`. -/
theorem aux_lem_weighted_cluster_weighted_coercive {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a arho : PositiveCoefficient Ω) (lo K : ℝ) (hlo : 0 < lo)
    (hK : 0 ≤ K) (N : DomainL2 Ω → ℝ) (u : S.space)
    (hcoer : N u.val.1 ≤ K * responseForm S a u u)
    (hform : lo * responseForm S a u u ≤ responseForm S arho u u) :
    N u.val.1 ≤ (K / lo) * responseForm S arho u u := by
  have h1 : responseForm S a u u ≤ responseForm S arho u u / lo := by
    rw [le_div_iff₀ hlo]
    linarith [mul_comm lo (responseForm S a u u)]
  calc N u.val.1 ≤ K * responseForm S a u u := hcoer
    _ ≤ K * (responseForm S arho u u / lo) := mul_le_mul_of_nonneg_left h1 hK
    _ = (K / lo) * responseForm S arho u u := by ring

/-- G8 lower half: zero extension does not increase the Mosco-limit energy
(`prop_killed_consistency_zero_extension` for limit forms given by `limitFormEnergy`). -/
theorem aux_lem_weighted_cluster_lower_zeroExt
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
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Eq : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))))
    (hEQ : ∀ u, EQ.energy u = limitFormEnergy GQ u)
    (hEq : ∀ u, Eq.energy u = limitFormEnergy Gq u)
    (hQlower : ∀ (vN : ℕ → SQ.space) (v : DomainL2 (centeredCube zQ R hR0)),
      (∀ f : DomainL2 (centeredCube zQ R hR0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      limitFormEnergy GQ v ≤
        liminf (fun n => ((responseForm SQ (aQ n) (vN n) (vN n) : ℝ) : EReal)) atTop)
    (hqrec : ∀ v ∈ limitFormDomain Gq, ∃ vN : ℕ → Sq.space,
      Tendsto (fun n => ((vN n).val.1,
        ((responseForm Sq (aq n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (v, limitFormEnergy Gq v))) :
    ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ Eq.domain →
      (EQ.energy (zeroExtensionLp hqQ u) : EReal) ≤ (Eq.energy u : EReal) := by
  intro u hu
  have hlower' : ∀ (vN : ℕ → SQ.space) (v : DomainL2 (centeredCube zQ R hR0)),
      (∀ f : DomainL2 (centeredCube zQ R hR0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      (EQ.energy v : EReal) ≤
        liminf (fun n => (responseForm SQ (aQ n) (vN n) (vN n) : EReal)) atTop := by
    intro vN v hv
    rw [hEQ]
    exact hQlower vN v hv
  have hrec' : ∀ v ∈ Eq.domain, ∃ vN : ℕ → Sq.space,
      Tendsto (fun n => ((vN n).val.1,
        (responseForm Sq (aq n) (vN n) (vN n) : EReal))) atTop
        (𝓝 (v, (Eq.energy v : EReal))) := by
    intro v hv
    have hv' : v ∈ limitFormDomain Gq := by
      show limitFormEnergy Gq v < ⊤
      rw [← hEq]
      exact (Eq.energy_lt_top_iff v).2 hv
    rw [hEq]
    exact hqrec v hv'
  obtain ⟨_, _, _, _, h4⟩ := prop_killed_consistency_zero_extension d hd zQ zq R r hR0 hr0 hqQ
    SQ Sq hSQ hSq aQ aq hcoeff EQ Eq hlower' hrec' u hu
  exact h4

/-! ## Estimates A5, A6, G8-upper -/

section WCChain

open scoped Distributions

/-- Dominated convergence to zero in `L²`. -/
theorem aux_lem_weighted_cluster_eLpNorm_two_tendsto_zero_of_dominated
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {g : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hg : MemLp g 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, |F n x| ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hI : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) atTop (𝓝 0) := by
    have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2 h2t hg.eLpNorm_lt_top
    have h := tendsto_lintegral_of_dominated_convergence'
      (F := fun n x => ‖F n x‖ₑ ^ (2 : ℝ≥0∞).toReal) (f := fun _ => 0)
      (fun x => ‖g x‖ₑ ^ (2 : ℝ≥0∞).toReal)
      (fun n => (hF n).enorm.pow_const _)
      (fun n => by
        filter_upwards [hbound n] with x hx
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _)))
      hfin.ne
      (by
        filter_upwards [hlim] with x hx
        have h0 : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
          simpa using! (continuous_enorm.tendsto (0 : ℝ)).comp hx
        have h1 := (ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp h0
        rw [htr] at h1 ⊢
        simpa [ENNReal.zero_rpow_of_pos] using! h1)
    simpa using h
  have h := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp hI
  have hz : (0 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) = 0 := by
    rw [htr]; exact ENNReal.zero_rpow_of_pos (by norm_num)
  rw [hz] at h
  refine h.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2t (hF n)]

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- A smooth function vanishing at `0` composed with a test function is a test function. -/
def aux_lem_weighted_cluster_compTest (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨Φ ∘ φ, hΦ.comp φ.contDiff, φ.hasCompactSupport.comp_left hΦ0,
    (tsupport_comp_subset hΦ0 _).trans φ.tsupport_subset⟩

theorem aux_lem_weighted_cluster_compTest_apply (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hΦ0 : Φ 0 = 0) (φ : 𝓓(Ω, ℝ)) (x : SpatialCoordinates d) :
    aux_lem_weighted_cluster_compTest Φ hΦ hΦ0 φ x = Φ (φ x) := rfl

theorem aux_lem_weighted_cluster_fderiv_compTest (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hΦ0 : Φ 0 = 0) (φ : 𝓓(Ω, ℝ)) (x v : SpatialCoordinates d) :
    fderiv ℝ (aux_lem_weighted_cluster_compTest Φ hΦ hΦ0 φ) x v =
      deriv Φ (φ x) * fderiv ℝ φ x v := by
  have hΦd : HasDerivAt Φ (deriv Φ (φ x)) (φ x) :=
    ((hΦ.differentiable (by simp)) (φ x)).hasDerivAt
  have hφd : HasFDerivAt (φ : SpatialCoordinates d → ℝ) (fderiv ℝ φ x) x :=
    ((φ.contDiff.differentiable (by simp)) x).hasFDerivAt
  have h := hΦd.comp_hasFDerivAt x hφd
  change fderiv ℝ (Φ ∘ (φ : SpatialCoordinates d → ℝ)) x v = _
  rw [h.fderiv]
  simp [smul_eq_mul]

/-- **Smooth chain rule on the killed graph.** -/
theorem aux_lem_weighted_cluster_killed_comp_smooth
    (w : SobolevData Ω) (hw : w ∈ killedSobolevGraph Ω)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    (L : ℝ) (hL : ∀ s, |deriv Φ s| ≤ L) :
    ∃ p : SobolevData Ω, p ∈ killedSobolevGraph Ω ∧
      (p.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
          (fun x => Φ ((w.1 : SpatialCoordinates d → ℝ) x)) ∧
      ∀ i : Fin d, (p.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
          (fun x => deriv Φ ((w.1 : SpatialCoordinates d → ℝ) x) *
            (w.2 i : SpatialCoordinates d → ℝ) x) := by
  classical
  set μ := volume.restrict (Ω : Set (SpatialCoordinates d)) with hμ
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hΦdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hΦ'cont : Continuous (deriv Φ) := hΦ.continuous_deriv (by simp)
  have hLip : LipschitzWith (Real.toNNReal L) Φ := by
    refine lipschitzWith_of_nnnorm_deriv_le hΦdiff (fun s => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hL0]
    exact hL s
  -- the gradient candidate
  have hgradMem : ∀ i : Fin d, MemLp (fun x => deriv Φ ((w.1 : SpatialCoordinates d → ℝ) x) *
      (w.2 i : SpatialCoordinates d → ℝ) x) 2 μ := by
    intro i
    refine MemLp.of_le ((Lp.memLp (w.2 i)).const_mul L)
      ((hΦ'cont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.1)).mul
        (Lp.aestronglyMeasurable (w.2 i))) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hL0]
    exact mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)
  let p : SobolevData Ω := (hLip.compLp hΦ0 w.1, fun i => (hgradMem i).toLp _)
  refine ⟨p, ?_, hLip.coeFn_compLp hΦ0 w.1, fun i => (hgradMem i).coeFn_toLp⟩
  -- approximate `w` by the smooth graph
  have hw' : w ∈ closure ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) :
      Set (SobolevData Ω)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hw
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.1 hw'
  choose φ hφ using fun n => LinearMap.mem_range.1 (hxmem n)
  have hφeq : ∀ n, smoothSobolevData (φ n) = x n := hφ
  have hfst : Tendsto (fun n => testL2 (φ n)) atTop (𝓝 w.1) := by
    have h := ((continuous_fst).tendsto w).comp hxlim
    refine h.congr (fun n => ?_)
    simp [← hφeq n, smoothSobolevData]
  have hsnd : ∀ i : Fin d, Tendsto (fun n => testPartialL2 (φ n) i) atTop (𝓝 (w.2 i)) := by
    intro i
    have h := (((continuous_apply i).comp continuous_snd).tendsto w).comp hxlim
    refine h.congr (fun n => ?_)
    simp [← hφeq n, smoothSobolevData]
  -- an a.e.-convergent subsequence
  have hmeas : TendstoInMeasure μ (fun n => (testL2 (φ n) : SpatialCoordinates d → ℝ)) atTop
      (w.1 : SpatialCoordinates d → ℝ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ?_
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hfst
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  let ψ : ℕ → 𝓓(Ω, ℝ) := fun k => aux_lem_weighted_cluster_compTest Φ hΦ hΦ0 (φ (ns k))
  have hψmem : ∀ k, smoothSobolevData (ψ k) ∈
      ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) : Set (SobolevData Ω)) :=
    fun k => ⟨ψ k, rfl⟩
  have hp_closure : p ∈ closure ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) :
      Set (SobolevData Ω)) := by
    refine mem_closure_of_tendsto (f := fun k => smoothSobolevData (ψ k)) (b := atTop) ?_
      (Eventually.of_forall hψmem)
    refine Tendsto.prodMk_nhds ?_ (tendsto_pi_nhds.2 fun i => ?_)
    · -- value component
      have hcont := (hLip.continuous_compLp (μ := μ) (p := 2) hΦ0).tendsto w.1
      have h := hcont.comp (hfst.comp hns.tendsto_atTop)
      refine h.congr (fun k => ?_)
      apply Lp.ext
      filter_upwards [hLip.coeFn_compLp hΦ0 (testL2 (φ (ns k))), testL2_coeFn (φ (ns k)),
        testL2_coeFn (ψ k)] with y h1 h2 h3
      simp only [Function.comp_apply] at h1 ⊢
      change _ = (testL2 (ψ k) : SpatialCoordinates d → ℝ) y
      rw [h1, h3, h2]
      rfl
    · -- gradient component
      change Tendsto (fun k => testPartialL2 (ψ k) i) atTop (𝓝 ((hgradMem i).toLp _))
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      -- split into a Lipschitz term and a dominated term
      set D1 : ℕ → SpatialCoordinates d → ℝ := fun k y =>
        deriv Φ ((testL2 (φ (ns k)) : SpatialCoordinates d → ℝ) y) *
          ((testPartialL2 (φ (ns k)) i : SpatialCoordinates d → ℝ) y -
            (w.2 i : SpatialCoordinates d → ℝ) y) with hD1
      set D2 : ℕ → SpatialCoordinates d → ℝ := fun k y =>
        (deriv Φ ((testL2 (φ (ns k)) : SpatialCoordinates d → ℝ) y) -
            deriv Φ ((w.1 : SpatialCoordinates d → ℝ) y)) *
          (w.2 i : SpatialCoordinates d → ℝ) y with hD2
      have hD1meas : ∀ k, AEStronglyMeasurable (D1 k) μ := fun k =>
        (hΦ'cont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).mul
          ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
      have hD2meas : ∀ k, AEStronglyMeasurable (D2 k) μ := fun k =>
        ((hΦ'cont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).sub
          (hΦ'cont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))).mul
          (Lp.aestronglyMeasurable _)
      have hsplit : ∀ k, (testPartialL2 (ψ k) i : SpatialCoordinates d → ℝ) -
          ((hgradMem i).toLp _ : SpatialCoordinates d → ℝ) =ᵐ[μ] D1 k + D2 k := by
        intro k
        filter_upwards [testPartialL2_coeFn (ψ k) i, testPartialL2_coeFn (φ (ns k)) i,
          testL2_coeFn (φ (ns k)), (hgradMem i).coeFn_toLp] with y h1 h2 h3 h4
        rw [Pi.sub_apply, h1, h4, aux_lem_weighted_cluster_fderiv_compTest, Pi.add_apply,
          hD1, hD2]
        simp only
        rw [h2, h3]
        ring
      have hD1lim : Tendsto (fun k => eLpNorm (D1 k) 2 μ) atTop (𝓝 0) := by
        have hbase := ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 (hsnd i)).comp
          hns.tendsto_atTop
        have hmul := ENNReal.Tendsto.const_mul hbase (Or.inr ENNReal.ofReal_ne_top)
          (a := ENNReal.ofReal L)
        rw [mul_zero] at hmul
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
          (fun k => zero_le) (fun k => ?_)
        show eLpNorm (D1 k) 2 μ ≤ ENNReal.ofReal L *
          eLpNorm ((testPartialL2 (φ (ns k)) i : SpatialCoordinates d → ℝ) -
            (w.2 i : SpatialCoordinates d → ℝ)) 2 μ
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hD1meas k) (Eventually.of_forall fun y => ?_) 2
        simp only [hD1, Pi.sub_apply, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)
      have hD2lim : Tendsto (fun k => eLpNorm (D2 k) 2 μ) atTop (𝓝 0) := by
        refine aux_lem_weighted_cluster_eLpNorm_two_tendsto_zero_of_dominated hD2meas
          (g := fun y => (2 * L) * |(w.2 i : SpatialCoordinates d → ℝ) y|)
          ((Lp.memLp (w.2 i)).abs.const_mul _) (fun k => Eventually.of_forall fun y => ?_) ?_
        · simp only [hD2, abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine (abs_sub _ _).trans ?_
          linarith [hL ((testL2 (φ (ns k)) : SpatialCoordinates d → ℝ) y),
            hL ((w.1 : SpatialCoordinates d → ℝ) y)]
        · filter_upwards [hae] with y hy
          have h1 : Tendsto (fun k => deriv Φ ((testL2 (φ (ns k)) : SpatialCoordinates d → ℝ) y) -
              deriv Φ ((w.1 : SpatialCoordinates d → ℝ) y)) atTop (𝓝 0) := by
            have := ((hΦ'cont.tendsto _).comp hy).sub_const
              (deriv Φ ((w.1 : SpatialCoordinates d → ℝ) y))
            simpa using this
          simpa [hD2] using h1.mul_const ((w.2 i : SpatialCoordinates d → ℝ) y)
      have hsum : Tendsto (fun k => eLpNorm (D1 k) 2 μ + eLpNorm (D2 k) 2 μ) atTop (𝓝 0) := by
        simpa using hD1lim.add hD2lim
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun k => zero_le) (fun k => ?_)
      rw [eLpNorm_congr_ae (hsplit k)]
      exact eLpNorm_add_le (by norm_num)
  rw [← Submodule.topologicalClosure_coe] at hp_closure
  exact hp_closure

/-- Energy does not increase when the gradient is multiplied by a factor of modulus `≤ 1`. -/
theorem aux_lem_weighted_cluster_responseForm_le_of_grad_factor (S : ResponseSpace Ω)
    (a : PositiveCoefficient Ω) (x y : S.space) (m : SpatialCoordinates d → ℝ)
    (hm : ∀ z, |m z| ≤ 1)
    (hgrad : ∀ i : Fin d, (((y : SobolevData Ω).2 i : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun z => m z * ((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z) :
    responseForm S a y y ≤ responseForm S a x x := by
  rw [responseForm_apply, responseForm_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨c, hc, ha⟩ := a.property
  have hsq : Integrable (fun z => ((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z *
      ((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    simpa [pow_two] using (Lp.memLp ((x : SobolevData Ω).2 i)).integrable_sq
  have hint := hsq.mul_of_top_right (Lp.memLp a.val)
  refine integral_mono_of_nonneg ?_ hint ?_
  · filter_upwards [ha] with z hz
    exact mul_nonneg (hc.le.trans hz) (mul_self_nonneg _)
  · filter_upwards [ha, hgrad i] with z hz hy
    change a.val z * (_ * _) ≤ a.val z * (_ * _)
    rw [hy]
    refine mul_le_mul_of_nonneg_left ?_ (hc.le.trans hz)
    have hm2 : m z * m z ≤ 1 := by
      rw [← abs_mul_abs_self (m z)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hm z)).trans (hm z)
    have hx2 := mul_self_nonneg (((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z)
    calc m z * ((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z *
          (m z * ((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z)
        = (m z * m z) * (((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z *
          ((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z) := by ring
      _ ≤ 1 * (((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z *
          ((x : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) z) :=
        mul_le_mul_of_nonneg_right hm2 hx2
      _ = _ := one_mul _


end WCChain

/-- A smooth normal contraction uniformly `δ`-close to the unit truncation:
`Φ(s) = ∫₀ˢ η` for a bump `η` equal to `1` on `[a, 1-a]` and supported in `(0, 1)`. -/
theorem aux_lem_weighted_cluster_exists_smooth_truncation (δ : ℝ) (hδ : 0 < δ) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ Φ 0 = 0 ∧ (∀ s, |deriv Φ s| ≤ 1) ∧
      ∀ s, |Φ s - _root_.SubdiffusiveProcess.DirichletForm.unitTruncation s| ≤ δ := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min (δ / 2) (1 / 4) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact lt_min (by linarith) (by norm_num)
  have ha4 : a ≤ 1 / 4 := by rw [ha]; exact min_le_right _ _
  have haδ : 2 * a ≤ δ := by
    have : a ≤ δ / 2 := by rw [ha]; exact min_le_left _ _
    linarith
  let η : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2 - a, 1 / 2, by linarith, by linarith⟩
  have hηc : Continuous η := η.continuous
  have hderiv : deriv (fun s => ∫ t in (0 : ℝ)..s, η t) = η :=
    funext fun s => Continuous.deriv_integral _ hηc 0 s
  have hdiff : Differentiable ℝ (fun s => ∫ t in (0 : ℝ)..s, η t) := fun s =>
    (hηc.integral_hasStrictDerivAt 0 s).hasDerivAt.differentiableAt
  have hsmooth : ContDiff ℝ ∞ (fun s => ∫ t in (0 : ℝ)..s, η t) := by
    rw [contDiff_infty_iff_deriv, hderiv]
    exact ⟨hdiff, η.contDiff⟩
  have hη1 : ∀ t : ℝ, a ≤ t → t ≤ 1 - a → η t = 1 := by
    intro t h1 h2
    apply η.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |t - 1 / 2| ≤ 1 / 2 - a
    rw [abs_le]
    constructor <;> linarith
  have hη0 : ∀ t : ℝ, (t ≤ 0 ∨ 1 ≤ t) → η t = 0 := by
    intro t ht
    apply η.zero_of_le_dist
    rw [Real.dist_eq]
    show (1 / 2 : ℝ) ≤ |t - 1 / 2|
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hηnn : ∀ t : ℝ, 0 ≤ η t := fun t => η.nonneg
  have hηle : ∀ t : ℝ, η t ≤ 1 := fun t => η.le_one
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun t => η t) volume x y :=
    fun x y => hηc.intervalIntegrable x y
  have hint1 : ∀ x y : ℝ, IntervalIntegrable (fun t => 1 - η t) volume x y :=
    fun x y => (continuous_const.sub hηc).intervalIntegrable x y
  have hm : ∫ t in (0 : ℝ)..1, (1 - η t) ≤ 2 * a := by
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (hint1 0 a) (hint1 a 1)
    have hsplit2 :=
      intervalIntegral.integral_add_adjacent_intervals (hint1 a (1 - a)) (hint1 (1 - a) 1)
    have hmid : ∫ t in a..(1 - a), (1 - η t) = 0 := by
      have heq : Set.EqOn (fun t => 1 - η t) (fun _ => (0 : ℝ)) (Set.uIcc a (1 - a)) := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        simp only [hη1 t ht.1 ht.2, sub_self]
      rw [intervalIntegral.integral_congr heq]
      simp
    have hleft : ∫ t in (0 : ℝ)..a, (1 - η t) ≤ a := by
      have h := intervalIntegral.integral_mono_on ha0.le (hint1 0 a)
        (intervalIntegrable_const (c := (1 : ℝ)))
        (fun t _ => by linarith [hηnn t])
      simpa using h
    have hright : ∫ t in (1 - a)..1, (1 - η t) ≤ a := by
      have h := intervalIntegral.integral_mono_on (by linarith) (hint1 (1 - a) 1)
        (intervalIntegrable_const (c := (1 : ℝ)))
        (fun t _ => by linarith [hηnn t])
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
      linarith
    linarith
  have hId : ∀ s : ℝ, ∫ t in (0 : ℝ)..s, η t = s - ∫ t in (0 : ℝ)..s, (1 - η t) := by
    intro s
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint 0 s)]
    simp
  refine ⟨fun s => ∫ t in (0 : ℝ)..s, η t, hsmooth, by simp, fun s => ?_, fun s => ?_⟩
  · rw [hderiv, abs_of_nonneg (hηnn s)]
    exact hηle s
  · show |(∫ t in (0 : ℝ)..s, η t) - _root_.SubdiffusiveProcess.DirichletForm.unitTruncation s| ≤ δ
    rcases le_total s 0 with hs | hs
    · have h0 : ∫ t in (0 : ℝ)..s, η t = 0 := by
        have heq : Set.EqOn (fun t => η t) (fun _ => (0 : ℝ)) (Set.uIcc 0 s) := by
          intro t ht
          rw [Set.uIcc_of_ge hs] at ht
          exact hη0 t (Or.inl ht.2)
        rw [intervalIntegral.integral_congr heq]
        simp
      have hT : _root_.SubdiffusiveProcess.DirichletForm.unitTruncation s = 0 := by
        unfold _root_.SubdiffusiveProcess.DirichletForm.unitTruncation
        rw [min_eq_left (by linarith), max_eq_right hs]
      rw [h0, hT, sub_zero, abs_zero]
      exact hδ.le
    · rcases le_total s 1 with hs1 | hs1
      · have hT : _root_.SubdiffusiveProcess.DirichletForm.unitTruncation s = s := by
          unfold _root_.SubdiffusiveProcess.DirichletForm.unitTruncation
          rw [min_eq_left hs1, max_eq_left hs]
        have hnn : 0 ≤ ∫ t in (0 : ℝ)..s, (1 - η t) :=
          intervalIntegral.integral_nonneg hs (fun t _ => by linarith [hηle t])
        have hle : ∫ t in (0 : ℝ)..s, (1 - η t) ≤ ∫ t in (0 : ℝ)..1, (1 - η t) :=
          intervalIntegral.integral_mono_interval le_rfl hs hs1
            (Eventually.of_forall fun t => by
              show (0 : ℝ) ≤ 1 - η t
              linarith [hηle t]) (hint1 0 1)
        rw [hId s, hT, abs_le]
        constructor <;> linarith
      · have hT : _root_.SubdiffusiveProcess.DirichletForm.unitTruncation s = 1 := by
          unfold _root_.SubdiffusiveProcess.DirichletForm.unitTruncation
          rw [min_eq_right hs1, max_eq_left zero_le_one]
        have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 s)
        have htail : ∫ t in (1 : ℝ)..s, η t = 0 := by
          have heq : Set.EqOn (fun t => η t) (fun _ => (0 : ℝ)) (Set.uIcc 1 s) := by
            intro t ht
            rw [Set.uIcc_of_le hs1] at ht
            exact hη0 t (Or.inr ht.1)
          rw [intervalIntegral.integral_congr heq]
          simp
        have h1 := hId 1
        have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, (1 - η t) :=
          intervalIntegral.integral_nonneg zero_le_one (fun t _ => by linarith [hηle t])
        rw [← hsplit, htail, add_zero, h1, hT, abs_le]
        constructor <;> linarith

/-- A5 (G3c). Approximate unit truncation inside the killed response space without
increasing the finite-level energy (smooth normal contractions `Φ` with `|Φ'| ≤ 1`, `Φ(0)=0`,
uniformly close to the unit truncation, composed with the killed element). -/
theorem aux_lem_weighted_cluster_unitTruncation_approx
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (S : ResponseSpace Ω)
    (hS : S.space = killedSobolevGraph Ω)
    (hfin : volume (Ω : Set (SpatialCoordinates d)) ≠ ⊤)
    (a : PositiveCoefficient Ω) (u : S.space) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : S.space,
      ‖v.val.1 - _root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_unitTruncation.compLp
          _root_.SubdiffusiveProcess.DirichletForm.unitTruncation_zero u.val.1‖ ≤ ε ∧
      responseForm S a v v ≤ responseForm S a u u := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.2 hfin
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (measureUnivNNReal
      (volume.restrict (Ω : Set (SpatialCoordinates d))) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hδ : 0 < ε / (M + 1) := div_pos hε (by linarith)
  have hob := aux_lem_weighted_cluster_exists_smooth_truncation (ε / (M + 1)) hδ
  obtain ⟨Φ, hΦ, hΦ0, hΦ', hΦT⟩ := hob
  have hu : (u : SobolevData Ω) ∈ killedSobolevGraph Ω := by
    rw [← hS]; exact u.property
  have hob2 := aux_lem_weighted_cluster_killed_comp_smooth (u : SobolevData Ω) hu Φ hΦ hΦ0 1 hΦ'
  obtain ⟨p, hp, hp1, hp2⟩ := hob2
  have hpS : p ∈ S.space := by rw [hS]; exact hp
  refine ⟨⟨p, hpS⟩, ?_, ?_⟩
  · have hbound : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
        ‖(p.1 - _root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_unitTruncation.compLp
          _root_.SubdiffusiveProcess.DirichletForm.unitTruncation_zero u.val.1 : DomainL2 Ω) x‖ ≤ ε / (M + 1) := by
      filter_upwards [Lp.coeFn_sub p.1 (_root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_unitTruncation.compLp
          _root_.SubdiffusiveProcess.DirichletForm.unitTruncation_zero u.val.1), hp1,
        _root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_unitTruncation.coeFn_compLp
          _root_.SubdiffusiveProcess.DirichletForm.unitTruncation_zero u.val.1] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]
      exact hΦT _
    have hle := Lp.norm_le_of_ae_bound hδ.le hbound
    refine hle.trans ?_
    rw [← hM]
    have hfrac : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    calc M * (ε / (M + 1)) = ε * (M / (M + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hfrac hε.le
      _ = ε := mul_one ε
  · exact aux_lem_weighted_cluster_responseForm_le_of_grad_factor S a u ⟨p, hpS⟩
      (fun z => deriv Φ (((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) z))
      (fun z => hΦ' _) hp2

/-- The closed form of the dual energy of a symmetric positive injective `G` with a
spectral square root whose range is the dual-energy domain (the construction of
`prop_killed_inverse_dirichlet_form`, without the contraction part). -/
theorem aux_lem_weighted_cluster_closedForm_of_root
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hinj : Function.Injective G)
    (hroot : ∃ Rroot : DomainL2 Q →L[ℝ] DomainL2 Q,
      (∀ x y : DomainL2 Q, inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (Rroot x)) ∧
      Rroot.comp Rroot = G ∧ limitFormDomain G = Set.range Rroot) :
    ∃ E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))),
      ∀ w : DomainL2 Q, E.energy w = limitFormEnergy G w := by
  classical
  obtain ⟨R, hRsym, _hRpos, hcomp, hdomain⟩ := hroot
  have hRinj : Function.Injective R :=
    aux_prop_killed_inverse_dirichlet_form_root_injective G R hcomp hinj
  let D : Submodule ℝ (DomainL2 Q) := LinearMap.range (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q)
  have hDset : (D : Set (DomainL2 Q)) = Set.range R := by
    ext u
    constructor
    · intro hu
      exact (LinearMap.mem_range.mp hu)
    · rintro ⟨u, rfl⟩
      exact LinearMap.mem_range_self (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q) u
  have hD_mem_iff (u : DomainL2 Q) : u ∈ D ↔ u ∈ Set.range R := by
    change u ∈ (D : Set (DomainL2 Q)) ↔ u ∈ Set.range R
    rw [hDset]
  let e : DomainL2 Q ≃ₗ[ℝ] D :=
    LinearEquiv.ofInjective (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q) hRinj
  let rootInv : DomainL2 Q → DomainL2 Q := fun u =>
    if hu : u ∈ D then e.symm ⟨u, hu⟩ else 0
  have hrootInv_apply (u : DomainL2 Q) : rootInv (R u) = u := by
    dsimp [rootInv]
    rw [dite_eq_left (show R u ∈ D by exact LinearMap.mem_range_self (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q) u)]
    have heq :
        (⟨R u, (show R u ∈ D by exact LinearMap.mem_range_self (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q) u)⟩ : D) = e u := by
      apply Subtype.ext
      exact (LinearEquiv.ofInjective_apply
        (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q) u).symm
    rw [heq, e.symm_apply_apply]
  have hR_rootInv (u : DomainL2 Q) (hu : u ∈ D) : R (rootInv u) = u := by
    change (e (rootInv u) : DomainL2 Q) = u
    have he : (e (rootInv u) : DomainL2 Q) = u := by
      dsimp [rootInv]
      rw [dite_eq_left hu]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨u, hu⟩)
    exact he
  have hrootInv_add {u v : DomainL2 Q} (hu : u ∈ D) (hv : v ∈ D) :
      rootInv (u + v) = rootInv u + rootInv v := by
    apply hRinj
    calc
      R (rootInv (u + v)) = u + v := hR_rootInv (u + v) (D.add_mem hu hv)
      _ = R (rootInv u) + R (rootInv v) := by rw [hR_rootInv u hu, hR_rootInv v hv]
      _ = R (rootInv u + rootInv v) := by rw [R.map_add]
  have hrootInv_smul (c : ℝ) {u : DomainL2 Q} (hu : u ∈ D) :
      rootInv (c • u) = c • rootInv u := by
    apply hRinj
    calc
      R (rootInv (c • u)) = c • u := hR_rootInv (c • u) (D.smul_mem c hu)
      _ = c • R (rootInv u) := by rw [hR_rootInv u hu]
      _ = R (c • rootInv u) := by rw [R.map_smul]
  have henergy_root (u : DomainL2 Q) :
      (⨆ f : DomainL2 Q,
        ((2 * inner ℝ f (R u) - inner ℝ f (G f) : ℝ) : EReal)) =
        ((inner ℝ u u : ℝ) : EReal) :=
    aux_prop_killed_inverse_dirichlet_form_dual_energy_root_range G R hsym hRsym hcomp hRinj u
  have hrootInv_neg {u : DomainL2 Q} (hu : u ∈ D) :
      rootInv (-u) = -rootInv u := by
    simpa using hrootInv_smul (-1) hu
  have hrootInv_sub {u v : DomainL2 Q} (hu : u ∈ D) (hv : v ∈ D) :
      rootInv (u - v) = rootInv u - rootInv v := by
    rw [sub_eq_add_neg, hrootInv_add hu (D.neg_mem hv), hrootInv_neg hv]
    simp only [sub_eq_add_neg]
  let form : DomainL2 Q → DomainL2 Q → ℝ := fun u v =>
    inner ℝ (rootInv u) (rootInv v)
  have hform_symm : ∀ u ∈ D, ∀ v ∈ D, form u v = form v u := by
    intro u _ v _
    exact real_inner_comm _ _
  have hform_add_left : ∀ u ∈ D, ∀ v ∈ D, ∀ w ∈ D,
      form (u + v) w = form u w + form v w := by
    intro u hu v hv w _
    dsimp [form]
    rw [hrootInv_add hu hv, inner_add_left]
  have hform_smul_left : ∀ c : ℝ, ∀ u ∈ D, ∀ v ∈ D,
      form (c • u) v = c * form u v := by
    intro c u hu v _
    dsimp [form]
    rw [hrootInv_smul c hu, real_inner_smul_left]
  have hform_nonneg : ∀ u ∈ D, 0 ≤ form u u := by
    intro u _
    exact real_inner_self_nonneg
  have hDdense : Dense (D : Set (DomainL2 Q)) := by
    dsimp [D]
    exact aux_prop_killed_inverse_dirichlet_form_root_dense R hRsym hRinj
  have hform_eq_limit {u : DomainL2 Q} (hu : u ∈ D) :
      ((form u u : ℝ) : EReal) = limitFormEnergy G u := by
    have huR : u = R (rootInv u) := (hR_rootInv u hu).symm
    rw [huR]
    dsimp [form]
    rw [hrootInv_apply]
    simpa [limitFormEnergy] using (henergy_root (rootInv u)).symm
  let EClosed : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    { domain := D
      form := form
      denseDomain := hDdense
      form_symm := hform_symm
      form_add_left := hform_add_left
      form_smul_left := hform_smul_left
      form_nonneg := hform_nonneg
      complete := by
        intro u hu hc
        let f : ℕ → DomainL2 Q := fun n => rootInv (u n)
        have hfC : CauchySeq f := by
          rw [Metric.cauchySeq_iff]
          intro ε hε
          obtain ⟨N, hN⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
          refine ⟨N, fun p hp q hq => ?_⟩
          have hformdiff : form (u p - u q) (u p - u q) =
              ‖f p - f q‖ ^ 2 := by
            dsimp [form, f]
            rw [hrootInv_sub (hu p) (hu q), real_inner_self_eq_norm_sq]
          have hsmall := hN p hp q hq
          rw [hformdiff] at hsmall
          rw [dist_eq_norm]
          nlinarith [norm_nonneg (f p - f q)]
        obtain ⟨f_lim, hf_lim⟩ := cauchySeq_tendsto_of_complete hfC
        let z : DomainL2 Q := R f_lim
        have hz : z ∈ D := by
          dsimp [z, D]
          exact LinearMap.mem_range_self (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q) f_lim
        refine ⟨z, hz, ?_⟩
        have hfdiff : Tendsto (fun n => f n - f_lim) atTop (𝓝 0) := by
          simpa using hf_lim.sub
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => f_lim) atTop (𝓝 f_lim))
        have hnorm_f : Tendsto (fun n => ‖f n - f_lim‖ ^ 2) atTop (𝓝 0) := by
          have h := (tendsto_norm.comp hfdiff).pow 2
          simpa using h
        have hnorm_R : Tendsto
            (fun n => ‖R (f n - f_lim)‖ ^ 2) atTop (𝓝 0) := by
          have hRzero : Tendsto (fun n => R (f n - f_lim)) atTop (𝓝 0) := by
            simpa only [Function.comp_apply, map_zero] using!
              R.continuous.continuousAt.tendsto.comp hfdiff
          have h := (tendsto_norm.comp hRzero).pow 2
          simpa using h
        have hsum : Tendsto
            (fun n => ‖f n - f_lim‖ ^ 2 + ‖R (f n - f_lim)‖ ^ 2)
            atTop (𝓝 0) := by simpa only [add_zero] using hnorm_f.add hnorm_R
        apply hsum.congr'
        filter_upwards [] with n
        have hdiff : u n - z = R (f n - f_lim) := by
          dsimp [f, z]
          calc
            u n - R f_lim = R (rootInv (u n)) - R f_lim := by
              exact congrArg (fun x => x - R f_lim) (hR_rootInv (u n) (hu n)).symm
            _ = R (rootInv (u n) - f_lim) := (R.map_sub _ _).symm
            _ = R (rootInv (u n) - f_lim) := rfl
        rw [hdiff]
        dsimp [form]
        rw [hrootInv_apply, real_inner_self_eq_norm_sq]
      }
  have henergy_off {u : DomainL2 Q} (hu : u ∉ D) :
      limitFormEnergy G u = (⊤ : EReal) := by
    have hu_not : u ∉ limitFormDomain G := by
      intro huG
      apply hu
      apply (hD_mem_iff u).2
      rw [← hdomain]
      exact huG
    have hnotlt : ¬ limitFormEnergy G u < (⊤ : EReal) := by
      simpa only [limitFormDomain, mem_ofPred_eq] using hu_not
    exact le_antisymm le_top (not_lt.mp hnotlt)
  refine ⟨EClosed, fun u => ?_⟩
  by_cases hu : u ∈ D
  · rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem EClosed hu, hform_eq_limit hu]
  · rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_notMem EClosed hu, henergy_off hu]

/-- A6 (G3d). The dual-energy Dirichlet form from Mosco + approximate truncation
(variant of `prop_killed_inverse_dirichlet_form`, `hcontract` replaced by `happrox`). -/
theorem aux_lem_weighted_cluster_dirichlet_form
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (_hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (hinj : Function.Injective G)
    (hroot : ∃ Rroot : DomainL2 Q →L[ℝ] DomainL2 Q,
      (∀ x y : DomainL2 Q, inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (Rroot x)) ∧
      Rroot.comp Rroot = G ∧ limitFormDomain G = Set.range Rroot)
    (hmosco :
      (∀ (uN : ℕ → S.space) (u : DomainL2 Q),
          (∀ f : DomainL2 Q,
            Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
          limitFormEnergy G u ≤
            liminf (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
        (∀ u ∈ limitFormDomain G, ∃ w : ℕ → S.space,
          Tendsto (fun n => ((w n).val.1,
            ((responseForm S (a n) (w n) (w n) : ℝ) : EReal))) atTop
            (𝓝 (u, limitFormEnergy G u))))
    (happrox : ∀ (n : ℕ) (u : S.space) (ε : ℝ), 0 < ε → ∃ v : S.space,
      ‖v.val.1 - _root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_unitTruncation.compLp
          _root_.SubdiffusiveProcess.DirichletForm.unitTruncation_zero u.val.1‖ ≤ ε ∧
      responseForm S (a n) v v ≤ responseForm S (a n) u u) :
    ∃ EForm : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))),
      ∀ w : DomainL2 Q, EForm.toClosedForm.energy w = limitFormEnergy G w := by
  have hob := aux_lem_weighted_cluster_closedForm_of_root G hsym hinj hroot
  obtain ⟨E, hE⟩ := hob
  have hmarkov : ∀ u ∈ E.domain, ∀ v : DomainL2 Q,
      (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        fun x => _root_.SubdiffusiveProcess.DirichletForm.unitTruncation (u x)) →
      v ∈ E.domain ∧ E.form v v ≤ E.form u u := by
    intro u hu v hv
    let TLp : DomainL2 Q → DomainL2 Q :=
      _root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_unitTruncation.compLp _root_.SubdiffusiveProcess.DirichletForm.unitTruncation_zero
    have hv_eq : v = TLp u := by
      apply Lp.ext
      exact hv.trans (_root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_unitTruncation.coeFn_compLp
        _root_.SubdiffusiveProcess.DirichletForm.unitTruncation_zero u).symm
    have hu_lim : u ∈ limitFormDomain G := by
      show limitFormEnergy G u < ⊤
      rw [← hE u]
      exact (E.energy_lt_top_iff u).2 hu
    obtain ⟨w, hw⟩ := hmosco.2 u hu_lim
    have hwstrong : Tendsto (fun n => (w n).val.1) atTop (𝓝 u) :=
      (continuous_fst.tendsto (u, limitFormEnergy G u)).comp hw
    have hTLp_cont : Continuous TLp :=
      _root_.SubdiffusiveProcess.DirichletForm.lipschitzWith_unitTruncation.continuous_compLp
        _root_.SubdiffusiveProcess.DirichletForm.unitTruncation_zero
    have hcomp : Tendsto (fun n => TLp ((w n).val.1)) atTop (𝓝 (TLp u)) :=
      hTLp_cont.continuousAt.tendsto.comp hwstrong
    have hpos' : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    choose v' hv'_near hv'_le using fun n => happrox n (w n) (1 / ((n : ℝ) + 1)) (hpos' n)
    have hv'strong : Tendsto (fun n => (v' n).val.1) atTop (𝓝 (TLp u)) := by
      have hd : Tendsto (fun n => (v' n).val.1 - TLp ((w n).val.1)) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => hv'_near n) tendsto_one_div_add_atTop_nhds_zero_nat
      have := hd.add hcomp
      simpa only [sub_add_cancel, zero_add] using this
    have hv'weak : ∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (v' n).val.1) atTop (𝓝 (inner ℝ f (TLp u))) := by
      intro f
      exact tendsto_const_nhds.inner hv'strong
    have hlow := hmosco.1 (fun n => v' n) (TLp u) hv'weak
    have hwenergy : Tendsto
        (fun n => ((responseForm S (a n) (w n) (w n) : ℝ) : EReal)) atTop
          (𝓝 (limitFormEnergy G u)) :=
      (continuous_snd.tendsto (u, limitFormEnergy G u)).comp hw
    have hliminf_le :
        liminf (fun n => ((responseForm S (a n) (v' n) (v' n) : ℝ) : EReal)) atTop ≤
          liminf (fun n => ((responseForm S (a n) (w n) (w n) : ℝ) : EReal)) atTop := by
      refine Filter.liminf_le_liminf
        (h := ?_)
        (Filter.isBoundedUnder_of_eventually_ge (a := (0 : EReal)) <| by
          filter_upwards [] with n
          exact (EReal.coe_nonneg).mpr (responseForm_nonneg S (a n) (v' n)))
        hwenergy.isCoboundedUnder_ge
      filter_upwards [] with n
      exact_mod_cast hv'_le n
    have hfinite_le : limitFormEnergy G (TLp u) ≤ limitFormEnergy G u :=
      hlow.trans (hliminf_le.trans_eq hwenergy.liminf_eq)
    have hEle : E.energy (TLp u) ≤ E.energy u := by
      rw [hE, hE]
      exact hfinite_le
    have hTdom : TLp u ∈ E.domain :=
      E.mem_domain_of_energy_lt_top (hEle.trans_lt ((E.energy_lt_top_iff u).2 hu))
    refine ⟨hv_eq ▸ hTdom, ?_⟩
    rw [hv_eq]
    have h2 := hEle
    rw [E.energy_of_mem hTdom, E.energy_of_mem hu] at h2
    exact EReal.coe_le_coe_iff.mp h2
  exact ⟨{ toClosedForm := E, markov := hmarkov }, hE⟩

section WCRestrict

open scoped Distributions

/-- Restriction of `L²` classes to a subdomain is `1`-Lipschitz. -/
theorem aux_lem_weighted_cluster_lipschitz_domainLpRestrict {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U) :
    LipschitzWith 1 (fun f : DomainL2 U => domainLpRestrict hV f) := by
  have hsub : ∀ f g : DomainL2 U, domainLpRestrict hV (f - g)
      = domainLpRestrict hV f - domainLpRestrict hV g := by
    intro f g
    have h : f - g = f + (-1 : ℝ) • g := by module
    rw [h, domainLpRestrict_add, domainLpRestrict_smul]
    module
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [dist_eq_norm, dist_eq_norm, ← hsub]
  simpa using domainLpRestrict_norm_le hV (f - g)

/-- Restriction of Sobolev data to a subdomain is continuous. -/
theorem aux_lem_weighted_cluster_continuous_sobolevDataRestrict {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U) :
    Continuous (sobolevDataRestrict (V := V) (U := U) hV) := by
  have hlip := aux_lem_weighted_cluster_lipschitz_domainLpRestrict hV
  refine Continuous.prodMk (hlip.continuous.comp continuous_fst) ?_
  refine continuous_pi fun j => ?_
  exact hlip.continuous.comp (((continuous_apply j).comp continuous_snd))

/-- Zero extension undoes restriction for an `L²` class vanishing a.e. off `V`. -/
theorem aux_lem_weighted_cluster_zeroExtension_restrict_Lp {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U) (f : DomainL2 U)
    (hf : ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      x ∉ (V : Set (SpatialCoordinates d)) → (f : SpatialCoordinates d → ℝ) x = 0) :
    zeroExtensionLp hVU (domainLpRestrict hVU f) = f := by
  apply Lp.ext
  filter_upwards [zeroExtensionLp_coeFn hVU (domainLpRestrict hVU f),
    ae_restrict_of_ae ((ae_restrict_iff' V.isOpen.measurableSet).1
      (domainLpRestrict_coeFn hVU f)), hf] with x h1 h2 h3
  rw [h1]
  by_cases hx : x ∈ (V : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hx]
    exact h2 hx
  · rw [Set.indicator_of_notMem hx]
    exact (h3 hx).symm

/-- Restriction undoes zero extension. -/
theorem aux_lem_weighted_cluster_restrict_zeroExtension_Lp {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U) (f : DomainL2 V) :
    domainLpRestrict hVU (zeroExtensionLp hVU f) = f := by
  apply Lp.ext
  filter_upwards [domainLpRestrict_coeFn hVU (zeroExtensionLp hVU f),
    ae_restrict_of_ae_restrict_of_subset hVU (zeroExtensionLp_coeFn hVU f),
    ae_restrict_mem V.isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2, Set.indicator_of_mem hx]

/-- Restricting smooth data whose test function is supported in `V` gives killed data on `V`. -/
theorem aux_lem_weighted_cluster_restrict_smooth_mem {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U) (χ : 𝓓(U, ℝ))
    (hχ : tsupport (χ : SpatialCoordinates d → ℝ) ⊆ (V : Set (SpatialCoordinates d))) :
    sobolevDataRestrict hVU (smoothSobolevData χ) ∈ killedSobolevGraph V := by
  let χV : 𝓓(V, ℝ) := ⟨χ, χ.contDiff, χ.hasCompactSupport, hχ⟩
  have hχV_eq : (χV : SpatialCoordinates d → ℝ) = ⇑χ := rfl
  have hkey : sobolevDataRestrict hVU (smoothSobolevData χ) = smoothSobolevData χV := by
    apply Prod.ext
    · change domainLpRestrict hVU (testL2 χ) = testL2 χV
      apply Lp.ext
      filter_upwards [domainLpRestrict_coeFn hVU (testL2 χ),
        ae_restrict_of_ae_restrict_of_subset hVU (testL2_coeFn χ),
        testL2_coeFn χV] with x h1 h2 h3
      rw [h1, h3, hχV_eq]
      exact h2
    · change (fun j => domainLpRestrict hVU (testPartialL2 χ j)) = testPartialL2 χV
      funext i
      apply Lp.ext
      filter_upwards [domainLpRestrict_coeFn hVU (testPartialL2 χ i),
        ae_restrict_of_ae_restrict_of_subset hVU (testPartialL2_coeFn χ i),
        testPartialL2_coeFn χV i] with x h1 h2 h3
      rw [h1, h3, hχV_eq]
      exact h2
  rw [hkey]
  exact smoothSobolevData_mem_killed χV

/-- A test function on `U`, supported in `V`, equal to `1` on an open neighbourhood of a
compact `K ⊆ V`. -/
theorem aux_lem_weighted_cluster_exists_plateau_test {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hKV : K ⊆ (V : Set (SpatialCoordinates d))) :
    ∃ (ψ : 𝓓(U, ℝ)) (W : Set (SpatialCoordinates d)), IsOpen W ∧ K ⊆ W ∧
      tsupport (ψ : SpatialCoordinates d → ℝ) ⊆ (V : Set (SpatialCoordinates d)) ∧
      ∀ x ∈ W, ψ x = 1 := by
  obtain ⟨O₂, hO₂open, hKO₂, hclO₂V, hclO₂cpt⟩ :=
    exists_open_between_and_isCompact_closure hK V.isOpen hKV
  obtain ⟨O₁, hO₁open, hKO₁, hclO₁O₂, _⟩ :=
    exists_open_between_and_isCompact_closure hK hO₂open hKO₂
  have hdisj : Disjoint (O₂ᶜ) (closure O₁) :=
    disjoint_left.mpr (fun x hx hx' => hx (hclO₁O₂ hx'))
  obtain ⟨f, hf0, hf1, _⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (modelWithCornersSelf ℝ (SpatialCoordinates d))
      hO₂open.isClosed_compl isClosed_closure hdisj
  have hsupp : Function.support f ⊆ O₂ := by
    intro x hx
    by_contra hxO₂
    exact hx (hf0 hxO₂)
  have htsub : tsupport f ⊆ (V : Set (SpatialCoordinates d)) :=
    (closure_mono hsupp).trans hclO₂V
  refine ⟨⟨f, ?_, ?_, ?_⟩, O₁, hO₁open, hKO₁, htsub, ?_⟩
  · exact contMDiff_iff_contDiff.mp f.contMDiff
  · exact hclO₂cpt.of_isClosed_subset (isClosed_tsupport (f : SpatialCoordinates d → ℝ))
      (closure_mono hsupp)
  · exact htsub.trans hVU
  · intro x hx
    exact hf1 (subset_closure hx)

/-- Multiplying by a plateau test does nothing to data that vanish, with their gradient,
a.e. off the plateau's compact core `K`. -/
theorem aux_lem_weighted_cluster_mulTest_eq_self {d : ℕ} {U : Opens (SpatialCoordinates d)}
    (ψ : 𝓓(U, ℝ)) (W K : Set (SpatialCoordinates d)) (hW : IsOpen W) (hKW : K ⊆ W)
    (hψ1 : ∀ x ∈ W, ψ x = 1) (p : SobolevData U)
    (hzero : ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      x ∉ K → (p.1 : SpatialCoordinates d → ℝ) x = 0)
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      x ∉ K → (p.2 i : SpatialCoordinates d → ℝ) x = 0) :
    aux_prop_locality_recovery_mulTest ψ p = p := by
  apply Prod.ext
  · rw [aux_prop_locality_recovery_mulTest_fst]
    apply Lp.ext
    filter_upwards [aux_prop_locality_recovery_mulL_coeFn
        (aux_prop_locality_recovery_testLinf ψ) p.1,
      aux_prop_locality_recovery_testLinf_coeFn ψ, hzero] with x h1 h2 h3
    rw [h1, h2]
    by_cases hx : x ∈ K
    · rw [hψ1 x (hKW hx), one_mul]
    · rw [h3 hx, mul_zero]
  · funext i
    rw [aux_prop_locality_recovery_mulTest_snd]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add
        (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf ψ i) p.1)
        (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf ψ) (p.2 i)),
      aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testPartialLinf ψ i) p.1,
      aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testLinf ψ) (p.2 i),
      aux_prop_locality_recovery_testLinf_coeFn ψ,
      aux_prop_locality_recovery_testPartialLinf_coeFn ψ i,
      hzero, hgrad i] with x h0 h1 h2 h3 h4 h5 h6
    rw [h0, Pi.add_apply, h1, h2, h3, h4]
    by_cases hx : x ∈ K
    · have hderiv : fderiv ℝ (⇑ψ) x = 0 := by
        have hloc : (⇑ψ : SpatialCoordinates d → ℝ) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
          Filter.eventually_of_mem (hW.mem_nhds (hKW hx)) (fun y hy => hψ1 y hy)
        rw [Filter.EventuallyEq.fderiv_eq hloc]
        simp
      rw [hψ1 x (hKW hx), hderiv]
      simp
    · rw [h5 hx, h6 hx]
      simp

/-- Restriction after multiplication by a test supported in `V` maps the killed graph of `U`
into the killed graph of `V`. -/
theorem aux_lem_weighted_cluster_restrict_mulTest_mem {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U) (ψ : 𝓓(U, ℝ))
    (hψV : tsupport (ψ : SpatialCoordinates d → ℝ) ⊆ (V : Set (SpatialCoordinates d)))
    {w : SobolevData U} (hw : w ∈ killedSobolevGraph U) :
    sobolevDataRestrict hVU (aux_prop_locality_recovery_mulTest ψ w) ∈ killedSobolevGraph V := by
  have hcont : Continuous (fun w : SobolevData U =>
      sobolevDataRestrict hVU (aux_prop_locality_recovery_mulTest ψ w)) :=
    (aux_lem_weighted_cluster_continuous_sobolevDataRestrict hVU).comp
      (aux_prop_locality_recovery_mulTest ψ).continuous
  have hm : Set.MapsTo (fun w : SobolevData U =>
      sobolevDataRestrict hVU (aux_prop_locality_recovery_mulTest ψ w))
      (Set.range (smoothSobolevData (Ω := U)))
      (killedSobolevGraph V : Set (SobolevData V)) := by
    rintro _ ⟨χ, rfl⟩
    change sobolevDataRestrict hVU (aux_prop_locality_recovery_mulTest ψ (smoothSobolevData χ))
      ∈ killedSobolevGraph V
    rw [aux_prop_locality_recovery_mulTest_smooth]
    exact aux_lem_weighted_cluster_restrict_smooth_mem hVU _
      ((tsupport_mul_subset_right (f := fun x => χ x) (g := fun x => ψ x)).trans hψV)
  apply hm.closure_left hcont isClosed_killedSobolevGraph
  rw [← killedSobolevGraph_coe_eq_closure]
  exact hw

/-- A killed element of `U` vanishing a.e. off a compact `K ⊆ V` is the zero extension of a
killed element of `V`. -/
theorem aux_lem_weighted_cluster_killed_restrict
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U)
    (p : SobolevData U) (hp : p ∈ killedSobolevGraph U)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hKV : K ⊆ (V : Set (SpatialCoordinates d)))
    (hzero : ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      x ∉ K → (p.1 : SpatialCoordinates d → ℝ) x = 0) :
    ∃ q : SobolevData V, q ∈ killedSobolevGraph V ∧ zeroExtensionSobolevData hVU q = p := by
  obtain ⟨ψ, W, hW, hKW, hψV, hψ1⟩ := aux_lem_weighted_cluster_exists_plateau_test hVU K hK hKV
  have hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      x ∉ K → (p.2 i : SpatialCoordinates d → ℝ) x = 0 := fun i =>
    aux_prop_locality_recovery_grad_ae_zero_of_const p (killedSobolevGraph_le_weakSobolevGraph hp)
      Kᶜ hK.isClosed.isOpen_compl 0 hzero i
  have hself : aux_prop_locality_recovery_mulTest ψ p = p :=
    aux_lem_weighted_cluster_mulTest_eq_self ψ W K hW hKW hψ1 p hzero hgrad
  refine ⟨sobolevDataRestrict hVU p, ?_, ?_⟩
  · have h := aux_lem_weighted_cluster_restrict_mulTest_mem hVU ψ hψV hp
    rwa [hself] at h
  · refine Prod.ext ?_ ?_
    · refine aux_lem_weighted_cluster_zeroExtension_restrict_Lp hVU p.1 ?_
      filter_upwards [hzero] with x hx hxV
      exact hx fun hxK => hxV (hKV hxK)
    · funext i
      refine aux_lem_weighted_cluster_zeroExtension_restrict_Lp hVU (p.2 i) ?_
      filter_upwards [hgrad i] with x hx hxV
      exact hx fun hxK => hxV (hKV hxK)

end WCRestrict

/-- The response energy of a zero extension equals the subdomain energy, when the
coefficients agree on the subdomain. -/
theorem aux_lem_weighted_cluster_responseForm_zeroExt
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U)
    (SU : ResponseSpace U) (SV : ResponseSpace V)
    (aU : PositiveCoefficient U) (aV : PositiveCoefficient V)
    (hcoeff : (aU.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] (aV.val : SpatialCoordinates d → ℝ))
    (y : SU.space) (x : SV.space)
    (hyx : zeroExtensionSobolevData hVU (x : SobolevData V) = (y : SobolevData U)) :
    responseForm SV aV x x = responseForm SU aU y y := by
  rw [responseForm_apply, responseForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hy : (y : SobolevData U).2 i = zeroExtensionLp hVU ((x : SobolevData V).2 i) := by
    rw [← hyx]
    rfl
  have hae : ∀ᵐ z ∂volume.restrict (V : Set (SpatialCoordinates d)),
      ((y : SobolevData U).2 i : SpatialCoordinates d → ℝ) z =
        ((x : SobolevData V).2 i : SpatialCoordinates d → ℝ) z := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hVU
      (zeroExtensionLp_coeFn hVU ((x : SobolevData V).2 i))
    filter_upwards [h1, ae_restrict_mem V.isOpen.measurableSet] with z hz hzV
    rw [hy, hz, Set.indicator_of_mem hzV]
  calc (∫ z in (V : Set (SpatialCoordinates d)),
        aV.val z * ((x : SobolevData V).2 i z * (x : SobolevData V).2 i z))
      = ∫ z in (V : Set (SpatialCoordinates d)),
          (aU.val z * (y : SobolevData U).2 i z) * (x : SobolevData V).2 i z := by
        apply integral_congr_ae
        filter_upwards [hcoeff, hae] with z h1 h2
        rw [h1, h2]
        ring
    _ = ∫ z in (U : Set (SpatialCoordinates d)),
          (aU.val z * (y : SobolevData U).2 i z) *
            zeroExtensionLp hVU ((x : SobolevData V).2 i) z :=
        (integral_mul_zeroExtensionLp hVU _ _).symm
    _ = ∫ z in (U : Set (SpatialCoordinates d)),
          aU.val z * ((y : SobolevData U).2 i z * (y : SobolevData U).2 i z) := by
        rw [← hy]
        apply integral_congr_ae
        filter_upwards [] with z
        ring

/-- The limit squeeze of `prop_killed_consistency_cutoff_localization`: a small-cube sequence
converging to `wq`, whose finite energies are Young-dominated by a sequence converging to
`FQ(w)` plus a vanishing error, puts `wq` in the small-cube domain with `Fq(wq) ≤ FQ(w)`. -/
theorem aux_lem_weighted_cluster_upper_tail
    {d : ℕ} {V U : Opens (SpatialCoordinates d)}
    (Sq : ResponseSpace V) (aq : ℕ → PositiveCoefficient V)
    (FQ : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (U : Set (SpatialCoordinates d))))
    (Fq : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (V : Set (SpatialCoordinates d))))
    (hqlower : ∀ (vN : ℕ → Sq.space) (v : DomainL2 V),
      (∀ f : DomainL2 V,
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      (Fq.energy v : EReal) ≤
        liminf (fun n => (responseForm Sq (aq n) (vN n) (vN n) : EReal)) atTop)
    (w : DomainL2 U) (hw : w ∈ FQ.domain) (wq : DomainL2 V)
    (vNq : ℕ → Sq.space) (hvNq : Tendsto (fun n => (vNq n).val.1) atTop (𝓝 wq))
    (e err : ℕ → ℝ) (he : Tendsto e atTop (𝓝 (FQ.form w w)))
    (herr_zero : Tendsto err atTop (𝓝 0))
    (henergy : ∀ ε : ℝ, 0 < ε → ∀ n,
      responseForm Sq (aq n) (vNq n) (vNq n) ≤ (1 + ε) * e n + (1 + ε⁻¹) * err n) :
    wq ∈ Fq.domain ∧ (Fq.energy wq : EReal) ≤ (FQ.energy w : EReal) := by
  have hweak : ∀ f : DomainL2 V,
      Tendsto (fun n => inner ℝ f (vNq n).val.1) atTop (𝓝 (inner ℝ f wq)) :=
    fun f => tendsto_const_nhds.inner hvNq
  have hlow := hqlower vNq wq hweak
  have hEQenergy : FQ.energy w = (FQ.form w w : EReal) := FQ.energy_of_mem hw
  have hA_bdd : IsBoundedUnder (· ≥ ·) atTop
      (fun n => (responseForm Sq (aq n) (vNq n) (vNq n) : EReal)) := by
    change ∃ b : EReal, ∀ᶠ n : ℕ in atTop,
      (responseForm Sq (aq n) (vNq n) (vNq n) : EReal) ≥ b
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro n
    exact EReal.coe_nonneg.mpr (responseForm_nonneg Sq (aq n) (vNq n))
  have hliminf_bound : ∀ ε : ℝ, 0 < ε →
      liminf (fun n => (responseForm Sq (aq n) (vNq n) (vNq n) : EReal)) atTop ≤
        (((1 + ε) * FQ.form w w : ℝ) : EReal) := by
    intro ε hε
    have hCreal : Tendsto (fun n => (1 + ε) * e n + (1 + ε⁻¹) * err n) atTop
        (𝓝 ((1 + ε) * FQ.form w w + (1 + ε⁻¹) * 0)) :=
      (tendsto_const_nhds.mul he).add (tendsto_const_nhds.mul herr_zero)
    have hC : Tendsto (fun n => (((1 + ε) * e n + (1 + ε⁻¹) * err n : ℝ) : EReal)) atTop
        (𝓝 (((1 + ε) * FQ.form w w + (1 + ε⁻¹) * 0 : ℝ) : EReal)) :=
      EReal.tendsto_coe.mpr hCreal
    have hle : ∀ n : ℕ, (responseForm Sq (aq n) (vNq n) (vNq n) : EReal) ≤
        (((1 + ε) * e n + (1 + ε⁻¹) * err n : ℝ) : EReal) :=
      fun n => EReal.coe_le_coe_iff.mpr (henergy ε hε n)
    have hlim := Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
      hA_bdd hC.isCoboundedUnder_ge
    rw [hC.liminf_eq] at hlim
    simpa only [mul_zero, add_zero] using hlim
  have hEq_lt_top : Fq.energy wq < ⊤ :=
    (hlow.trans (hliminf_bound 1 one_pos)).trans_lt (EReal.coe_lt_top _)
  have hwqdom : wq ∈ Fq.domain := Fq.mem_domain_of_energy_lt_top hEq_lt_top
  refine ⟨hwqdom, ?_⟩
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro a ha
  obtain ⟨c, hEc, hca⟩ := EReal.exists_between_coe_real ha
  rw [hEQenergy] at hEc
  have hreal : 0 ≤ FQ.form w w := FQ.form_nonneg w hw
  have hce : FQ.form w w < c := EReal.coe_lt_coe_iff.mp hEc
  have hob := aux_prop_locality_recovery_eps_choice (FQ.form w w) (c - FQ.form w w) hreal
    (sub_pos.mpr hce)
  obtain ⟨ε, hε, hlt⟩ := hob
  have hmul : (1 + ε) * FQ.form w w < c := by
    rw [mul_zero, add_zero] at hlt
    linarith
  have hb := hlow.trans (hliminf_bound ε hε)
  exact hb.trans (le_of_lt ((EReal.coe_lt_coe_iff.mpr hmul).trans hca))

/-- The small-cube sequence obtained by restricting killed data that vanish off a
compact subset of the small cube: energies are unchanged and the `L²` limit is the
restriction. -/
theorem aux_lem_weighted_cluster_restrict_seq
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hVU : V ≤ U)
    (SU : ResponseSpace U) (SV : ResponseSpace V)
    (hSU : SU.space = killedSobolevGraph U) (hSV : SV.space = killedSobolevGraph V)
    (aU : ℕ → PositiveCoefficient U) (aV : ℕ → PositiveCoefficient V)
    (hcoeff : ∀ n, ((aU n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] ((aV n).val : SpatialCoordinates d → ℝ))
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hKV : K ⊆ (V : Set (SpatialCoordinates d)))
    (Y : ℕ → SU.space)
    (hzero : ∀ n, ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      x ∉ K → ((Y n).val.1 : SpatialCoordinates d → ℝ) x = 0)
    (w : DomainL2 U) (hY : Tendsto (fun n => (Y n).val.1) atTop (𝓝 w)) :
    ∃ vNq : ℕ → SV.space,
      Tendsto (fun n => (vNq n).val.1) atTop (𝓝 (domainLpRestrict hVU w)) ∧
      ∀ n, responseForm SV (aV n) (vNq n) (vNq n) = responseForm SU (aU n) (Y n) (Y n) := by
  have hres : ∀ n, ∃ q : SobolevData V, q ∈ killedSobolevGraph V ∧
      zeroExtensionSobolevData hVU q = ((Y n : SU.space) : SobolevData U) := fun n =>
    aux_lem_weighted_cluster_killed_restrict hVU _
      (aux_prop_locality_recovery_mem_killed SU hSU (Y n)) K hK hKV (hzero n)
  choose qd hqd hqdext using hres
  let vNq : ℕ → SV.space := fun n => ⟨qd n, aux_prop_locality_recovery_mem_space SV hSV (hqd n)⟩
  refine ⟨vNq, ?_, fun n => aux_lem_weighted_cluster_responseForm_zeroExt hVU SU SV (aU n) (aV n)
    (hcoeff n) (Y n) (vNq n) (hqdext n)⟩
  have hfst : ∀ n, (vNq n).val.1 = domainLpRestrict hVU (Y n).val.1 := by
    intro n
    have h1 : zeroExtensionLp hVU (qd n).1 = (Y n).val.1 := congrArg Prod.fst (hqdext n)
    change (qd n).1 = _
    rw [← h1, aux_lem_weighted_cluster_restrict_zeroExtension_Lp]
  have hcont := (aux_lem_weighted_cluster_lipschitz_domainLpRestrict hVU).continuous
  have h := (hcont.tendsto w).comp hY
  refine h.congr (fun n => ?_)
  exact (hfst n).symm

/-- G8 upper half (hUpperF). `prop_killed_consistency_cutoff_localization` WITHOUT the
carried `hcutoffProduct`: the reverse killed inequality, proved by running the
cutoff-localization limit argument on the cutoff product of a smoothed recovery sequence
(paper label `mfd:prop-21` applied to the weighted forms, ). -/
theorem aux_lem_weighted_cluster_upper_localize
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
    (hQrecovery : ∀ v ∈ EQ.domain, ∃ vN : ℕ → SQ.space,
      Tendsto (fun n => ((vN n).val.1,
        (responseForm SQ (aQ n) (vN n) (vN n) : EReal))) atTop
        (𝓝 (v, (EQ.energy v : EReal))))
    (hqlower : ∀ (vN : ℕ → Sq.space) (v : DomainL2 (centeredCube zq r hr0)),
      (∀ f : DomainL2 (centeredCube zq r hr0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop
          (𝓝 (inner ℝ f v))) →
      (Eq.energy v : EReal) ≤
        liminf (fun n => (responseForm Sq (aq n) (vN n) (vN n) : EReal)) atTop)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : SQ.space,
      cubeFractionalL2Seminorm hd zQ R hR0 _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : SQ.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd zQ R hR0 _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm SQ (aQ n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
        closure O ⊆ (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → SQ.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube zQ R hR0 : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm SQ (aQ n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aQ n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (w : DomainL2 (centeredCube zQ R hR0)) (hw : w ∈ EQ.domain)
    (hwrep : ∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧
      HasCompactSupport wc ∧
      tsupport wc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∧
      (w : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] wc) :
    ∃ wq : DomainL2 (centeredCube zq r hr0),
      wq ∈ Eq.domain ∧ zeroExtensionLp hqQ wq = w ∧
      (Eq.energy wq : EReal) ≤ (EQ.energy w : EReal) := by
  obtain ⟨wc, hwc_cont, hwc_supp, hwc_tsupp, hwc⟩ := hwrep
  have hob1 := exists_open_between_and_isCompact_closure hwc_supp.isCompact
    (centeredCube zq r hr0).isOpen hwc_tsupp
  obtain ⟨O₁, hO₁, hKO₁, hO₁q, hO₁c⟩ := hob1
  have hO₁Q : closure O₁ ⊆ (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) :=
    hO₁q.trans hqQ
  have hob2 := hcutoffs (tsupport wc) O₁ hwc_supp.isCompact hO₁ hKO₁ hO₁Q
  obtain ⟨V₁, psi, psic, B, hV₁, hKV₁, -, hB, hpsi⟩ := hob2
  have hob3 := hQrecovery w hw
  obtain ⟨vN, hvN⟩ := hob3
  have hEw : EQ.energy w = (EQ.form w w : EReal) := EQ.energy_of_mem hw
  have hEw0 : (0 : EReal) ≤ EQ.energy w := by
    rw [hEw]
    exact EReal.coe_nonneg.2 (EQ.form_nonneg w hw)
  have hEwtop : EQ.energy w < ⊤ := (EQ.energy_lt_top_iff w).2 hw
  have hob4 := aux_prop_locality_recovery_recovery_parts (fun n => (vN n).val.1)
    (fun n => responseForm SQ (aQ n) (vN n) (vN n)) w (EQ.energy w) hEw0 hEwtop hvN
  obtain ⟨hvN1, hvNE⟩ := hob4
  have hob5 := aux_prop_locality_recovery_smooth_seq SQ hSQ aQ vN w _ hvN1 hvNE
  obtain ⟨φ, Φ, hΦv, hΦ1, hΦE⟩ := hob5
  have hin := fun n => aux_prop_locality_recovery_inner_ae (psi n).val (SQ.le_weak (psi n).2)
    (psic n) (hpsi n).2.1 (hpsi n).2.2.1 V₁ hV₁ (hpsi n).2.2.2.1 w wc hwc hKV₁
  have hprops := fun n => aux_prop_locality_recovery_modV_props SQ hSQ (φ n) (Φ n) (hΦv n)
    (psi n) w (hin n).1 (hin n).2.1 (hin n).2.2
  have hob6 := hΦE.bddAbove_range
  obtain ⟨Eb, hEb⟩ := hob6
  have hT := aux_prop_locality_recovery_trace_tendsto hd hInterp zQ R hR0 t ht SQ aQ KN hKN
    Kstar hKstar hfrac hcoercive psi B hB (fun n => (hpsi n).2.2.2.2.2.1)
    (fun n => (hpsi n).2.2.2.2.2.2) Φ w hΦ1 Eb (fun n => hEb ⟨n, rfl⟩)
  have hY1 : Tendsto (fun n => (aux_prop_locality_recovery_modV SQ hSQ (φ n) (psi n)).val.1)
      atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.mp hΦ1)
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (aux_prop_locality_recovery_modV SQ hSQ (φ n) (psi n)).val.1 w,
      Lp.coeFn_sub (Φ n).val.1 w, (hprops n).2.2] with x h1 h2 h3
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
    exact h3
  have hzero : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
      x ∉ closure O₁ →
        ((aux_prop_locality_recovery_modV SQ hSQ (φ n) (psi n)).val.1 :
          SpatialCoordinates d → ℝ) x = 0 := by
    intro n
    filter_upwards [aux_prop_locality_recovery_modV_fst_ae SQ hSQ (φ n) (psi n), (hpsi n).2.1,
      ae_restrict_mem (centeredCube zQ R hR0).isOpen.measurableSet] with x h1 h2 hxQ hx
    rw [h1, h2, (hpsi n).2.2.2.2.1 x hxQ (fun h => hx (subset_closure h)), mul_zero]
  have hob7 := aux_lem_weighted_cluster_restrict_seq hqQ SQ Sq hSQ hSq aQ aq hcoeff
    (closure O₁) hO₁c hO₁q (fun n => aux_prop_locality_recovery_modV SQ hSQ (φ n) (psi n))
    hzero w hY1
  obtain ⟨vNq, hvNq, hEeq⟩ := hob7
  have hEΦ : Tendsto (fun n => responseForm SQ (aQ n) (Φ n) (Φ n)) atTop
      (𝓝 (EQ.form w w)) := by
    rw [hEw, EReal.toReal_coe] at hΦE
    exact hΦE
  have henergy : ∀ ε : ℝ, 0 < ε → ∀ n,
      responseForm Sq (aq n) (vNq n) (vNq n) ≤ (1 + ε) * responseForm SQ (aQ n) (Φ n) (Φ n) +
        (1 + ε⁻¹) * (∫⁻ x in (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((aQ n).val x * ∑ i : Fin d, ((psi n).val.2 i x) ^ 2) *
            ENNReal.ofReal (((Φ n).val.1 x - w x) ^ 2)).toReal := by
    intro ε hε n
    rw [hEeq n]
    exact aux_prop_locality_recovery_energy_split SQ (aQ n)
      (aux_prop_locality_recovery_modV SQ hSQ (φ n) (psi n)) (Φ n)
      (fun i => aux_prop_locality_recovery_mulL
        (aux_prop_locality_recovery_testPartialLinf (φ n) i) (psi n).val.1)
      (fun i => aux_prop_locality_recovery_mulL
        (aux_prop_locality_recovery_testLinf (φ n)) ((psi n).val.2 i))
      (fun i => (psi n).val.2 i) (fun x => (Φ n).val.1 x - w x)
      (fun i => aux_prop_locality_recovery_modV_grad SQ hSQ (φ n) (psi n) i)
      (hprops n).1 (hprops n).2.1 hε
  have htail := aux_lem_weighted_cluster_upper_tail Sq aq EQ Eq hqlower w hw
    (domainLpRestrict hqQ w) vNq hvNq _ _ hEΦ hT henergy
  obtain ⟨hdom, hle⟩ := htail
  refine ⟨domainLpRestrict hqQ w, hdom, ?_, hle⟩
  apply aux_lem_weighted_cluster_zeroExtension_restrict_Lp hqQ w
  filter_upwards [hwc] with x hx hxq
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport (fun h => hxq (hwc_tsupp h))

/-- Strong locality of the weighted Mosco-limit form is stated **relative to `Q`**
(`F.MemCoreOn Q`, continuous representatives with compact support in `Q`), not on the
whole-space `MemCore = MemCoreOn Set.univ` that `IsStronglyLocalOnCore` uses — `prop_locality`'s
argument (and the paper's `prop_locality`, strong locality of the form on `L²(Q)`) only ever
supplies the `tsupport ⊆ Q` case, since its recovery/coercivity/cutoff data all live on the one
cube `Q`. The Q-relative clause below has exactly `IsStronglyLocalOnCore`'s shape with
`MemCore`/`MemCoreOn Set.univ` replaced by `MemCoreOn Q`; the two extra hypotheses
`HasCompactSupport uc` and `tsupport uc ⊆ Q`, `tsupport vc ⊆ Q` are the Q-relative analogues of
clauses that are vacuous when `Q = Set.univ` (so are absent from `IsStronglyLocalOnCore`) but are
exactly what `prop_locality` needs and supplies for a proper cube `Q`.

Proof: unpack `F.MemCoreOn Q u/v` into `MemFormCore G u/v` via `hF` (domain membership rewrites
through `energy_lt_top_iff`; the core-representative witness is literally `MemFormCore`'s data),
apply `prop_locality` to get `limitFormBilinear G u v = 0`, then read off `F.form u v = 0` via
`aux_lem_weighted_cluster_form_eq_zero_of_bilinear`. 
(paper label `mfd:prop-21`, prop_locality ). -/
theorem aux_lem_weighted_cluster_strongly_local
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGsymm : ∀ f g : DomainL2 (centeredCube z r hr),
      (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (hRecovery : ∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
        closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ,
            0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hF : ∀ u, F.energy u = limitFormEnergy G u) :
    ∀ u v : DomainL2 (centeredCube z r hr),
      F.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
      F.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → F.form u v = 0 := by
  intro u v hu hv uc vc huc hvc hucont hvcont husupp hvsupp husuppQ hvsuppQ c W hW hsupp hconst
  have hu' : MemFormCore G u :=
    ⟨by
        show limitFormEnergy G u < ⊤
        rw [← hF u]
        exact (F.energy_lt_top_iff u).2 hu.1,
      hu.2⟩
  have hv' : MemFormCore G v :=
    ⟨by
        show limitFormEnergy G v < ⊤
        rw [← hF v]
        exact (F.energy_lt_top_iff v).2 hv.1,
      hv.2⟩
  have hbi := prop_locality d hd z r hr S hS a G hGsymm hLower hRecovery KN hKN Kstar hKstar
    hfrac hcoercive hInterp t ht htd hcutoffs u v hu' hv' uc vc huc hvc hucont hvcont hvsupp
    husuppQ hvsuppQ husupp c W hW hsupp hconst
  exact aux_lem_weighted_cluster_form_eq_zero_of_bilinear F G hF u v hu.1 hv.1 hbi

/-- Sixth split-out piece (same heartbeat rationale): G9 (open-cube inf/sup comparison) plus
the final assembly, taking G8 (`hcons`) as a hypothesis. -/
theorem aux_lem_weighted_cluster_principal_tail4
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u)
    (_hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤)
    (tau : ℕ → ℕ) (_htau : StrictMono tau)
    (sigma : ℕ → ℕ) (_hsigma : StrictMono sigma)
    (Grho : ∀ j, H j →L[ℝ] H j)
    (_hG : ∀ j, Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
      IsCompactOperator (Grho j) ∧
      (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
      (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
      Function.Injective (Grho j))
    (_hFmosco : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Grho j) u ≤
          liminf (fun n => ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (Grho j) u))))
    (_hEmoscoSub : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (GE j) u ≤
          liminf (fun n => ((responseForm (S j) (a j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (GE j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (a j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (GE j) u))))
    (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hFForm : ∀ j (u : H j), (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u)
    (_hcmpAll : ∀ j, limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
      ∀ u ∈ limitFormDomain (GE j),
        (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
        limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u)
    (_hforms : ∀ j, (∀ u, u ∈ (FForm j).toClosedForm.domain ↔ u ∈ (EForm j).domain) ∧
      ∀ u ∈ (EForm j).domain, lo j * (EForm j).form u u ≤ (FForm j).toClosedForm.form u u ∧
        (FForm j).toClosedForm.form u u ≤ hi j * (EForm j).form u u)
    (_hcoreReg : ∀ j, (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
      (Q j : Set (SpatialCoordinates d)) C) ∧ _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm)
    (_hcoerW : ∀ j (n : ℕ) (w : (S j).space),
      ‖w.val.1‖ ^ 2 + volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        (KN j (tau (sigma n)) / lo j) * responseForm (S j) (arho j (tau (sigma n))) w w)
    (_hcutW : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (arho j (tau (sigma n))) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((arho j (tau (sigma n))).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hKNW : ∀ j (n : ℕ), 0 ≤ KN j (tau (sigma n)) / lo j)
    (_hKstarW : ∀ j (n : ℕ), KN j (tau (sigma n)) / lo j ≤ Kstar j / lo j)
    (_hFdom : ∀ j (v : H j), v ∈ (FForm j).toClosedForm.domain → v ∈ limitFormDomain (Grho j))
    (_hcoeffW : ∀ j k (_hjk : Q j ≤ Q k) (m : ℕ), ((arho k m).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
        ((arho j m).val : SpatialCoordinates d → ℝ))
    (_hloc : ∀ j, (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0))
    (_hcons : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j,
          u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (FForm j).toClosedForm.domain,
        (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) =
          (FForm j).toClosedForm.energy u)),
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs hform hinverse tau htau sigma hsigma Grho hG hFmosco hEmoscoSub FForm hFForm
    hcmpAll hforms hcoreReg hcoerW hcutW hKNW hKstarW hFdom hcoeffW hloc hcons
  have hzmem : ∀ j, z j ∈ (Q j : Set (SpatialCoordinates d)) := by
    intro j
    change z j ∈ Metric.ball (z j) (r j / 2)
    exact Metric.mem_ball_self (half_pos (hr j))
  have hhi_pos : ∀ j, 0 < hi j := by
    intro j
    have h := hrhobounds j (z j) (subset_closure (hzmem j))
    linarith [hlo j]
  -- G9: open-cube inf/sup comparison on the E domain
  have hcQ : ∀ j, 0 < sInf (rho '' (Q j : Set (SpatialCoordinates d))) ∧
      ∀ x ∈ (Q j : Set (SpatialCoordinates d)),
        sInf (rho '' (Q j : Set (SpatialCoordinates d))) ≤ rho x ∧
        rho x ≤ sSup (rho '' (Q j : Set (SpatialCoordinates d))) := by
    intro j
    have hbddB : BddBelow (rho '' (Q j : Set (SpatialCoordinates d))) := by
      refine ⟨lo j, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (hrhobounds j x (subset_closure hx)).1
    have hbddA : BddAbove (rho '' (Q j : Set (SpatialCoordinates d))) := by
      refine ⟨hi j, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (hrhobounds j x (subset_closure hx)).2
    refine ⟨lt_of_lt_of_le (hlo j) (le_csInf ⟨rho (z j), mem_image_of_mem rho (hzmem j)⟩ ?_),
      fun x hx => ⟨csInf_le hbddB (mem_image_of_mem rho hx),
        le_csSup hbddA (mem_image_of_mem rho hx)⟩⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hrhobounds j x (subset_closure hx)).1
  have hfinal : ∀ j, ∀ u ∈ (EForm j).domain,
      sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
        (FForm j).toClosedForm.form u u ∧
      (FForm j).toClosedForm.form u u ≤
        sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u := by
    intro j
    obtain ⟨hc1, hbd⟩ := hcQ j
    have hc2 : 0 ≤ sSup (rho '' (Q j : Set (SpatialCoordinates d))) :=
      hc1.le.trans ((hbd (z j) (hzmem j)).1.trans (hbd (z j) (hzmem j)).2)
    have hcmp' := aux_lem_weighted_cluster_limit_comparison (S j)
      (fun n => a j (tau (sigma n))) (fun n => arho j (tau (sigma n))) (GE j) (Grho j) _ _ hc1 hc2
      (fun n u => aux_lem_weighted_cluster_rho_form_bounds (S j) (a j (tau (sigma n)))
        (arho j (tau (sigma n))) (A (tau (sigma n))) rho (ha j _) (harho j _) _ _ hc1 hbd u)
      (hEmoscoSub j).1 (hEmoscoSub j).2 (hFmosco j).1 (hFmosco j).2
    exact (aux_lem_weighted_cluster_forms_of_limit (EForm j) (FForm j).toClosedForm (GE j) (Grho j)
      (hEForm j) (hFForm j) _ _ hcmp'.1 hcmp'.2).2
  refine ⟨sigma, hsigma, Grho, FForm, fun j => ?_, fun j k hjk => ⟨hcons j k hjk, hfinal j⟩⟩
  exact ⟨(hG j).1, (hG j).2.1, (hG j).2.2.1, (hG j).2.2.2.1, (hG j).2.2.2.2, hFForm j,
    (hFmosco j).2, (hFmosco j).1, (hcmpAll j).1, (hcmpAll j).2, (hcoreReg j).2, (hcoreReg j).1,
    hloc j⟩

/-- G8b: `hUpperF` and `hcons`, taking `hLowerF` (G8a) as a hypothesis, further splitting
`aux_lem_weighted_cluster_principal_tail3` for the heartbeat budget. -/
theorem aux_lem_weighted_cluster_principal_tail3c
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u)
    (_hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤)
    (tau : ℕ → ℕ) (_htau : StrictMono tau)
    (sigma : ℕ → ℕ) (_hsigma : StrictMono sigma)
    (Grho : ∀ j, H j →L[ℝ] H j)
    (_hG : ∀ j, Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
      IsCompactOperator (Grho j) ∧
      (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
      (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
      Function.Injective (Grho j))
    (_hFmosco : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Grho j) u ≤
          liminf (fun n => ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (Grho j) u))))
    (_hEmoscoSub : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (GE j) u ≤
          liminf (fun n => ((responseForm (S j) (a j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (GE j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (a j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (GE j) u))))
    (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hFForm : ∀ j (u : H j), (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u)
    (_hcmpAll : ∀ j, limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
      ∀ u ∈ limitFormDomain (GE j),
        (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
        limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u)
    (_hforms : ∀ j, (∀ u, u ∈ (FForm j).toClosedForm.domain ↔ u ∈ (EForm j).domain) ∧
      ∀ u ∈ (EForm j).domain, lo j * (EForm j).form u u ≤ (FForm j).toClosedForm.form u u ∧
        (FForm j).toClosedForm.form u u ≤ hi j * (EForm j).form u u)
    (_hcoreReg : ∀ j, (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
      (Q j : Set (SpatialCoordinates d)) C) ∧ _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm)
    (_hcoerW : ∀ j (n : ℕ) (w : (S j).space),
      ‖w.val.1‖ ^ 2 + volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        (KN j (tau (sigma n)) / lo j) * responseForm (S j) (arho j (tau (sigma n))) w w)
    (_hcutW : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (arho j (tau (sigma n))) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((arho j (tau (sigma n))).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hKNW : ∀ j (n : ℕ), 0 ≤ KN j (tau (sigma n)) / lo j)
    (_hKstarW : ∀ j (n : ℕ), KN j (tau (sigma n)) / lo j ≤ Kstar j / lo j)
    (_hFdom : ∀ j (v : H j), v ∈ (FForm j).toClosedForm.domain → v ∈ limitFormDomain (Grho j))
    (_hcoeffW : ∀ j k (_hjk : Q j ≤ Q k) (m : ℕ), ((arho k m).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
        ((arho j m).val : SpatialCoordinates d → ℝ))
    (_hloc : ∀ j, (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0))
    (_hLowerF : ∀ j k (hjk : Q j ≤ Q k), ∀ u : H j, u ∈ (FForm j).toClosedForm.domain →
      ((FForm k).toClosedForm.energy (zeroExtensionLp hjk u) : EReal) ≤
        ((FForm j).toClosedForm.energy u : EReal))
    (_hUpperF : ∀ j k (hjk : Q j ≤ Q k), ∀ w : H k, w ∈ (FForm k).toClosedForm.domain →
      (∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧ HasCompactSupport wc ∧
        tsupport wc ⊆ (Q j : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q k : Set (SpatialCoordinates d))] wc) →
      ∃ wq : H j, wq ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk wq = w ∧
        ((FForm j).toClosedForm.energy wq : EReal) ≤ ((FForm k).toClosedForm.energy w : EReal)),
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs hform hinverse tau htau sigma hsigma Grho hG hFmosco hEmoscoSub FForm hFForm
    hcmpAll hforms hcoreReg hcoerW hcutW hKNW hKstarW hFdom hcoeffW hloc hLowerF hUpperF
  have hzmem : ∀ j, z j ∈ (Q j : Set (SpatialCoordinates d)) := by
    intro j
    change z j ∈ Metric.ball (z j) (r j / 2)
    exact Metric.mem_ball_self (half_pos (hr j))
  have hhi_pos : ∀ j, 0 < hi j := by
    intro j
    have h := hrhobounds j (z j) (subset_closure (hzmem j))
    linarith [hlo j]
  have hcons : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j,
          u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (FForm j).toClosedForm.domain,
        (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) =
          (FForm j).toClosedForm.energy u) := by
    intro j k hjk
    have hcc := prop_killed_consistency_core_closure d hd (z k) (z j) (r k) (r j) (hr k) (hr j)
      hjk (FForm k).toClosedForm (FForm j).toClosedForm (hcoreReg j).1 (hLowerF j k hjk)
      (hUpperF j k hjk)
    exact ⟨aux_lem_weighted_cluster_killed_domain_transfer hjk (EForm k) (FForm k).toClosedForm
      (EForm j) (FForm j).toClosedForm (hforms k).1 (hforms j).1 (lo k) (hi k) (hlo k)
      (hhi_pos k).le (hforms k).2 (hEconsistent j k hjk).1, fun u hu => (hcc u hu).2.1⟩
  exact aux_lem_weighted_cluster_principal_tail4 d hd J j0 z r hr hroot S hS A hAcont a arho
    ha rho hrhocont hrhopos lo hi hlo hlodef hhidef hrhobounds harho GN GrhoN hGN hGrhoN KN hKN
    Kstar hKstar H34sq hH34def hfrac hcoercive hInterp GE EForm hEForm hEnorm hEinj hEmosco
    hElower hEcore hEloc hEconsistent t ht htd hcutoffs hform hinverse tau htau sigma hsigma
    Grho hG hFmosco hEmoscoSub FForm hFForm hcmpAll hforms hcoreReg hcoerW hcutW hKNW hKstarW
    hFdom hcoeffW hloc hcons





theorem aux_lem_weighted_cluster_principal_tail3b
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u)
    (_hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤)
    (tau : ℕ → ℕ) (_htau : StrictMono tau)
    (sigma : ℕ → ℕ) (_hsigma : StrictMono sigma)
    (Grho : ∀ j, H j →L[ℝ] H j)
    (_hG : ∀ j, Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
      IsCompactOperator (Grho j) ∧
      (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
      (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
      Function.Injective (Grho j))
    (_hFmosco : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Grho j) u ≤
          liminf (fun n => ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (Grho j) u))))
    (_hEmoscoSub : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (GE j) u ≤
          liminf (fun n => ((responseForm (S j) (a j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (GE j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (a j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (GE j) u))))
    (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hFForm : ∀ j (u : H j), (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u)
    (_hcmpAll : ∀ j, limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
      ∀ u ∈ limitFormDomain (GE j),
        (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
        limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u)
    (_hforms : ∀ j, (∀ u, u ∈ (FForm j).toClosedForm.domain ↔ u ∈ (EForm j).domain) ∧
      ∀ u ∈ (EForm j).domain, lo j * (EForm j).form u u ≤ (FForm j).toClosedForm.form u u ∧
        (FForm j).toClosedForm.form u u ≤ hi j * (EForm j).form u u)
    (_hcoreReg : ∀ j, (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
      (Q j : Set (SpatialCoordinates d)) C) ∧ _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm)
    (_hcoerW : ∀ j (n : ℕ) (w : (S j).space),
      ‖w.val.1‖ ^ 2 + volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        (KN j (tau (sigma n)) / lo j) * responseForm (S j) (arho j (tau (sigma n))) w w)
    (_hcutW : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (arho j (tau (sigma n))) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((arho j (tau (sigma n))).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hKNW : ∀ j (n : ℕ), 0 ≤ KN j (tau (sigma n)) / lo j)
    (_hKstarW : ∀ j (n : ℕ), KN j (tau (sigma n)) / lo j ≤ Kstar j / lo j)
    (_hFdom : ∀ j (v : H j), v ∈ (FForm j).toClosedForm.domain → v ∈ limitFormDomain (Grho j))
    (_hcoeffW : ∀ j k (_hjk : Q j ≤ Q k) (m : ℕ), ((arho k m).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
        ((arho j m).val : SpatialCoordinates d → ℝ))
    (_hloc : ∀ j, (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0))
    (_hLowerF : ∀ j k (hjk : Q j ≤ Q k), ∀ u : H j, u ∈ (FForm j).toClosedForm.domain →
      ((FForm k).toClosedForm.energy (zeroExtensionLp hjk u) : EReal) ≤
        ((FForm j).toClosedForm.energy u : EReal)),
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs hform hinverse tau htau sigma hsigma Grho hG hFmosco hEmoscoSub FForm hFForm
    hcmpAll hforms hcoreReg hcoerW hcutW hKNW hKstarW hFdom hcoeffW hloc hLowerF
  have hzmem : ∀ j, z j ∈ (Q j : Set (SpatialCoordinates d)) := by
    intro j
    change z j ∈ Metric.ball (z j) (r j / 2)
    exact Metric.mem_ball_self (half_pos (hr j))
  have hhi_pos : ∀ j, 0 < hi j := by
    intro j
    have h := hrhobounds j (z j) (subset_closure (hzmem j))
    linarith [hlo j]
  have hUpperF : ∀ j k (hjk : Q j ≤ Q k), ∀ w : H k, w ∈ (FForm k).toClosedForm.domain →
      (∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧ HasCompactSupport wc ∧
        tsupport wc ⊆ (Q j : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q k : Set (SpatialCoordinates d))] wc) →
      ∃ wq : H j, wq ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk wq = w ∧
        ((FForm j).toClosedForm.energy wq : EReal) ≤ ((FForm k).toClosedForm.energy w : EReal) := by
    intro j k hjk w hw hwrep
    have hQrecoveryArg : ∀ v ∈ (FForm k).toClosedForm.domain, ∃ vN : ℕ → (S k).space,
        Tendsto (fun n => ((vN n).val.1,
          (responseForm (S k) (arho k (tau (sigma n))) (vN n) (vN n) : EReal))) atTop
          (𝓝 (v, ((FForm k).toClosedForm.energy v : EReal))) := by
      intro v hv
      simp only [hFForm k]
      exact (hFmosco k).2 v (hFdom k v hv)
    have hqlowerArg : ∀ (vN : ℕ → (S j).space) (v : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
        ((FForm j).toClosedForm.energy v : EReal) ≤
          liminf (fun n => (responseForm (S j) (arho j (tau (sigma n))) (vN n) (vN n) : EReal))
            atTop := by
      intro vN v hv
      simp only [hFForm j]
      exact (hFmosco j).1 vN v hv
    exact aux_lem_weighted_cluster_upper_localize d hd (z k) (z j) (r k) (r j) (hr k) (hr j) hjk
      (S k) (S j) (hS k) (hS j) (fun n => arho k (tau (sigma n)))
      (fun n => arho j (tau (sigma n))) (fun n => hcoeffW j k hjk _)
      (FForm k).toClosedForm (FForm j).toClosedForm
      hQrecoveryArg hqlowerArg
      (fun n => KN k (tau (sigma n)) / lo k) (hKNW k) (Kstar k / lo k) (hKstarW k) (hfrac k)
      (hcoerW k) hInterp t ht htd (hcutW k) w hw hwrep
  exact aux_lem_weighted_cluster_principal_tail3c d hd J j0 z r hr hroot S hS A hAcont a arho
    ha rho hrhocont hrhopos lo hi hlo hlodef hhidef hrhobounds harho GN GrhoN hGN hGrhoN KN hKN
    Kstar hKstar H34sq hH34def hfrac hcoercive hInterp GE EForm hEForm hEnorm hEinj hEmosco
    hElower hEcore hEloc hEconsistent t ht htd hcutoffs hform hinverse tau htau sigma hsigma
    Grho hG hFmosco hEmoscoSub FForm hFForm hcmpAll hforms hcoreReg hcoerW hcutW hKNW hKstarW
    hFdom hcoeffW hloc hLowerF hUpperF

/-- G8c: `hcons`, taking `hLowerF` and `hUpperF` (G8a/G8b) as hypotheses, further splitting
`aux_lem_weighted_cluster_principal_tail3b` for the heartbeat budget. -/
theorem aux_lem_weighted_cluster_principal_tail3
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u)
    (_hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤)
    (tau : ℕ → ℕ) (_htau : StrictMono tau)
    (sigma : ℕ → ℕ) (_hsigma : StrictMono sigma)
    (Grho : ∀ j, H j →L[ℝ] H j)
    (_hG : ∀ j, Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
      IsCompactOperator (Grho j) ∧
      (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
      (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
      Function.Injective (Grho j))
    (_hFmosco : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Grho j) u ≤
          liminf (fun n => ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (Grho j) u))))
    (_hEmoscoSub : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (GE j) u ≤
          liminf (fun n => ((responseForm (S j) (a j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (GE j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (a j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (GE j) u))))
    (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hFForm : ∀ j (u : H j), (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u)
    (_hcmpAll : ∀ j, limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
      ∀ u ∈ limitFormDomain (GE j),
        (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
        limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u)
    (_hforms : ∀ j, (∀ u, u ∈ (FForm j).toClosedForm.domain ↔ u ∈ (EForm j).domain) ∧
      ∀ u ∈ (EForm j).domain, lo j * (EForm j).form u u ≤ (FForm j).toClosedForm.form u u ∧
        (FForm j).toClosedForm.form u u ≤ hi j * (EForm j).form u u)
    (_hcoreReg : ∀ j, (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
      (Q j : Set (SpatialCoordinates d)) C) ∧ _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm)
    (_hcoerW : ∀ j (n : ℕ) (w : (S j).space),
      ‖w.val.1‖ ^ 2 + volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        (KN j (tau (sigma n)) / lo j) * responseForm (S j) (arho j (tau (sigma n))) w w)
    (_hcutW : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (arho j (tau (sigma n))) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((arho j (tau (sigma n))).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hKNW : ∀ j (n : ℕ), 0 ≤ KN j (tau (sigma n)) / lo j)
    (_hKstarW : ∀ j (n : ℕ), KN j (tau (sigma n)) / lo j ≤ Kstar j / lo j)
    (_hFdom : ∀ j (v : H j), v ∈ (FForm j).toClosedForm.domain → v ∈ limitFormDomain (Grho j))
    (_hcoeffW : ∀ j k (_hjk : Q j ≤ Q k) (m : ℕ), ((arho k m).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
        ((arho j m).val : SpatialCoordinates d → ℝ))
    (_hloc : ∀ j, (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)),
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs hform hinverse tau htau sigma hsigma Grho hG hFmosco hEmoscoSub FForm hFForm
    hcmpAll hforms hcoreReg hcoerW hcutW hKNW hKstarW hFdom hcoeffW hloc
  have hzmem : ∀ j, z j ∈ (Q j : Set (SpatialCoordinates d)) := by
    intro j
    change z j ∈ Metric.ball (z j) (r j / 2)
    exact Metric.mem_ball_self (half_pos (hr j))
  have hhi_pos : ∀ j, 0 < hi j := by
    intro j
    have h := hrhobounds j (z j) (subset_closure (hzmem j))
    linarith [hlo j]
  -- G8: killed consistency of F via prop_killed_consistency_core_closure
  have hLowerF : ∀ j k (hjk : Q j ≤ Q k), ∀ u : H j, u ∈ (FForm j).toClosedForm.domain →
      ((FForm k).toClosedForm.energy (zeroExtensionLp hjk u) : EReal) ≤
        ((FForm j).toClosedForm.energy u : EReal) := by
    intro j k hjk
    exact aux_lem_weighted_cluster_lower_zeroExt d hd (z k) (z j) (r k) (r j) (hr k) (hr j) hjk
      (S k) (S j) (hS k) (hS j) (fun n => arho k (tau (sigma n)))
      (fun n => arho j (tau (sigma n))) (fun n => hcoeffW j k hjk _) (Grho k) (Grho j)
      (FForm k).toClosedForm (FForm j).toClosedForm (hFForm k) (hFForm j) (hFmosco k).1
      (hFmosco j).2
  exact aux_lem_weighted_cluster_principal_tail3b d hd J j0 z r hr hroot S hS A hAcont a arho
    ha rho hrhocont hrhopos lo hi hlo hlodef hhidef hrhobounds harho GN GrhoN hGN hGrhoN KN hKN
    Kstar hKstar H34sq hH34def hfrac hcoercive hInterp GE EForm hEForm hEnorm hEinj hEmosco
    hElower hEcore hEloc hEconsistent t ht htd hcutoffs hform hinverse tau htau sigma hsigma
    Grho hG hFmosco hEmoscoSub FForm hFForm hcmpAll hforms hcoreReg hcoerW hcutW hKNW hKstarW
    hFdom hcoeffW hloc hLowerF

/-- Second split-out tail (same heartbeat rationale as `aux_lem_weighted_cluster_principal_tail`:
the G1-G5 portion alone still exceeded the 200000-heartbeat budget together with the
weighted-inputs/G6/G8/G9 portion, so the latter is a further separate declaration taking the
G1-G5 outputs as hypotheses). -/
theorem aux_lem_weighted_cluster_principal_tail2
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u)
    (_hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤)
    (tau : ℕ → ℕ) (_htau : StrictMono tau)
    (sigma : ℕ → ℕ) (_hsigma : StrictMono sigma)
    (Grho : ∀ j, H j →L[ℝ] H j)
    (_hG : ∀ j, Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
      IsCompactOperator (Grho j) ∧
      (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
      (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
      Function.Injective (Grho j))
    (_hFmosco : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Grho j) u ≤
          liminf (fun n => ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (Grho j) u))))
    (_hEmoscoSub : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (GE j) u ≤
          liminf (fun n => ((responseForm (S j) (a j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (GE j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (a j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (GE j) u))))
    (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hFForm : ∀ j (u : H j), (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u)
    (_hcmpAll : ∀ j, limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
      ∀ u ∈ limitFormDomain (GE j),
        (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
        limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u)
    (_hforms : ∀ j, (∀ u, u ∈ (FForm j).toClosedForm.domain ↔ u ∈ (EForm j).domain) ∧
      ∀ u ∈ (EForm j).domain, lo j * (EForm j).form u u ≤ (FForm j).toClosedForm.form u u ∧
        (FForm j).toClosedForm.form u u ≤ hi j * (EForm j).form u u)
    (_hcoreReg : ∀ j, (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
      (Q j : Set (SpatialCoordinates d)) C) ∧ _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm),
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs hform hinverse tau htau sigma hsigma Grho hG hFmosco hEmoscoSub FForm hFForm
    hcmpAll hforms hcoreReg
  have hzmem : ∀ j, z j ∈ (Q j : Set (SpatialCoordinates d)) := by
    intro j
    change z j ∈ Metric.ball (z j) (r j / 2)
    exact Metric.mem_ball_self (half_pos (hr j))
  have hhi_pos : ∀ j, 0 < hi j := by
    intro j
    have h := hrhobounds j (z j) (subset_closure (hzmem j))
    linarith [hlo j]
  -- weighted inputs along tau ∘ sigma (coercivity with KN/lo, catalog cutoffs via A3)
  have hcoerW : ∀ j (n : ℕ) (w : (S j).space),
      ‖w.val.1‖ ^ 2 + volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        (KN j (tau (sigma n)) / lo j) * responseForm (S j) (arho j (tau (sigma n))) w w := by
    intro j n w
    rw [← hH34def j]
    exact aux_lem_weighted_cluster_weighted_coercive (S j) (a j (tau (sigma n)))
      (arho j (tau (sigma n))) (lo j) (KN j (tau (sigma n))) (hlo j) (hKN j _) (H34sq j) w
      (hcoercive j _ w) (hform j _ w).1
  have hcutW := fun j => aux_lem_weighted_cluster_weighted_cutoffs (z j) (r j) (hr j) t (S j)
    (a j) (fun n => arho j (tau (sigma n))) (fun n => tau (sigma n)) (hi j) (hhi_pos j).le
    (fun n => aux_lem_weighted_cluster_coeff_le (a j (tau (sigma n))) (arho j (tau (sigma n)))
      (A (tau (sigma n))) rho (ha j _) (harho j _) (hi j)
      (fun x hx => (hrhobounds j x (subset_closure hx)).2))
    (hcutoffs j)
  have hKNW : ∀ j (n : ℕ), 0 ≤ KN j (tau (sigma n)) / lo j := fun j n =>
    div_nonneg (hKN j _) (hlo j).le
  have hKstarW : ∀ j (n : ℕ), KN j (tau (sigma n)) / lo j ≤ Kstar j / lo j := fun j n =>
    (div_le_div_iff_of_pos_right (hlo j)).mpr (hKstar j _)
  have hFdom : ∀ j (v : H j), v ∈ (FForm j).toClosedForm.domain → v ∈ limitFormDomain (Grho j) := by
    intro j v hv
    show limitFormEnergy (Grho j) v < ⊤
    rw [← hFForm j]
    exact ((FForm j).toClosedForm.energy_lt_top_iff v).2 hv
  have hcoeffW : ∀ j k (_hjk : Q j ≤ Q k) (m : ℕ), ((arho k m).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
        ((arho j m).val : SpatialCoordinates d → ℝ) := by
    intro j k hjk m
    have h1 : ((arho k m).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] (fun x => rho x * A m x) :=
      ae_restrict_of_ae_restrict_of_subset
        (show (Q j : Set (SpatialCoordinates d)) ⊆ (Q k : Set (SpatialCoordinates d)) from hjk)
        (harho k m)
    exact h1.trans (harho j m).symm
  -- G6: strong locality on core, relative to Q j  (AUTHOR DECISION G6b: MemCoreOn (Q j))
  have hloc : ∀ j, (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0) := by
    intro j
    exact aux_lem_weighted_cluster_strongly_local d hd (z j) (r j) (hr j) (S j) (hS j)
      (fun n => arho j (tau (sigma n))) (Grho j)
      (fun f g => (real_inner_comm _ _).trans ((hG j).2.2.1 g f))
      (hFmosco j).1 (hFmosco j).2 (fun n => KN j (tau (sigma n)) / lo j) (hKNW j)
      (Kstar j / lo j) (hKstarW j) (hfrac j) (hcoerW j) hInterp t ht htd (hcutW j)
      (FForm j).toClosedForm (hFForm j)
  exact aux_lem_weighted_cluster_principal_tail3 d hd J j0 z r hr hroot S hS A hAcont a arho
    ha rho hrhocont hrhopos lo hi hlo hlodef hhidef hrhobounds harho GN GrhoN hGN hGrhoN KN hKN
    Kstar hKstar H34sq hH34def hfrac hcoercive hInterp GE EForm hEForm hEnorm hEinj hEmosco
    hElower hEcore hEloc hEconsistent t ht htd hcutoffs hform hinverse tau htau sigma hsigma
    Grho hG hFmosco hEmoscoSub FForm hFForm hcmpAll hforms hcoreReg hcoerW hcutW hKNW hKstarW
    hFdom hcoeffW hloc

/-- Third split-out piece (same heartbeat rationale): G3-G5 (existence of the weighted
Dirichlet form `FForm`, the domain/limit comparison, and core/regularity transfer), taking
G1-G2 (`hFmosco`, `hEmoscoSub`) as hypotheses and handing G3-G5's outputs on to
`aux_lem_weighted_cluster_principal_tail2`. -/
theorem aux_lem_weighted_cluster_principal_mid
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u)
    (_hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤)
    (tau : ℕ → ℕ) (_htau : StrictMono tau)
    (sigma : ℕ → ℕ) (_hsigma : StrictMono sigma)
    (Grho : ∀ j, H j →L[ℝ] H j)
    (_hG : ∀ j, Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
      IsCompactOperator (Grho j) ∧
      (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
      (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
      Function.Injective (Grho j))
    (_hFmosco : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Grho j) u ≤
          liminf (fun n => ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (Grho j) u))))
    (_hEmoscoSub : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (GE j) u ≤
          liminf (fun n => ((responseForm (S j) (a j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (GE j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (a j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (GE j) u)))),
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs hform hinverse tau htau sigma hsigma Grho hG hFmosco hEmoscoSub
  have hzmem : ∀ j, z j ∈ (Q j : Set (SpatialCoordinates d)) := by
    intro j
    change z j ∈ Metric.ball (z j) (r j / 2)
    exact Metric.mem_ball_self (half_pos (hr j))
  have hhi_pos : ∀ j, 0 < hi j := by
    intro j
    have h := hrhobounds j (z j) (subset_closure (hzmem j))
    linarith [hlo j]
  -- G3: the Dirichlet form of Grho j
  have hFexists : ∀ j, ∃ F : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (Q j : Set (SpatialCoordinates d))),
      ∀ u : H j, F.toClosedForm.energy u = limitFormEnergy (Grho j) u := by
    intro j
    obtain ⟨R, hR⟩ := prop_killed_inverse_spectral_square_root (Grho j) (hG j).2.1
      (hG j).2.2.1 (hG j).2.2.2.1 (hG j).2.2.2.2
    have hfin : volume (Q j : Set (SpatialCoordinates d)) ≠ ⊤ := by
      change volume (Metric.ball (z j) (r j / 2)) ≠ ⊤
      exact measure_ball_lt_top.ne
    exact aux_lem_weighted_cluster_dirichlet_form (S j) (fun n => arho j (tau (sigma n)))
      (Grho j) (hG j).2.2.1 (hG j).2.2.2.1 (hG j).2.2.2.2 ⟨R, hR⟩ (hFmosco j)
      (fun n u ε hε => aux_lem_weighted_cluster_unitTruncation_approx (S j) (hS j) hfin _ u ε hε)
  choose FForm hFForm using hFexists
  -- G4: domain equality and two-sided limit bounds
  have hcmpAll : ∀ j, limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
      ∀ u ∈ limitFormDomain (GE j),
        (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
        limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u := by
    intro j
    exact aux_lem_weighted_cluster_limit_comparison (S j) (fun n => a j (tau (sigma n)))
      (fun n => arho j (tau (sigma n))) (GE j) (Grho j) (lo j) (hi j) (hlo j) (hhi_pos j).le
      (fun n u => hform j (tau (sigma n)) u) (hEmoscoSub j).1 (hEmoscoSub j).2
      (hFmosco j).1 (hFmosco j).2
  have hforms : ∀ j, (∀ u, u ∈ (FForm j).toClosedForm.domain ↔ u ∈ (EForm j).domain) ∧
      ∀ u ∈ (EForm j).domain, lo j * (EForm j).form u u ≤ (FForm j).toClosedForm.form u u ∧
        (FForm j).toClosedForm.form u u ≤ hi j * (EForm j).form u u := fun j =>
    aux_lem_weighted_cluster_forms_of_limit (EForm j) (FForm j).toClosedForm (GE j) (Grho j)
      (hEForm j) (hFForm j) (lo j) (hi j) (hcmpAll j).1 (hcmpAll j).2
  -- G5: core and regularity transferred from E
  have hmU : ∀ j, (volume.restrict (Q j : Set (SpatialCoordinates d)))
      (Q j : Set (SpatialCoordinates d))ᶜ = 0 := by
    intro j
    rw [Measure.restrict_apply' (Q j).isOpen.measurableSet]
    simp
  have hcoreReg : ∀ j, (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
      (Q j : Set (SpatialCoordinates d)) C) ∧ _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm :=
    fun j => aux_lem_weighted_cluster_core_transfer (EForm j) (FForm j).toClosedForm
      (Q j : Set (SpatialCoordinates d)) (Q j).isOpen (hmU j) (hforms j).1 (hi j)
      (fun u hu => ((hforms j).2 u hu).2) (hEcore j)
  exact aux_lem_weighted_cluster_principal_tail2 d hd J j0 z r hr hroot S hS A hAcont a arho ha
    rho hrhocont hrhopos lo hi hlo hlodef hhidef hrhobounds harho GN GrhoN hGN hGrhoN KN hKN
    Kstar hKstar H34sq hH34def hfrac hcoercive hInterp GE EForm hEForm hEnorm hEinj hEmosco
    hElower hEcore hEloc hEconsistent t ht htd hcutoffs hform hinverse tau htau sigma hsigma
    Grho hG hFmosco hEmoscoSub FForm hFForm hcmpAll hforms hcoreReg

/-- Fourth split-out piece (same heartbeat rationale): G2 (the unweighted Mosco convergence
of `GE` along `tau ∘ sigma`), taking G1 (`hFmosco`, plus `sigma`/`Grho`/`hG`) as hypotheses and
handing on to `aux_lem_weighted_cluster_principal_mid`. -/
theorem aux_lem_weighted_cluster_principal_tail_g2
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u)
    (_hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤)
    (tau : ℕ → ℕ) (_htau : StrictMono tau)
    (sigma : ℕ → ℕ) (_hsigma : StrictMono sigma)
    (Grho : ∀ j, H j →L[ℝ] H j)
    (_hG : ∀ j, Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
      IsCompactOperator (Grho j) ∧
      (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
      (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
      Function.Injective (Grho j))
    (_hFmosco : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Grho j) u ≤
          liminf (fun n => ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (Grho j) u)))),
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs hform hinverse tau htau sigma hsigma Grho hG hFmosco
  have hGlim : ∀ j f, Tendsto (fun n =>
      (responseSolution (S j) (a j n)
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop (𝓝 (GE j f)) := by
    intro j f
    have h : Tendsto (fun n => GN j n f) atTop (𝓝 (GE j f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto (GE j)).comp (hEnorm j)
    simpa only [hGN] using h
  
  have hGNpt : ∀ j (x : H j), Tendsto (fun n => GN j n x) atTop (𝓝 (GE j x)) := fun j x =>
    ((continuous_id.clm_apply continuous_const).tendsto (GE j)).comp (hEnorm j)
  have hGEsym : ∀ j (x y : H j), inner ℝ (GE j x) y = inner ℝ x (GE j y) := by
    intro j x y
    have h1 : Tendsto (fun n => inner ℝ (GN j n x) y) atTop (𝓝 (inner ℝ (GE j x) y)) :=
      (hGNpt j x).inner tendsto_const_nhds
    have h2 : Tendsto (fun n => inner ℝ x (GN j n y)) atTop (𝓝 (inner ℝ x (GE j y))) :=
      tendsto_const_nhds.inner (hGNpt j y)
    have heq : ∀ n, inner ℝ (GN j n x) y = inner ℝ x (GN j n y) := by
      intro n
      rw [hGN, hGN, real_inner_comm]
      exact volumeResponse_pairing_symm (S j) (a j n) y x
    exact tendsto_nhds_unique (h1.congr heq) h2
  have hGEpos : ∀ j (x : H j), 0 ≤ inner ℝ x (GE j x) := by
    intro j x
    have h : Tendsto (fun n => inner ℝ x (GN j n x)) atTop (𝓝 (inner ℝ x (GE j x))) :=
      tendsto_const_nhds.inner (hGNpt j x)
    exact ge_of_tendsto' h (fun n => by
      rw [hGN]
      exact volumeResponse_pairing_nonneg (S j) (a j n) x)
  have hEmoscoSub : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (GE j) u ≤
          liminf (fun n => ((responseForm (S j) (a j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (GE j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (a j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (GE j) u))) := by
    intro j
    have hstrong : ∀ f : H j, Tendsto (fun n => (responseSolution (S j) (a j (tau (sigma n)))
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop (𝓝 (GE j f)) := by
      intro f
      simpa only [Function.comp_apply] using!
        (hGlim j f).comp ((htau.comp hsigma).tendsto_atTop)
    refine killedInverse_mosco (S j) (fun n => a j (tau (sigma n))) (GE j)
      (hGEsym j) (hGEpos j) hstrong ?_
    intro f
    have h : Tendsto (fun n => inner ℝ f (responseSolution (S j) (a j (tau (sigma n)))
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop
        (𝓝 (inner ℝ f (GE j f))) := tendsto_const_nhds.inner (hstrong f)
    refine h.congr (fun n => ?_)
    exact (inverseResponse_eq_load (S j) (a j (tau (sigma n)))
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).symm
  exact aux_lem_weighted_cluster_principal_mid d hd J j0 z r hr hroot S hS A hAcont a arho ha
    rho hrhocont hrhopos lo hi hlo hlodef hhidef hrhobounds harho GN GrhoN hGN hGrhoN KN hKN
    Kstar hKstar H34sq hH34def hfrac hcoercive hInterp GE EForm hEForm hEnorm hEinj hEmosco
    hElower hEcore hEloc hEconsistent t ht htd hcutoffs hform hinverse tau htau sigma hsigma
    Grho hG hFmosco hEmoscoSub

/-- Split-out tail of the principal proof (heartbeat budget: the combined
`hform`/`hinverse`/tau-clause proof exceeds the default 200000-heartbeat budget in one
declaration; splitting into a second top-level declaration gives it a fresh budget without
raising `maxHeartbeats`). Computes G1 (`hFmosco`, plus `sigma`/`Grho`/`hG`) and hands on to
`aux_lem_weighted_cluster_principal_tail_g2`. -/
theorem aux_lem_weighted_cluster_principal_tail
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (_hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u)
    (_hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤)
    (tau : ℕ → ℕ) (_htau : StrictMono tau),
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs hform hinverse tau htau
  have hGlim : ∀ j f, Tendsto (fun n =>
      (responseSolution (S j) (a j n)
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop (𝓝 (GE j f)) := by
    intro j f
    have h : Tendsto (fun n => GN j n f) atTop (𝓝 (GE j f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto (GE j)).comp (hEnorm j)
    simpa only [hGN] using h
  obtain ⟨sigma, hsigma, Grho, hG⟩ := lem_weighted_cluster_limit_cluster d hd J z r hr S hS a arho
    GrhoN hGrhoN KN hKN Kstar hKstar GE hEinj hGlim H34sq hH34def hfrac lo hi hlo hform hInterp
    hinverse tau htau
  
  have hFmosco : ∀ j,
      (∀ (uN : ℕ → (S j).space) (u : H j),
        (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Grho j) u ≤
          liminf (fun n => ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) :
            EReal)) atTop) ∧
      (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
        Tendsto (fun n => ((w n).val.1,
          ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy (Grho j) u))) := by
    intro j
    have hstrong : ∀ f : H j, Tendsto (fun n => (responseSolution (S j) (arho j (tau (sigma n)))
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop (𝓝 (Grho j f)) := by
      intro f
      have h : Tendsto (fun n => GrhoN j (tau (sigma n)) f) atTop (𝓝 (Grho j f)) :=
        ((continuous_id.clm_apply continuous_const).tendsto (Grho j)).comp (hG j).1
      simpa only [hGrhoN] using h
    refine killedInverse_mosco (S j) (fun n => arho j (tau (sigma n))) (Grho j)
      (hG j).2.2.1 (hG j).2.2.2.1 hstrong ?_
    intro f
    have h : Tendsto (fun n => inner ℝ f (responseSolution (S j) (arho j (tau (sigma n)))
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop
        (𝓝 (inner ℝ f (Grho j f))) := tendsto_const_nhds.inner (hstrong f)
    refine h.congr (fun n => ?_)
    exact (inverseResponse_eq_load (S j) (arho j (tau (sigma n)))
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).symm
  exact aux_lem_weighted_cluster_principal_tail_g2 d hd J j0 z r hr hroot S hS A hAcont a arho
    ha rho hrhocont hrhopos lo hi hlo hlodef hhidef hrhobounds harho GN GrhoN hGN hGrhoN KN hKN
    Kstar hKstar H34sq hH34def hfrac hcoercive hInterp GE EForm hEForm hEnorm hEinj hEmosco
    hElower hEcore hEloc hEconsistent t ht htd hcutoffs hform hinverse tau htau sigma hsigma
    Grho hG hFmosco

/--
- paper label `mfd:prop-21`, every clause and correct quantifier order;
- concrete countable cube family/one represented sequence, common A and rho; same coefficient on overlaps;
- hS pins the killed domain, hGN/hGrhoN pin all inverses;
- KN j n is the original indexed coercivity constant; Kstar only for extraction;
- hH34def/hfrac pin a finite actual fractional norm, using the fixed-cube equivalent norm convention;
- unweighted Mosco/injectivity/norm convergence from prop_killed_inverse;
- regularity/locality/consistency of E from those preceding nodes;
- unweighted cutoff bounds from catalog_cutoff_existence and catalog selection; lem_19 supplies the published fractional compactness/interpolation input;
- conclusions quantified on each native L2 cube; zero extension image is a killed submodule, no false ambient-density assumption;
- all weighted statements remain conclusions; no new proof is attempted.
- actual-cube core from prop_regularity first conjunct, not merely some full-measure open set.
- the pointwise form comparison, inverse H^{3/4} bound, and simultaneous
  cluster/Mosco/local-comparison package are exposed as the fine children
  `lem_weighted_cluster_form_bounds`, `lem_weighted_cluster_inverse_bounds`,
  and `lem_weighted_cluster_limit_cluster`; these are proof conclusions, not
  carried premises.
-/
theorem lem_weighted_cluster
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (_hroot : ∀ j, Q j ≤ Q j0)
    (S : ∀ j, ResponseSpace (Q j))
    (_hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (_hAcont : ∀ n, ContinuousOn (A n) (closure (Q j0 : Set (SpatialCoordinates d))))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (_ha : ∀ j n, (a j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (_hrhocont : ContinuousOn rho (closure (Q j0 : Set (SpatialCoordinates d))))
    (_hrhopos : ∀ x ∈ closure (Q j0 : Set (SpatialCoordinates d)), 0 < rho x)
    (lo hi : J → ℝ) (_hlo : ∀ j, 0 < lo j)
    (_hlodef : ∀ j, lo j = sInf (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hhidef : ∀ j, hi j = sSup (rho '' closure (Q j : Set (SpatialCoordinates d))))
    (_hrhobounds : ∀ j x, x ∈ closure (Q j : Set (SpatialCoordinates d)) →
      lo j ≤ rho x ∧ rho x ≤ hi j)
    (_harho : ∀ j n, (arho j n).val =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x))
    (GN GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (_hGN : ∀ j n f, GN j n f = (responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (_hGrhoN : ∀ j n f, GrhoN j n f = (responseSolution (S j) (arho j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (_hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (_hKstar : ∀ j n, KN j n ≤ Kstar j)
    (H34sq : ∀ j, H j → ℝ)
    (_hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (_hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (_hcoercive : ∀ j n (u : (S j).space),
      H34sq j u.val.1 ≤ KN j n * responseForm (S j) (a j n) u u)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (GE : ∀ j, H j →L[ℝ] H j)
    (EForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q j : Set (SpatialCoordinates d))))
    (_hEForm : ∀ j u, (EForm j).energy u = limitFormEnergy (GE j) u)
    (_hEnorm : ∀ j, Tendsto (GN j) atTop (𝓝 (GE j)))
    (_hEinj : ∀ j, Function.Injective (GE j))
    (_hEmosco : ∀ j u, u ∈ limitFormDomain (GE j) → ∃ w : ℕ → (S j).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (S j) (a j n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy (GE j) u)))
    (_hElower : ∀ j (uN : ℕ → (S j).space) (u : H j),
      (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy (GE j) u ≤
        liminf (fun n => ((responseForm (S j) (a j n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hEcore : ∀ j, ∃ C : Set (H j),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (EForm j) (Q j : Set (SpatialCoordinates d)) C)
    (_hEloc : ∀ j, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore (EForm j))
    (_hEconsistent : ∀ j k (hjk : Q j ≤ Q k),
      (∃ D : Submodule ℝ (H k),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (EForm k) (Q j : Set (SpatialCoordinates d)) D ∧
        (∀ w : H k, w ∈ D ↔ ∃ u : H j, u ∈ (EForm j).domain ∧ zeroExtensionLp hjk u = w)) ∧
      (∀ u ∈ (EForm j).domain,
        (EForm k).energy (zeroExtensionLp hjk u) = (EForm j).energy u))
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ j (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q j : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q j : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q j : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (S j) (a j n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q j : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q j : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a j n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))),
    (∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u) ∧
    (∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤) ∧
    (∀ tau : ℕ → ℕ, StrictMono tau → ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (Grho : ∀ j, H j →L[ℝ] H j)
        (FForm : ∀ j, _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q j : Set (SpatialCoordinates d)))),
        (∀ j,
          Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
          IsCompactOperator (Grho j) ∧
          (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
          (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
          Function.Injective (Grho j) ∧
          (∀ u : H j, (FForm j).toClosedForm.energy u = limitFormEnergy (Grho j) u) ∧
          (∀ u ∈ limitFormDomain (Grho j), ∃ w : ℕ → (S j).space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm (S j) (arho j (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy (Grho j) u))) ∧
          (∀ (uN : ℕ → (S j).space) (u : H j),
            (∀ f : H j, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (Grho j) u ≤ liminf (fun n =>
              ((responseForm (S j) (arho j (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
          limitFormDomain (Grho j) = limitFormDomain (GE j) ∧
          (∀ u ∈ limitFormDomain (GE j),
            (lo j : EReal) * limitFormEnergy (GE j) u ≤ limitFormEnergy (Grho j) u ∧
            limitFormEnergy (Grho j) u ≤ (hi j : EReal) * limitFormEnergy (GE j) u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (FForm j).toClosedForm ∧
          (∃ C : Set (H j), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (FForm j).toClosedForm
            (Q j : Set (SpatialCoordinates d)) C) ∧
          (∀ u v : H j,
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) u →
      (FForm j).toClosedForm.MemCoreOn (Q j : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q j : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (Q j : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (Q j : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → (FForm j).toClosedForm.form u v = 0)) ∧
        (∀ j k (hjk : Q j ≤ Q k),
          ((∃ D : Submodule ℝ (H k),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (FForm k).toClosedForm (Q j : Set (SpatialCoordinates d)) D ∧
            (∀ w : H k, w ∈ D ↔ ∃ u : H j,
              u ∈ (FForm j).toClosedForm.domain ∧ zeroExtensionLp hjk u = w)) ∧
          (∀ u ∈ (FForm j).toClosedForm.domain,
            (FForm k).toClosedForm.energy (zeroExtensionLp hjk u) = (FForm j).toClosedForm.energy u)) ∧
          ∀ u ∈ (EForm j).domain,
            sInf (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u ≤
              (FForm j).toClosedForm.form u u ∧
            (FForm j).toClosedForm.form u u ≤
              sSup (rho '' (Q j : Set (SpatialCoordinates d))) * (EForm j).form u u)) := by
  intro Q H hroot S hS A hAcont a arho ha rho hrhocont hrhopos lo hi hlo hlodef hhidef
    hrhobounds harho GN GrhoN hGN hGrhoN KN hKN Kstar hKstar H34sq hH34def hfrac hcoercive
    hInterp GE EForm hEForm hEnorm hEinj hEmosco hElower hEcore hEloc hEconsistent t ht htd
    hcutoffs
  have hsub : ∀ j, (Q j : Set (SpatialCoordinates d)) ⊆ (Q j0 : Set (SpatialCoordinates d)) :=
    fun j => hroot j
  have hzmem : ∀ j, z j ∈ (Q j : Set (SpatialCoordinates d)) := by
    intro j
    change z j ∈ Metric.ball (z j) (r j / 2)
    exact Metric.mem_ball_self (half_pos (hr j))
  have hhi_pos : ∀ j, 0 < hi j := by
    intro j
    have h := hrhobounds j (z j) (subset_closure (hzmem j))
    linarith [hlo j]
  -- clause (i): closed child
  have hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤ responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤ hi j * responseForm (S j) (a j n) u u := by
    intro j
    exact lem_weighted_cluster_form_bounds d hd (z j) (r j) (hr j) (S j) (hS j) (a j) (arho j) A
      (ha j) rho (hrhocont.mono (closure_mono (hsub j)))
      (fun x hx => hrhopos x (closure_mono (hsub j) hx)) (lo j) (hi j) (hlo j) (hlodef j)
      (hhidef j) (hrhobounds j) (harho j)
  -- clause (ii): closed child
  have hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN j n f) < ⊤ := by
    intro j
    exact lem_weighted_cluster_inverse_bounds d hd (z j) (r j) (hr j) (S j) (hS j) (a j) (arho j)
      (lo j) (hi j) (hlo j) (GrhoN j) (hGrhoN j) (KN j) (hKN j) (H34sq j) (hH34def j) (hfrac j)
      (hcoercive j) (hform j)
  refine ⟨hform, hinverse, ?_⟩
  intro tau htau
  exact aux_lem_weighted_cluster_principal_tail d hd J j0 z r hr hroot S hS A hAcont a arho ha
    rho hrhocont hrhopos lo hi hlo hlodef hhidef hrhobounds harho GN GrhoN hGN hGrhoN KN hKN
    Kstar hKstar H34sq hH34def hfrac hcoercive hInterp GE EForm hEForm hEnorm hEinj hEmosco
    hElower hEcore hEloc hEconsistent t ht htd hcutoffs hform hinverse tau htau

end SubdiffusiveProcess.Paper
