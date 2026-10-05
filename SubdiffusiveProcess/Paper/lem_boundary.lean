module

public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import Mathlib.Tactic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import SubdiffusiveProcess.Paper.boundary_cell_count
public import SubdiffusiveProcess.Paper.lem_goodext
public import SubdiffusiveProcess.Paper.lem_skeleton
public import SubdiffusiveProcess.Paper.parameter_chain
public import SubdiffusiveProcess.Paper.prop_allchain
public import SubdiffusiveProcess.Paper.prop_density_core_closure
public import SubdiffusiveProcess.Paper.prop_density_core_comparison
public import SubdiffusiveProcess.Paper.prop_density_core_approximation
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.reference_coefficients
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper
noncomputable section

/-! ### Closure and energy density for the limiting forms

The limiting forms are the dual energies `limitFormEnergy G u = sup_f (2<f,u> - <f,Gf>)` of the
limiting inverse operators.  The helpers below are the closedness of `F` (a supremum of continuous
affine functions is lower semicontinuous), the energy density of the smooth-source range of `G_E`
(positive-shift resolvents plus density of the catalogue sources), and the passage
`cFloor -> 0` / `r_0 -> 0` / `J -> infinity` of the paper's "Gluing and closure" paragraph. -/

/-- Norm limits of the actual killed volume-response operators are symmetric and positive. -/
theorem aux_lem_boundary_limit_sym_pos {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (Gn : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGn : ∀ n f, Gn n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : Tendsto Gn atTop (𝓝 G)) :
    (∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) := by
  have happ : ∀ x : DomainL2 Q, Tendsto (fun n => Gn n x) atTop (𝓝 (G x)) := fun x =>
    ((continuous_id.clm_apply continuous_const).tendsto G).comp hlim
  constructor
  · intro x y
    have h1 : Tendsto (fun n => inner ℝ (Gn n x) y) atTop (𝓝 (inner ℝ (G x) y)) :=
      (happ x).inner tendsto_const_nhds
    have h2 : Tendsto (fun n => inner ℝ x (Gn n y)) atTop (𝓝 (inner ℝ x (G y))) :=
      tendsto_const_nhds.inner (happ y)
    have heq : ∀ n, inner ℝ (Gn n x) y = inner ℝ x (Gn n y) := by
      intro n
      rw [hGn, hGn, real_inner_comm]
      exact volumeResponse_pairing_symm S (a n) y x
    exact tendsto_nhds_unique (h1.congr heq) h2
  · intro x
    have h1 : Tendsto (fun n => inner ℝ x (Gn n x)) atTop (𝓝 (inner ℝ x (G x))) :=
      tendsto_const_nhds.inner (happ x)
    refine ge_of_tendsto' h1 (fun n => ?_)
    rw [hGn]
    exact volumeResponse_pairing_nonneg S (a n) x

/-- A lower semicontinuous functional is bounded by `b` at `x` if it is bounded by `b + eps`
at points within `eps` of `x`. -/
theorem aux_lem_boundary_lsc_le {X : Type*} [NormedAddCommGroup X]
    (φ : X → EReal) (hφ : LowerSemicontinuous φ) (x : X) (b : ℝ)
    (h : ∀ eps : ℝ, 0 < eps → ∃ w : X, ‖w - x‖ ≤ eps ∧ φ w ≤ ((b + eps : ℝ) : EReal)) :
    φ x ≤ (b : EReal) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, hby, hyx⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hby' : b < y := EReal.coe_lt_coe_iff.mp hby
  have hev := hφ x (y : EReal) hyx
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set e : ℝ := min (ε / 2) ((y - b) / 2) with he
  have he0 : 0 < e := lt_min (by linarith) (by linarith)
  have he1 : e ≤ ε / 2 := min_le_left _ _
  have he2 : e ≤ (y - b) / 2 := min_le_right _ _
  obtain ⟨w, hw1, hw2⟩ := h e he0
  have hdist : dist w x < ε := by
    rw [dist_eq_norm]
    linarith
  have hyw := hball hdist
  have h3 : (y : EReal) < ((b + e : ℝ) : EReal) := lt_of_lt_of_le hyw hw2
  have h4 := EReal.coe_lt_coe_iff.mp h3
  linarith

/-- Energy density of a dense source family: every finite-energy vector is approximated in norm
by `G f`, `f` in the family, with `<f, G f>` at most its energy plus `eps`. -/
theorem aux_lem_boundary_dense_energy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : H, 0 ≤ inner ℝ x (G x))
    (D : Set H) (hD : Dense D) (u : H) (e : ℝ)
    (he : (⨆ f : H, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) = (e : EReal)) :
    ∀ eps : ℝ, 0 < eps → ∃ f ∈ D, ‖G f - u‖ ≤ eps ∧ inner ℝ f (G f) ≤ e + eps := by
  intro eps heps
  choose R hR using fun n : ℕ =>
    existsUnique_positive_shift_inverse G hsym hpos (1 / (n + 1 : ℝ)) (by positivity)
  have hbase := tendsto_positive_shift_energy_approximation G R hsym hpos
    (fun n => (hR n).1.1) u e he
  have hG : Tendsto (fun n => G (R n u)) atTop (𝓝 u) :=
    (continuous_fst.tendsto _).comp hbase
  have hq : Tendsto (fun n => inner ℝ (R n u) (G (R n u))) atTop (𝓝 e) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hbase
  have hev1 : ∀ᶠ n in atTop, ‖G (R n u) - u‖ < eps / 2 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hG).eventually (gt_mem_nhds (half_pos heps))
  have hev2 : ∀ᶠ n in atTop, inner ℝ (R n u) (G (R n u)) < e + eps / 2 :=
    hq.eventually (gt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  set p : H := R n u with hp
  let U : Set H := {y | ‖G y - G p‖ < eps / 2} ∩
    {y | inner ℝ y (G y) < inner ℝ p (G p) + eps / 2}
  have hUo : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt ((G.continuous.sub continuous_const).norm) continuous_const
    · exact isOpen_lt (continuous_id.inner G.continuous) continuous_const
  have hpU : p ∈ U := by
    refine ⟨?_, ?_⟩
    · show ‖G p - G p‖ < eps / 2
      rw [sub_self, norm_zero]
      exact half_pos heps
    · show inner ℝ p (G p) < inner ℝ p (G p) + eps / 2
      linarith
  obtain ⟨f, hfD, hfU⟩ := hD.exists_mem_open hUo ⟨p, hpU⟩
  have hf1 : ‖G f - G p‖ < eps / 2 := hfU.1
  have hf2 : inner ℝ f (G f) < inner ℝ p (G p) + eps / 2 := hfU.2
  refine ⟨f, hfD, ?_, ?_⟩
  · calc ‖G f - u‖ = ‖(G f - G p) + (G p - u)‖ := by congr 1; abel
      _ ≤ ‖G f - G p‖ + ‖G p - u‖ := norm_add_le _ _
      _ ≤ eps := by linarith
  · linarith

/-- Closedness plus energy density: a comparison with an additive floor on the image of a dense
source family extends to the whole limiting form domain. -/
theorem aux_lem_boundary_closure {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (GE x) y = inner ℝ x (GE y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (GE x))
    (D : Set (DomainL2 Q)) (hD : Dense D) (C V : ℝ) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (happrox : ∀ f ∈ D, ∀ c : ℝ, 0 < c → ∀ eps : ℝ, 0 < eps → ∃ w : DomainL2 Q,
      ‖w - GE f‖ ≤ eps ∧
        limitFormEnergy GF w ≤
          ((C * ((limitFormEnergy GE (GE f)).toReal + c * V) + eps : ℝ) : EReal)) :
    ∀ u : DomainL2 Q, u ∈ limitFormDomain GE →
      limitFormEnergy GF u ≤ ((C * (limitFormEnergy GE u).toReal : ℝ) : EReal) := by
  have hlsc : LowerSemicontinuous (fun u : DomainL2 Q => limitFormEnergy GF u) :=
    lowerSemicontinuous_iSup_quadraticDual GF
  have hEimg : ∀ f, limitFormEnergy GE (GE f) = ((inner ℝ f (GE f) : ℝ) : EReal) :=
    fun f => iSup_quadraticDual_apply_image GE hsym hpos f
  have hCV : 0 ≤ C * V := mul_nonneg hC hV
  -- the smooth-source core: `F(G_E f) ≤ C E(G_E f)`
  have hcore : ∀ f ∈ D,
      limitFormEnergy GF (GE f) ≤ ((C * inner ℝ f (GE f) : ℝ) : EReal) := by
    intro f hf
    apply aux_lem_boundary_lsc_le _ hlsc
    intro eps heps
    set c : ℝ := eps / (2 * (C * V + 1)) with hc
    have hc0 : 0 < c := by rw [hc]; positivity
    obtain ⟨w, hw1, hw2⟩ := happrox f hf c hc0 (eps / 2) (half_pos heps)
    refine ⟨w, hw1.trans (by linarith), hw2.trans ?_⟩
    rw [EReal.coe_le_coe_iff, hEimg, EReal.toReal_coe]
    have hkey : C * (c * V) * (2 * (C * V + 1)) = C * V * eps := by
      rw [hc]; field_simp
    have hsmall : C * (c * V) ≤ eps / 2 := by
      have h2 : C * (c * V) * (2 * (C * V + 1)) ≤ eps / 2 * (2 * (C * V + 1)) := by
        rw [hkey]; nlinarith
      exact le_of_mul_le_mul_right h2 (by positivity)
    calc C * (inner ℝ f (GE f) + c * V) + eps / 2
        = C * inner ℝ f (GE f) + C * (c * V) + eps / 2 := by ring
      _ ≤ C * inner ℝ f (GE f) + eps := by linarith
  -- energy density on the whole domain
  intro u hu
  have hne_top : limitFormEnergy GE u ≠ ⊤ := ne_of_lt hu
  have hne_bot : limitFormEnergy GE u ≠ ⊥ :=
    (EReal.bot_lt_zero.trans_le (limitFormEnergy_nonneg GE u)).ne'
  set e : ℝ := (limitFormEnergy GE u).toReal with he_def
  have he : limitFormEnergy GE u = (e : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
  apply aux_lem_boundary_lsc_le _ hlsc
  intro eps heps
  set δ : ℝ := eps / (C + 1) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδle : δ ≤ eps := div_le_self heps.le (by linarith)
  have hCδ : C * δ ≤ eps := by
    have h1 : C * δ * (C + 1) = C * eps := by rw [hδ]; field_simp
    have h2 : C * δ * (C + 1) ≤ eps * (C + 1) := by rw [h1]; nlinarith
    exact le_of_mul_le_mul_right h2 (by linarith)
  obtain ⟨f, hfD, hf1, hf2⟩ := aux_lem_boundary_dense_energy GE hsym hpos D hD u e he δ hδ0
  refine ⟨GE f, hf1.trans hδle, (hcore f hfD).trans ?_⟩
  rw [EReal.coe_le_coe_iff]
  have : C * inner ℝ f (GE f) ≤ C * (e + δ) := mul_le_mul_of_nonneg_left hf2 hC
  linarith

/-- A uniform bound on representatives on the cube bounds the `L²` distance. -/
theorem aux_lem_boundary_L2_le_of_uniform {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (v u : DomainL2 (centeredCube z r hr)) (vRep uRep : SpatialCoordinates d → ℝ)
    (hv : (v : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vRep)
    (hu : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uRep)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hunif : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      |vRep x - uRep x| ≤ eps) :
    ‖v - u‖ ≤ ((measureUnivNNReal
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) + 1) * eps := by
  have hmem : ∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet
  have hae : ∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      ‖((v - u : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x‖ ≤ eps := by
    filter_upwards [Lp.coeFn_sub v u, hv, hu, hmem] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]
    exact hunif x h4
  have h := Lp.norm_le_of_ae_bound heps hae
  set t : ℝ := (measureUnivNNReal
    (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) with ht
  have ht0 : 0 ≤ t := NNReal.coe_nonneg _
  have hexp : (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) := by norm_num
  have hpow : t ^ (2 : ℝ≥0∞).toReal⁻¹ ≤ t + 1 := by
    rw [hexp]
    rcases le_total t 1 with h1 | h1
    · have : t ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one ht0 h1 (by norm_num)
      linarith
    · have : t ^ (1 / 2 : ℝ) ≤ t ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      rw [Real.rpow_one] at this
      linarith
  calc ‖v - u‖ ≤ t ^ (2 : ℝ≥0∞).toReal⁻¹ * eps := h
    _ ≤ (t + 1) * eps := mul_le_mul_of_nonneg_right hpow heps

/-- The finite-horizon approximation of a smooth-source solution (uniform on the cube, with the
`cFloor * |Q|` floor) gives `L²`-close competitors with the energy bound in `EReal` form. -/
theorem aux_lem_boundary_approx_of_core {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r)
    (GE GF : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (C : ℝ) (f : DomainL2 (centeredCube z r hr))
    (hcore : ∀ cFloor : ℝ, 0 < cFloor →
      ∃ uRep : SpatialCoordinates d → ℝ,
        ∃ v : ℕ → DomainL2 (centeredCube z r hr),
        ∃ vRep : ℕ → SpatialCoordinates d → ℝ,
          ContinuousOn uRep (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((GE f : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uRep) ∧
          (∀ J, v J ∈ limitFormDomain GF) ∧
          (∀ J, ContinuousOn (vRep J)
            (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) ∧
          (∀ J, (v J : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (vRep J)) ∧
          (∀ eps : ℝ, 0 < eps →
            ∃ J0 : ℕ, ∀ J ≥ J0,
              (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
                |vRep J x - uRep x| ≤ eps) ∧
              (limitFormEnergy GF (v J)).toReal ≤
                C * ((limitFormEnergy GE (GE f)).toReal +
                  cFloor * (volume (centeredCube z r hr :
                    Set (SpatialCoordinates d))).toReal) + eps)) :
    ∀ c : ℝ, 0 < c → ∀ eps : ℝ, 0 < eps → ∃ w : DomainL2 (centeredCube z r hr),
      ‖w - GE f‖ ≤ eps ∧
        limitFormEnergy GF w ≤
          ((C * ((limitFormEnergy GE (GE f)).toReal +
            c * (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) +
              eps : ℝ) : EReal) := by
  intro c hc eps heps
  obtain ⟨uRep, v, vRep, -, hu, hvdom, -, hv, hJ⟩ := hcore c hc
  set K : ℝ := (measureUnivNNReal
    (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) with hK
  have hK0 : 0 ≤ K := NNReal.coe_nonneg _
  set e' : ℝ := eps / (K + 1) with he'
  have he'0 : 0 < e' := by rw [he']; positivity
  have he'le : e' ≤ eps := div_le_self heps.le (by linarith)
  obtain ⟨J0, hJ0⟩ := hJ e' he'0
  obtain ⟨hunif, hen⟩ := hJ0 J0 le_rfl
  refine ⟨v J0, ?_, ?_⟩
  · have h := aux_lem_boundary_L2_le_of_uniform z r hr (v J0) (GE f) (vRep J0) uRep
      (hv J0) hu e' he'0.le hunif
    calc ‖v J0 - GE f‖ ≤ (K + 1) * e' := h
      _ = eps := by rw [he']; field_simp
  · have htop : limitFormEnergy GF (v J0) ≠ ⊤ := ne_of_lt (hvdom J0)
    have hbot : limitFormEnergy GF (v J0) ≠ ⊥ :=
      (EReal.bot_lt_zero.trans_le (limitFormEnergy_nonneg GF _)).ne'
    rw [← EReal.coe_toReal htop hbot, EReal.coe_le_coe_iff]
    linarith

/-- Clause D (density of the rational source catalogue) of `conv_represented_estimates`. -/
theorem aux_lem_boundary_catalogue_dense
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
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey) :
    ∀ i, Dense (Dcat i : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDense, -⟩ := h
  exact hDense

/-! ### The continuous Hölder representative of `u = G_E g` (`eq:mfd-5`) -/

/-- The sup distance is at most the Euclidean length used by `holderRatioSet`. -/
theorem aux_lem_boundary_dist_le_eucl {d : ℕ} (x y : SpatialCoordinates d) :
    dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  rw [dist_pi_le_iff (Real.sqrt_nonneg _)]
  intro j
  rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ j)

/-- The Euclidean length used by `holderRatioSet` is at most `√d` times the sup distance. -/
theorem aux_lem_boundary_eucl_le {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
  have h : ∑ j : Fin d, (x j - y j) ^ 2 ≤ d * dist x y ^ 2 := by
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, dist x y ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          have h1 : |x j - y j| ≤ dist x y := by
            rw [← Real.dist_eq]; exact dist_le_pi_dist x y j
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = d * dist x y ^ 2 := by simp
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt (d * dist x y ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt d * dist x y := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq dist_nonneg]

/-- A `C^α` norm bound gives the sup bound and the Hölder quotient bound. -/
theorem aux_lem_boundary_holder_bounds {d : ℕ} (alpha : ℝ) (S : Set (SpatialCoordinates d))
    (hS : IsCompact S) (f : SpatialCoordinates d → ℝ) (hf : ContinuousOn f S)
    (hhol : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S f) (K : ℝ) (hK : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S f ≤ K) :
    (∀ x ∈ S, |f x| ≤ K) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        |f x - f y| ≤ K * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha) := by
  have hbdd : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|} := by
    obtain ⟨M, hM⟩ :=
      (hS.image_of_continuousOn (continuous_abs.comp_continuousOn hf)).bddAbove
    refine ⟨M, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact hM ⟨x, hx, rfl⟩
  have hsup0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} :=
    Real.sSup_nonneg (by rintro v ⟨x, -, rfl⟩; exact abs_nonneg _)
  have hsem0 : 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f :=
    Real.sSup_nonneg (by
      rintro v ⟨x, -, y, -, -, rfl⟩
      exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  have hK' : sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f ≤ K := hK
  have hK0 : 0 ≤ K := by linarith
  constructor
  · intro x hx
    have := le_csSup hbdd ⟨x, hx, rfl⟩
    linarith
  · intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      rw [sub_self, abs_zero]
      exact mul_nonneg hK0 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    · have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
        lt_of_lt_of_le (dist_pos.mpr hxy) (aux_lem_boundary_dist_le_eucl x y)
      have hmem : |f x - f y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha ∈
          _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha S f := ⟨x, hx, y, hy, hxy, rfl⟩
      have hle : |f x - f y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha ≤
          _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f := le_csSup hhol hmem
      have h2 : |f x - f y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha ≤ K := by
        linarith
      rwa [div_le_iff₀ (Real.rpow_pos_of_pos hpos alpha)] at h2

/-- Arzelà–Ascoli on a compact set for a uniformly bounded, uniformly Hölder sequence. -/
theorem aux_lem_boundary_subseq_uniform {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (u : ℕ → SpatialCoordinates d → ℝ) (hcont : ∀ N, ContinuousOn (u N) K)
    (B : ℝ) (hB : ∀ N, ∀ x ∈ K, |u N x| ≤ B)
    (alpha : ℝ) (halpha : 0 < alpha) (C : ℝ)
    (hC : ∀ N, ∀ x ∈ K, ∀ y ∈ K, |u N x - u N y| ≤ C * dist x y ^ alpha) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g K ∧
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x ∈ K, |u (τ k) x - g x| < eps) := by
  classical
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let f : ℕ → BoundedContinuousFunction ↥K ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (ContinuousMap.mk (K.domRestrict (u n)) (ContinuousOn.domRestrict (hcont n)))
  let A : Set (BoundedContinuousFunction ↥K ℝ) := Set.range f
  have hA : ∀ (g : BoundedContinuousFunction ↥K ℝ) (x : ↥K), g ∈ A → g x ∈ Set.Icc (-B) B := by
    rintro g x ⟨n, rfl⟩
    change u n ↑x ∈ Set.Icc (-B) B
    exact abs_le.mp (hB n ↑x x.property)
  have heq : Equicontinuous ((↑) : A → ↥K → ℝ) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C * t ^ alpha) ?_ _ ?_
    · have h0 : Tendsto (fun t : ℝ => t ^ alpha) (𝓝 0) (𝓝 0) := by
        have ht := (Real.continuousAt_rpow_const 0 alpha (Or.inr halpha.le)).tendsto
        rwa [Real.zero_rpow halpha.ne'] at ht
      simpa using h0.const_mul C
    · intro x y i
      obtain ⟨n, hn⟩ := i.property
      have hb : |u n ↑x - u n ↑y| ≤ C * dist x y ^ alpha := hC n ↑x x.property ↑y y.property
      rw [← hn]
      change dist (u n ↑x) (u n ↑y) ≤ C * dist x y ^ alpha
      exact le_trans (le_of_eq (Real.dist_eq _ _)) hb
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc A hA heq
  obtain ⟨a, -, τ, hτ, htend⟩ :=
    hcomp.tendsto_subseq (x := fun k => f k) (fun k => subset_closure ⟨k, rfl⟩)
  let g : SpatialCoordinates d → ℝ := fun x => if hx : x ∈ K then a ⟨x, hx⟩ else 0
  refine ⟨τ, hτ, g, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hgr : K.domRestrict g = ⇑a := by
      funext x
      change (if hx : (x : SpatialCoordinates d) ∈ K then a ⟨x, hx⟩ else 0) = a x
      exact dite_eq_left x.property
    rw [hgr]; exact a.continuous
  · intro eps heps
    obtain ⟨k0, hk0⟩ := Metric.tendsto_atTop.mp htend eps heps
    refine ⟨k0, fun k hk x hx => ?_⟩
    have hdist : dist (f (τ k)) a < eps := hk0 k hk
    have hpt : dist ((f (τ k)) ⟨x, hx⟩) (a ⟨x, hx⟩) ≤ dist (f (τ k)) a :=
      (BoundedContinuousFunction.dist_le (f := f (τ k)) (g := a)
        (C := dist (f (τ k)) a) dist_nonneg).mp le_rfl ⟨x, hx⟩
    have hlt : dist ((f (τ k)) ⟨x, hx⟩) (a ⟨x, hx⟩) < eps := lt_of_le_of_lt hpt hdist
    have hfx : (f (τ k)) ⟨x, hx⟩ = u (τ k) x := rfl
    have hgx : g x = a ⟨x, hx⟩ := by
      change (if h : x ∈ K then a ⟨x, h⟩ else 0) = a ⟨x, hx⟩
      exact dite_eq_left hx
    rw [Real.dist_eq, hfx, ← hgx] at hlt
    exact hlt

/-- **.**  If `G_n → G` in `L²` and the `G_n` have representatives with a uniform
`C^α` bound on the closed cube, vanishing on its boundary, then `G` has a continuous `C^α`
representative on the closed cube vanishing on the boundary (Arzelà–Ascoli plus uniqueness of the
`L²` limit). -/
theorem aux_lem_boundary_holder_limit_rep {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (alpha : ℝ) (halpha : 0 < alpha)
    (Gn : ℕ → DomainL2 (centeredCube z r hr)) (G : DomainL2 (centeredCube z r hr))
    (hGn : Tendsto Gn atTop (𝓝 G))
    (rep : ℕ → SpatialCoordinates d → ℝ)
    (hrep : ∀ n, (Gn n : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] rep n)
    (hcont : ∀ n, ContinuousOn (rep n)
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hzero : ∀ n, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      rep n x = 0)
    (hhol : ∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (rep n))
    (K : ℝ) (hK : ∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (rep n) ≤ K) :
    ∃ uRep : SpatialCoordinates d → ℝ,
      ContinuousOn uRep (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      ((G : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uRep) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), uRep x = 0) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) uRep := by
  set Qs : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    with hQs
  have hcpt : IsCompact (closure Qs) := by
    have hball : Qs = Metric.ball z (r / 2) := rfl
    rw [hball]
    exact (isCompact_closedBall z (r / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hb := fun n => aux_lem_boundary_holder_bounds alpha (closure Qs) hcpt (rep n) (hcont n)
    (hhol n) K (hK n)
  have hzQ : z ∈ closure Qs := subset_closure (Metric.mem_ball_self (by positivity))
  have hK0 : 0 ≤ K := (abs_nonneg _).trans ((hb 0).1 z hzQ)
  set C' : ℝ := K * Real.sqrt d ^ alpha with hC'
  have hC : ∀ n, ∀ x ∈ closure Qs, ∀ y ∈ closure Qs,
      |rep n x - rep n y| ≤ C' * dist x y ^ alpha := by
    intro n x hx y hy
    have h1 := (hb n).2 x hx y hy
    have h2 := aux_lem_boundary_eucl_le x y
    calc |rep n x - rep n y| ≤ K * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha := h1
      _ ≤ K * (Real.sqrt d * dist x y) ^ alpha :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Real.sqrt_nonneg _) h2 halpha.le) hK0
      _ = C' * dist x y ^ alpha := by
          rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg, hC']; ring
  obtain ⟨τ, hτ, φ, hφc, hunif⟩ := aux_lem_boundary_subseq_uniform (closure Qs) hcpt rep hcont
    K (fun n => (hb n).1) alpha halpha C' hC
  have hpt : ∀ x ∈ closure Qs, Tendsto (fun k => rep (τ k) x) atTop (𝓝 (φ x)) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨k0, hk0⟩ := hunif eps heps
    exact ⟨k0, fun k hk => by rw [Real.dist_eq]; exact hk0 k hk x hx⟩
  have hφhol : ∀ x ∈ closure Qs, ∀ y ∈ closure Qs,
      |φ x - φ y| ≤ K * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha := by
    intro x hx y hy
    have ht : Tendsto (fun k => |rep (τ k) x - rep (τ k) y|) atTop (𝓝 (|φ x - φ y|)) :=
      ((hpt x hx).sub (hpt y hy)).abs
    exact le_of_tendsto' ht (fun k => (hb (τ k)).2 x hx y hy)
  have hφbd : ∀ x ∈ closure Qs, |φ x| ≤ K := fun x hx =>
    le_of_tendsto' (hpt x hx).abs (fun k => (hb (τ k)).1 x hx)
  refine ⟨φ, hφc, ?_, ?_, ?_⟩
  · have hmeas : MeasurableSet Qs := (centeredCube z r hr).isOpen.measurableSet
    have hmem : MemLp φ 2 (volume.restrict Qs) := by
      refine MemLp.of_bound ((hφc.mono subset_closure).aestronglyMeasurable hmeas) K ?_
      filter_upwards [ae_restrict_mem hmeas] with x hx
      rw [Real.norm_eq_abs]
      exact hφbd x (subset_closure hx)
    set Φ : DomainL2 (centeredCube z r hr) := hmem.toLp φ with hΦdef
    have hΦ : (Φ : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Qs] φ := hmem.coeFn_toLp
    have hlim : Tendsto (fun k => Gn (τ k)) atTop (𝓝 Φ) := by
      rw [Metric.tendsto_atTop]
      intro eps heps
      set m : ℝ := (measureUnivNNReal (volume.restrict Qs) : ℝ) with hm
      have hm0 : 0 ≤ m := NNReal.coe_nonneg _
      obtain ⟨k0, hk0⟩ := hunif (eps / (2 * (m + 1))) (by positivity)
      refine ⟨k0, fun k hk => ?_⟩
      have hL2 := aux_lem_boundary_L2_le_of_uniform z r hr (Gn (τ k)) Φ (rep (τ k)) φ
        (hrep (τ k)) hΦ (eps / (2 * (m + 1))) (by positivity)
        (fun x hx => (hk0 k hk x (subset_closure hx)).le)
      rw [dist_eq_norm]
      calc ‖Gn (τ k) - Φ‖ ≤ (m + 1) * (eps / (2 * (m + 1))) := hL2
        _ = eps / 2 := by field_simp
        _ < eps := by linarith
    have hGΦ : G = Φ := tendsto_nhds_unique (hGn.comp hτ.tendsto_atTop) hlim
    rw [hGΦ]
    exact hΦ
  · intro x hx
    have ht := hpt x (frontier_subset_closure hx)
    have h0 : (fun k => rep (τ k) x) = fun _ => (0 : ℝ) := by
      funext k; exact hzero (τ k) x hx
    rw [h0] at ht
    exact (tendsto_nhds_unique tendsto_const_nhds ht).symm
  · refine ⟨K, ?_⟩
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      lt_of_lt_of_le (dist_pos.mpr hxy) (aux_lem_boundary_dist_le_eucl x y)
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos alpha)]
    exact hφhol x hx y hy

/-- ** on the represented package.**  Almost surely, for every catalogue cube and
catalogue source, `u = G_E g` has a continuous representative on the closed cube which vanishes on
its boundary and is `C^α` there: the clause-K Hölder bounds of the represented source solutions are
bounded along the sequence (clause B, objectwise boundedness), clause F identifies them with
`G_N^E g`, and `G_N^E → G_E` in norm. -/
theorem aux_lem_boundary_source_representative
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
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (G : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hid : ∀ᵐ omega ∂P, ∀ i n f,
      GN i n omega f =
        (responseSolution (S i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n omega) (cutoff n) (z i) (hr i))
          ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1)
    (hconv : ∀ᵐ omega ∂P, ∀ i, Tendsto (fun n => GN i n omega) atTop (𝓝 (G i omega))) :
    ∀ᵐ omega ∂P, ∀ i : ℕ, ∀ g : Dcat i, ∃ uRep : SpatialCoordinates d → ℝ,
      ContinuousOn uRep
        (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
      ((G i omega (g : DomainL2 (centeredCube (z i) (r i) (hr i))) :
          SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
          uRep) ∧
      (∀ x ∈ frontier (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
        uRep x = 0) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) uRep := by
  obtain ⟨-, ⟨-, heta, h2a⟩, -, -, -, -, -, -, -, hseq, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hF, -, -, -, -, hK, -⟩ := h
  obtain ⟨-, -, hGnull, -, hbdd⟩ := hseq
  have halpha0 : 0 < alpha := by linarith
  have hGae : ∀ᵐ omega ∂P, omega ∈ event := mem_ae_iff.mpr hGnull
  filter_upwards [hGae, hid, hconv] with omega homega h2 h3
  intro i g
  obtain ⟨M, hM⟩ := hbdd (sourceHolderKey i g) omega homega
  have hS0 : 0 ≤ sSup {v : ℝ |
      ∃ x ∈ closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
        v = |fcat i g x|} :=
    Real.sSup_nonneg (by rintro v ⟨x, -, rfl⟩; exact abs_nonneg _)
  have htend : Tendsto (fun n => GN i n omega (g : DomainL2 (centeredCube (z i) (r i) (hr i))))
      atTop (𝓝 (G i omega (g : DomainL2 (centeredCube (z i) (r i) (hr i))))) :=
    ((continuous_id.clm_apply continuous_const).tendsto _).comp (h3 i)
  refine aux_lem_boundary_holder_limit_rep (z i) (r i) (hr i) alpha halpha0
    (fun n => GN i n omega (g : DomainL2 (centeredCube (z i) (r i) (hr i))))
    (G i omega (g : DomainL2 (centeredCube (z i) (r i) (hr i)))) htend
    (fun n => srcRep i g n omega) (fun n => ?_) (fun n => (hK i g n omega homega).2.1)
    (fun n => (hK i g n omega homega).2.2.1) (fun n => (hK i g n omega homega).2.2.2.1)
    (M * sSup {v : ℝ |
      ∃ x ∈ closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
        v = |fcat i g x|}) (fun n => ?_)
  · have hFg := (hF i n omega homega).1 g
    have hGNg := h2 i n (g : DomainL2 (centeredCube (z i) (r i) (hr i)))
    show (GN i n omega (g : DomainL2 (centeredCube (z i) (r i) (hr i))) :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
        srcRep i g n omega
    rw [hGNg, ← hFg.1]
    exact hFg.2.1
  · exact (hK i g n omega homega).2.2.2.2.trans
      (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hM n)) hS0)

/-- **Glued competitors (the remaining proof obligation).**
Given the continuous `C^α` representative `uRep` of `u = G_E g` (zero on `∂Q`, supplied by
`aux_lem_boundary_source_representative`), extend it by zero to an enclosing absolute-grid root,
run the stopping construction on its descendants (good padded cells of `S`-levels whose
enlargement lies in `Q`: `lem_goodext`; mass comparison `λ(p) ≤ L^D λ(q)`), bound cells meeting
`∂Q` by the crude `K r^{s0}` cost (`O(r^{-(d-1)})` of them by `boundary_cell_count`, `s0 > d-1`),
count unstopped branches (`prop_allchain`, padding count), sum the stopped costs
(`prop_density_core_comparison`) and glue (`lem_skeleton`) into `v J ∈ D(F)` converging uniformly to
`uRep` with `F(v J) ≤ C_* a (E(u) + cFloor |Q|) + eps` eventually. -/
theorem aux_lem_boundary_catalogue_approximation
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Ddet : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
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
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega)))) →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr Sspace GE GF NE NF →
      ∀ (root : ℕ)
      (Dcat : ∀ i, Submodule ℚ
        (DomainL2 (centeredCube (z i) (r i) (hr i))))
      (hDcat : ∀ i, Countable (Dcat i))
      (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
      (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
      (traceH1 : ∀ i, ℕ → Homogenization.H1Function
        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
      (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
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
        ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
        usrcE srcRepE ucellE Cext beta alpha eta t {1} I
        ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
        (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
        coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey
        cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey →
      conv_represented_estimates d hd model H Ω P NF envF
        ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
        usrcF srcRepF ucellF Cext beta alpha eta t {1} I
        ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
        (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
        coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey
        cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey →
      ∀ (eE eF : ℕ → ℝ), (∀ k, 0 < eE k ∧ 0 < eF k) →
      let kappa : ℕ → ℝ := fun N =>
        Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
      (∀ k, Tendsto (fun j => kappa (NE j - k) / kappa (NE j)) atTop (nhds (eE k))) →
      (∀ k, Tendsto (fun j => kappa (NF j - k) / kappa (NF j)) atTop (nhds (eF k))) →
      ∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ upperDensity Sset →
        (∀ n, Sset n → eF (H1 * n) / eE (H1 * n) ≤ a) →
        ∀ᵐ omega ∂P, ∀ i : ℕ, ∀ g : Dcat i, ∀ cFloor : ℝ, 0 < cFloor →
          ∃ uRep : SpatialCoordinates d → ℝ,
            ∃ v : ℕ → DomainL2 (centeredCube (z i) (r i) (hr i)),
            ∃ vRep : ℕ → SpatialCoordinates d → ℝ,
              ContinuousOn uRep
                (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
              ((GE i omega (g : DomainL2 (centeredCube (z i) (r i) (hr i))) :
                  SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict
                    (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
                uRep) ∧
              (∀ J, v J ∈ limitFormDomain (GF i omega)) ∧
              (∀ J, ContinuousOn (vRep J)
                (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))) ∧
              (∀ J, (v J : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict
                    (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
                (vRep J)) ∧
              (∀ eps : ℝ, 0 < eps →
                ∃ J0 : ℕ, ∀ J ≥ J0,
                  (∀ x ∈ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
                    |vRep J x - uRep x| ≤ eps) ∧
                  (limitFormEnergy (GF i omega) (v J)).toReal ≤
                    Cstar * a *
                      ((limitFormEnergy (GE i omega)
                          (GE i omega (g : DomainL2 (centeredCube (z i) (r i) (hr i))))).toReal +
                        cFloor *
                          (volume (centeredCube (z i) (r i) (hr i) :
                            Set (SpatialCoordinates d))).toReal) + eps) := by
  intro L hLlarge hCdPad
  obtain ⟨delta0, Cstar, hdelta0, hCstar, hG⟩ :=
    _root_.SubdiffusiveProcess.Paper.prop_density_core_approximation d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp eta0 heta0 heta03 D theta alpha eta hD
      htheta htheta8 halpha halpha1 heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge
  refine ⟨delta0, Cstar, hdelta0, hCstar, ?_⟩
  intro _ _ model hmodel Rm Sreg It H Ω _ P _ field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr Sspace GNE GNF GE GF NE NF hpkg hBoundsI
    root Dcat hDcat fcat trace traceH1 usrcE usrcF srcRepE srcRepF ucellE ucellF
    Cext I coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey hEstE hEstF
    eE eF hpos kappa hE hF Sset a ha hdens hratio
  have hSmooth : ∀ i : ℕ, ∀ g : Dcat i,
      ∃ fSmooth : SpatialCoordinates d → ℝ,
        ContDiff ℝ ∞ fSmooth ∧ HasCompactSupport fSmooth ∧
        tsupport fSmooth ⊆
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ∧
        ((g : DomainL2 (centeredCube (z i) (r i) (hr i))) :
            SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict
                (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
          fSmooth := by
    have hS := hEstE.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    intro i g
    exact ⟨fcat i g, hS i g⟩
  obtain ⟨hP, hfield, hlaw, hIR, hNE, hNF, hmp, henv, hSsp, hid, hconv⟩ := hpkg
  let : ∀ i, Countable (Dcat i) := hDcat
  have hGg := hG model hmodel Rm Sreg It H Ω P field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr Sspace GNE GNF GE GF NE NF
    ⟨hP, hfield, hlaw, hIR, hNE, hNF, hmp, henv, hSsp, hid, hconv,
      ⟨root, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
        ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
        sourceResponseKey, sourceGrowthKey, sourceHolderKey,
        cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey,
        hEstE, hEstF⟩⟩ hBoundsI
    eE eF hpos hE hF Sset a ha hdens hratio
  filter_upwards [hGg] with omega hG1
  intro i g cFloor hc
  obtain ⟨fSmooth, hf1, hf2, hf3, hf4⟩ := hSmooth i g
  obtain ⟨uRep, v, vRep, hu1, hu2, hv1, hv2, hv3, hv4⟩ :=
    hG1 i (g : DomainL2 (centeredCube (z i) (r i) (hr i)))
      ⟨fSmooth, hf1, hf2, hf3, hf4⟩ cFloor hc
  exact ⟨uRep, v, vRep, hu1, hu2, hv1, hv2, hv3, hv4⟩



theorem lem_boundary
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Ddet : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
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
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1) ∧
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
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
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
            ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)) →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr Sspace GE GF NE NF →
      ∀ (eE eF : ℕ → ℝ), (∀ k, 0 < eE k ∧ 0 < eF k) →
      let kappa : ℕ → ℝ := fun N =>
        Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
      (∀ k, Tendsto (fun j => kappa (NE j - k) / kappa (NE j)) atTop (nhds (eE k))) →
      (∀ k, Tendsto (fun j => kappa (NF j - k) / kappa (NF j)) atTop (nhds (eF k))) →
      ∀ (unit : ℕ) (_hunitz : z unit = 0) (_hunitr : r unit = 1),
      ∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ upperDensity Sset →
        (∀ n, Sset n → eF (H1 * n) / eE (H1 * n) ≤ a) →
        ∀ᵐ omega ∂P, ∀ i : ℕ,
          limitFormDomain (GE i omega) ⊆ limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            (limitFormEnergy (GF i omega) u).toReal ≤
              Cstar * a * (limitFormEnergy (GE i omega) u).toReal := by
  intro L hLlarge hCdPad
  obtain ⟨delta0, Cstar, hdelta0, hCstar, hmain⟩ :=
    aux_lem_boundary_catalogue_approximation d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp eta0 heta0 heta03 D theta alpha eta hD
      htheta htheta8 halpha halpha1 heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  refine ⟨delta0, Cstar, hdelta0, hCstar, ?_⟩
  intro _ _ model hmodel Rm Sreg It H Ω _ P _ field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr Sspace GNE GNF GE GF NE NF hjoint hBoundsP
    eE eF hpos kappa hE hF _unit _hunitz _hunitr Sset a ha hdens hratio
  obtain ⟨hP, hfield, hlaw, hIR, hNE, hNF, hmp, henv, hSsp, hid, hconv, hcat⟩ := hjoint
  obtain ⟨root, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey,
    hEstE, hEstF⟩ := hcat
  have hA := hmain model hmodel Rm Sreg It H Ω P field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr Sspace GNE GNF GE GF NE NF
    ⟨hP, hfield, hlaw, hIR, hNE, hNF, hmp, henv, hSsp, hid, hconv⟩ hBoundsP
    root Dcat hDcat fcat trace traceH1 usrcE usrcF srcRepE srcRepF ucellE ucellF
    Cext I coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey hEstE hEstF
    eE eF hpos hE hF Sset a ha hdens hratio
  have hdense := aux_lem_boundary_catalogue_dense d hd model H Ω P NE envE root z r hr
    Sspace Dcat (hDcat := hDcat) fcat trace traceH1 usrcE srcRepE ucellE Cext beta alpha eta t I
    (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
    (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey hEstE
  filter_upwards [hA, hid, hconv] with omega h1 h2 h3
  intro i
  obtain ⟨hsym, hpos'⟩ := aux_lem_boundary_limit_sym_pos (Sspace i)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
    (fun n => GNE i n omega) (GE i omega) (fun n f => (h2 i n f).1) (h3 i).1
  have happrox : ∀ f ∈ (Dcat i : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))),
      ∀ c : ℝ, 0 < c → ∀ eps : ℝ, 0 < eps →
      ∃ w : DomainL2 (centeredCube (z i) (r i) (hr i)),
        ‖w - GE i omega f‖ ≤ eps ∧
          limitFormEnergy (GF i omega) w ≤
            ((Cstar * a * ((limitFormEnergy (GE i omega) (GE i omega f)).toReal +
              c * (volume (centeredCube (z i) (r i) (hr i) :
                Set (SpatialCoordinates d))).toReal) + eps : ℝ) : EReal) := by
    intro f hf
    exact aux_lem_boundary_approx_of_core (z i) (r i) (hr i) (GE i omega) (GF i omega)
      (Cstar * a) f (fun cFloor hc => h1 i ⟨f, hf⟩ cFloor hc)
  have key := aux_lem_boundary_closure (GE i omega) (GF i omega) hsym hpos' _ (hdense i)
    (Cstar * a) _ (by positivity) ENNReal.toReal_nonneg happrox
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · show limitFormEnergy (GF i omega) u < ⊤
    exact lt_of_le_of_lt (key u hu) (EReal.coe_lt_top _)
  · have hbot : limitFormEnergy (GF i omega) u ≠ ⊥ :=
      (EReal.bot_lt_zero.trans_le (limitFormEnergy_nonneg _ u)).ne'
    have hle := EReal.toReal_le_toReal (key u hu) hbot (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at hle


end
end SubdiffusiveProcess.Paper

