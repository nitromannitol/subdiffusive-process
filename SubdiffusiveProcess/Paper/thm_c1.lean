module

public import SubdiffusiveProcess.Variational.DualEnergy
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.cor_37
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.thm_prop_global
public import SubdiffusiveProcess.Paper.thm_c1_cube_positive_energy
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.in_moments
public import SubdiffusiveProcess.Paper.thm_c1_scalar
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.in_represented_bounds
public import SubdiffusiveProcess.Paper.in_represented_enum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.Paper

/-- A sequence of bounded represented catalogues, each containing the first
`k + 1` cubes of the global family. The same global response spaces and cutoff
subsequences are used on every restriction. -/
def aux_thm_c1_catalogues (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta beta t : ℝ) : Prop :=
  ∀ k : ℕ, ∃ e : ℕ → ℕ,
    (∀ i ≤ k, ∃ j, e j = i) ∧
    aux_thm_prop_catalogue d hd model H Ω P field
      (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j))
      NE NF alpha eta beta t

/-- The actual geometry clauses of a bounded catalogue supply its enumeration. -/
theorem aux_thm_c1_catalogue_enum (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t) :
    in_represented_enum d z r hr := by
  obtain ⟨resp, constants, respE, respF, eventE, eventF, root, hunit,
    Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey,
    cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hE, hF⟩ := hCat
  have hgeom := hE.2.2.2.2.2.2.2.2.2.2
  exact ⟨z root, r root, hr root, hgeom.2.1 root, hgeom.2.2.1 root,
    hgeom.2.2.2.1⟩

/-- Joint operator extraction is preserved on every subcatalogue. -/
theorem aux_thm_c1_joint_reindex (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (e : ℕ → ℕ) :
    in_joint_extracted_candidates d model H Ω P field
      (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j))
      (fun j => GN (e j)) (fun j => GE (e j)) (fun j => GF (e j)) NE NF := by
  obtain ⟨hP, hfield, hmap, hH, hmono, hS, hGN, hconv⟩ := hJoint
  exact ⟨hP, hfield, hmap, hH, hmono, fun j => hS (e j),
    fun j => hGN (e j), hconv.mono fun omega h j => h (e j)⟩

/-- Constants on exhaustive subcatalogues agree on their common first cube,
and the almost-sure proportionalities therefore glue on the whole family. -/
theorem aux_thm_c1_glue_proportionality {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (e : ℕ → ℕ → ℕ) (hcover : ∀ k i, i ≤ k → ∃ j, e k j = i)
    (hpos : ∀ᵐ omega ∂P, ∃ u : DomainL2 (centeredCube (z 0) (r 0) (hr 0)),
      u ∈ limitFormDomain (GE 0 omega) ∧ 0 < (limitFormEnergy (GE 0 omega) u).toReal)
    (hlocal : ∀ k, ∃ c : ℝ, 0 < c ∧ ∀ᵐ omega ∂P, ∀ j,
      limitFormDomain (GE (e k j) omega) = limitFormDomain (GF (e k j) omega) ∧
      ∀ u, u ∈ limitFormDomain (GE (e k j) omega) →
        (limitFormEnergy (GF (e k j) omega) u).toReal =
          c * (limitFormEnergy (GE (e k j) omega) u).toReal) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ omega ∂P, ∀ i,
      limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
      ∀ u, u ∈ limitFormDomain (GE i omega) →
        (limitFormEnergy (GF i omega) u).toReal =
          c * (limitFormEnergy (GE i omega) u).toReal := by
  choose c hc hprop using hlocal
  have heq : ∀ k, c k = c 0 := by
    intro k
    obtain ⟨j, hj⟩ := hcover k 0 (Nat.zero_le k)
    obtain ⟨j0, hj0⟩ := hcover 0 0 le_rfl
    obtain ⟨omega, hp, hp0, u, hu, hupos⟩ :=
      ((hprop k).and ((hprop 0).and hpos)).exists
    have hk := hp j
    have h0 := hp0 j0
    rw [hj] at hk
    rw [hj0] at h0
    exact (mul_right_cancel₀ (ne_of_gt hupos)) ((hk.2 u hu).symm.trans (h0.2 u hu))
  refine ⟨c 0, hc 0, ?_⟩
  filter_upwards [ae_all_iff.mpr hprop] with omega h i
  obtain ⟨j, hj⟩ := hcover i i le_rfl
  have hi := h i j
  rwa [hj, heq i] at hi


/-! ### Helpers for `thm_c1`

Measurability of the actual finite-cutoff response in the field (the side-`1`
argument of `lem_as_coarse_shallow_grid_affine_dirichlet_measurable`, run on
the triadic cube of side `3^k` with an arbitrary Poincare certificate), the
transfer of the calibration integral of `cor_37` from the common-scale law to
`P`, Fatou's lemma along a candidate subsequence, the scalar scaling of the
boundary minima, and the final energy identification. -/

/-- The global zero-infrared log-potential of the normalized cutoff coefficient. -/
noncomputable def aux_thm_c1_logPotential {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
    ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
    ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i))

theorem aux_thm_c1_logPotential_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    Measurable (aux_thm_c1_logPotential M N) :=
  measurable_const.add
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i)))

theorem aux_thm_c1_rootLog_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ) (om : BilateralField d) :
    continuousPositiveLog
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) =
      (aux_thm_c1_logPotential M N om).restrict
        (closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d)) := by
  ext x
  have hh : Real.log (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x) =
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)) x := by
    rw [cutoffCoefficient, Real.log_mul
      (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
      (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
    simp only [cutoffPotential, ContinuousMap.zero_apply]
    ring
  have hv : ((aux_thm_c1_logPotential M N om).restrict
      (closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))) x =
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)) x := by
    rw [ContinuousMap.restrict_apply]
    simp only [aux_thm_c1_logPotential, ContinuousMap.add_apply,
      ContinuousMap.const_apply, ContinuousMap.sum_apply]
  simpa only [continuousPositiveLog, _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM,
    ContinuousMap.coe_mk] using! hh.trans hv.symm

/-- The cutoff coefficient on `Q_{3^k}` as an exponential of a compact potential. -/
noncomputable def aux_thm_c1_expCoeff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ) (om : BilateralField d) :
    PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) := by
  let Om := centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  let K := closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)⟩
  exact expPotentialCoefficient (compactPotentialToLp K
    ((aux_thm_c1_logPotential M N om).restrict (K : Set (SpatialCoordinates d))))

theorem aux_thm_c1_coeff_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ) (om : BilateralField d) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) =
    aux_thm_c1_expCoeff M N k om := by
  let Om := centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  let K := closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  have : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)⟩
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
    aux_thm_c1_expCoeff
  rw [aux_thm_c1_rootLog_eq]
  simp only [Real.log_one, ContinuousMap.const_zero, sub_zero]

/-- The actual zero-infrared cutoff response on `Q_{3^k}` is measurable in the field. -/
theorem aux_thm_c1_response_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
          ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))) w‖)
    (p : Fin d → ℝ) :
    Measurable (fun om : BilateralField d => affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p) := by
  let Om := centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  let K := closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  have : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)⟩
  have hD := ((continuous_dirichletResponse_compact (killedResponseSpace hP) K
      (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p 0)).comp
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d)))).measurable.comp
      (aux_thm_c1_logPotential_measurable M N)
  convert hD using 1
  funext om
  rw [aux_thm_c1_coeff_eq M N k om]
  rfl

/-- Transfer of the calibration integral from the common-scale law to `P`. -/
theorem aux_thm_c1_transfer {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (hfield : Measurable field)
    (hmap : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (k N : ℕ)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
          ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))) w‖)
    (p : Fin d → ℝ) (L : Ω → ℝ) (v : ℝ)
    (hL : ∀ᵐ ω ∂P, L ω = affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (field ω) N 0 (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p)
    (hv : v = (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal) :
    ∫ ω, |L ω / v - ∑ i : Fin d, p i ^ 2| ∂P =
      ∫ om, |affineDirichletResponse
          (centeredCube_isBounded (0 : SpatialCoordinates d)
            (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) hP
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
            om N 0 (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p /
          (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
            (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal -
          ∑ i : Fin d, p i ^ 2| ∂(chaosSampleLaw model).toMeasure := by
  subst hv
  have hg := continuous_abs.measurable.comp
    (((aux_thm_c1_response_measurable model N k hP p).div_const
      (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal).sub_const
      (∑ i : Fin d, p i ^ 2))
  rw [← hmap]
  symm
  refine (integral_map hfield.aemeasurable hg.aestronglyMeasurable).trans ?_
  refine integral_congr_ae ?_
  filter_upwards [hL] with ω hω
  simp only [Function.comp_apply]
  rw [hω]

/-- Fatou's lemma along a candidate subsequence: the limit inherits the uniform
`L¹` calibration bound and is integrable. -/
theorem aux_thm_c1_fatou {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (G : Ω → ℝ) (s eps : ℝ) (heps : 0 ≤ eps)
    (hint : ∀ n, Integrable (F n) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)))
    (hbound : ∀ n, ∫ ω, |F n ω - s| ∂P ≤ eps) :
    Integrable G P ∧ ∫ ω, |G ω - s| ∂P ≤ eps := by
  have hGm : AEStronglyMeasurable G P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hint n).aestronglyMeasurable) hconv
  have hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal |F n ω - s|) P := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable
        ((hint n).aestronglyMeasurable.aemeasurable.sub_const s))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal |F n ω - s|) atTop
      (𝓝 (ENNReal.ofReal |G ω - s|)) := by
    filter_upwards [hconv] with ω hω
    exact ENNReal.tendsto_ofReal ((hω.sub_const s).abs)
  have hn : ∀ n, ∫⁻ ω, ENNReal.ofReal |F n ω - s| ∂P ≤ ENNReal.ofReal eps := by
    intro n
    have hi : Integrable (fun ω => |F n ω - s|) P :=
      ((hint n).sub (integrable_const s)).abs
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hG : ∫⁻ ω, ENNReal.ofReal |G ω - s| ∂P ≤ ENNReal.ofReal eps := by
    calc ∫⁻ ω, ENNReal.ofReal |G ω - s| ∂P
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal |F n ω - s|) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with ω hω
          exact hω.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal |F n ω - s| ∂P) atTop :=
          lintegral_liminf_le' hmeas
      _ ≤ ENNReal.ofReal eps :=
          liminf_le_of_frequently_le' (Frequently.of_forall hn)
  have hGs : Integrable (fun ω => G ω - s) P := by
    refine ⟨hGm.sub aestronglyMeasurable_const, ?_⟩
    show ∫⁻ ω, ‖G ω - s‖ₑ ∂P < ⊤
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hG ENNReal.ofReal_lt_top
  refine ⟨(hGs.add (integrable_const s)).congr
    (Filter.Eventually.of_forall fun ω => by simp), ?_⟩
  have hGa : Integrable (fun ω => |G ω - s|) P := hGs.abs
  rw [← ofReal_integral_eq_lintegral_ofReal hGa
    (Filter.Eventually.of_forall fun ω => abs_nonneg _)] at hG
  exact (ENNReal.ofReal_le_ofReal_iff heps).1 hG

/-- The deviation of the normalized mean is at most the mean absolute deviation. -/
theorem aux_thm_c1_mean_dev {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (f : Ω → ℝ) (v s : ℝ) (hf : Integrable (fun ω => f ω / v) P) :
    |(∫ ω, f ω ∂P) / v - s| ≤ ∫ ω, |f ω / v - s| ∂P := by
  have h1 : (∫ ω, f ω ∂P) / v - s = ∫ ω, (f ω / v - s) ∂P := by
    rw [integral_sub hf (integrable_const s), integral_div]
    simp
  rw [h1]
  exact abs_integral_le_integral_abs

theorem aux_thm_c1_tendsto_zero (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (h : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → f k ≤ eps) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨k0, hk0⟩ := h (eps / 2) (half_pos heps)
  refine ⟨k0, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf k)]
  linarith [hk0 k hk]

/-- Passage of the finite calibration to a candidate subsequence (Fatou). -/
theorem aux_thm_c1_limit_calibration {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (LN : ℕ → ℕ → Ω → ℝ) (L : ℕ → Ω → ℝ) (vol : ℕ → ℝ) (s : ℝ) (NS : ℕ → ℕ)
    (hint : ∀ k N, Integrable (fun ω => LN k N ω / vol k) P)
    (hconv : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => LN k (NS n) ω) atTop (𝓝 (L k ω)))
    (hcal : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ N,
      ∫ ω, |LN k N ω / vol k - s| ∂P ≤ eps) :
    ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      Integrable (fun ω => L k ω / vol k) P ∧ ∫ ω, |L k ω / vol k - s| ∂P ≤ eps := by
  intro eps heps
  obtain ⟨k0, hk0⟩ := hcal eps heps
  refine ⟨k0, fun k hk => ?_⟩
  exact aux_thm_c1_fatou P (fun n ω => LN k (NS n) ω / vol k) (fun ω => L k ω / vol k)
    s eps heps.le (fun n => hint k (NS n))
    ((hconv k).mono fun ω hω => hω.div_const (vol k))
    (fun n => hk0 k hk (NS n))

/-- The normalized expected candidate responses converge to the calibration value. -/
theorem aux_thm_c1_expect_tendsto {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (L : ℕ → Ω → ℝ) (vol : ℕ → ℝ) (s : ℝ)
    (h : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      Integrable (fun ω => L k ω / vol k) P ∧ ∫ ω, |L k ω / vol k - s| ∂P ≤ eps) :
    Tendsto (fun k => |(∫ ω, L k ω ∂P) / vol k - s|) atTop (𝓝 0) := by
  refine aux_thm_c1_tendsto_zero _ (fun k => abs_nonneg _) fun eps heps => ?_
  obtain ⟨k0, hk0⟩ := h eps heps
  exact ⟨k0, fun k hk =>
    (aux_thm_c1_mean_dev P (L k) (vol k) s (hk0 k hk).1).trans (hk0 k hk).2⟩

open scoped Pointwise in
/-- Scalar response scaling : if the candidate limit energies are
proportional with constant `c`, then so are the boundary minima of the
infrared-removed forms on every inner set. -/
theorem aux_thm_c1_sInf_scale {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E F E0 F0 : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GamE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (GamF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F)
    (GamE0 : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E0) (GamF0 : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F0)
    (rho : SpatialCoordinates d → ℝ)
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hwE : _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm E E0 GamE rho)
    (hwF : _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm F F0 GamF rho)
    (hE : ∀ u, E.energy u = limitFormEnergy GE u)
    (hF : ∀ u, F.energy u = limitFormEnergy GF u)
    (c : ℝ) (hc : 0 < c)
    (hprop : limitFormDomain GE = limitFormDomain GF ∧
      ∀ u : DomainL2 Q, u ∈ limitFormDomain GE →
        (limitFormEnergy GF u).toReal = c * (limitFormEnergy GE u).toReal)
    (hGS : F.domain = E.domain → (∀ u ∈ E.domain, F.form u u = c * E.form u u) →
      ∀ u ∈ E.domain, GamF.measure u = ENNReal.ofReal c • GamE.measure u)
    (hG0S : F0.domain = E0.domain → (∀ u ∈ E0.domain, F0.form u u = c * E0.form u u) →
      ∀ u ∈ E0.domain, GamF0.measure u = ENNReal.ofReal c • GamE0.measure u)
    (A : (SpatialCoordinates d → ℝ) → Prop)
    (B : DomainL2 Q → (SpatialCoordinates d → ℝ) → Prop)
    (C : (SpatialCoordinates d → ℝ) → Prop) (S : Set (SpatialCoordinates d)) :
    sInf {e : ℝ | ∃ U : DomainL2 Q, U ∈ F0.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamF0.measure U) S).toReal} =
      c * sInf {e : ℝ | ∃ U : DomainL2 Q, U ∈ E0.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamE0.measure U) S).toReal} := by
  have hdomE : (E.domain : Set (DomainL2 Q)) = limitFormDomain GE := by
    ext u
    change u ∈ E.domain ↔ limitFormEnergy GE u < ⊤
    rw [← hE u, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_lt_top_iff]
  have hdomF : (F.domain : Set (DomainL2 Q)) = limitFormDomain GF := by
    ext u
    change u ∈ F.domain ↔ limitFormEnergy GF u < ⊤
    rw [← hF u, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_lt_top_iff]
  have hFE : F.domain = E.domain :=
    SetLike.coe_injective (hdomF.trans (hprop.1.symm.trans hdomE.symm))
  have hform : ∀ u ∈ E.domain, F.form u u = c * E.form u u := by
    intro u hu
    have huF : u ∈ F.domain := by rw [hFE]; exact hu
    have huG : u ∈ limitFormDomain GE := by rw [← hdomE]; exact hu
    have h1 : (limitFormEnergy GF u).toReal = F.form u u := by
      rw [← hF u, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem F huF, EReal.toReal_coe]
    have h2 : (limitFormEnergy GE u).toReal = E.form u u := by
      rw [← hE u, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem E hu, EReal.toReal_coe]
    rw [← h1, ← h2]
    exact hprop.2 u huG
  have hGam := hGS hFE hform
  have hF0E0 : F0.domain = E0.domain :=
    hwF.domain_eq.trans (hFE.trans hwE.domain_eq.symm)
  have hform0 : ∀ u ∈ E0.domain, F0.form u u = c * E0.form u u := by
    intro u hu
    have huE : u ∈ E.domain := by rw [← hwE.domain_eq]; exact hu
    have huF : u ∈ F.domain := by rw [hFE]; exact huE
    rw [hwF.energy_eq u huF, hwE.energy_eq u huE, hGam u huE, integral_smul_measure,
      ENNReal.toReal_ofReal hc.le, smul_eq_mul]
  have hGam0 := hG0S hF0E0 hform0
  have hset : {e : ℝ | ∃ U : DomainL2 Q, U ∈ F0.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamF0.measure U) S).toReal} =
      c • {e : ℝ | ∃ U : DomainL2 Q, U ∈ E0.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamE0.measure U) S).toReal} := by
    ext e
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨U, hU, Uc, hA, hB, hC, rfl⟩
      have hU0 : U ∈ E0.domain := by rw [← hF0E0]; exact hU
      refine ⟨((GamE0.measure U) S).toReal, ⟨U, hU0, Uc, hA, hB, hC, rfl⟩, ?_⟩
      rw [hGam0 U hU0]
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hc.le]
    · rintro ⟨x, ⟨U, hU, Uc, hA, hB, hC, rfl⟩, rfl⟩
      have hUF : U ∈ F0.domain := by rw [hF0E0]; exact hU
      refine ⟨U, hUF, Uc, hA, hB, hC, ?_⟩
      rw [hGam0 U hU]
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hc.le]
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

/-- With `c = 1`, the real proportionality on the common domain gives equality of the
extended dual energies everywhere. -/
theorem aux_thm_c1_energy_eq {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q) (c : ℝ) (hc1 : c = 1)
    (hdom : limitFormDomain GE = limitFormDomain GF)
    (hen : ∀ u : DomainL2 Q, u ∈ limitFormDomain GE →
      (limitFormEnergy GF u).toReal = c * (limitFormEnergy GE u).toReal)
    (u : DomainL2 Q) : limitFormEnergy GE u = limitFormEnergy GF u := by
  by_cases hu : u ∈ limitFormDomain GE
  · have huF : u ∈ limitFormDomain GF := by rw [← hdom]; exact hu
    have hE1 : limitFormEnergy GE u < ⊤ := hu
    have hF1 : limitFormEnergy GF u < ⊤ := huF
    have hE2 : limitFormEnergy GE u ≠ ⊥ :=
      ne_bot_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg GE u))
    have hF2 : limitFormEnergy GF u ≠ ⊥ :=
      ne_bot_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg GF u))
    rw [← EReal.coe_toReal hE1.ne hE2, ← EReal.coe_toReal hF1.ne hF2, hen u hu, hc1,
      one_mul]
  · have huF : u ∉ limitFormDomain GF := by rw [← hdom]; exact hu
    have hE1 : ¬ limitFormEnergy GE u < ⊤ := hu
    have hF1 : ¬ limitFormEnergy GF u < ⊤ := huF
    rw [not_lt, top_le_iff] at hE1 hF1
    rw [hE1, hF1]

/-- The joint-extraction convention supplies the probability space and the law of the field. -/
theorem aux_thm_c1_joint (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (h : in_joint_extracted_candidates d M H Ω P field z r hr S GN GE GF NE NF) :
    IsProbabilityMeasure P ∧ Measurable field ∧
      Measure.map field P = (chaosSampleLaw M).toMeasure :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- The actual geometry clauses of a bounded catalogue: its cubes are rational triadic cubes of one
root cube, and every rational triadic cube of the root occurs. -/
theorem aux_thm_c1_catalogue_geometry (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) {beta t : ℝ}
    (hCat : aux_thm_prop_catalogue d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t) :
    ∃ root : ℕ,
      (∀ j : ℕ, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d))) ∧
      (∀ (j : ℕ) (i : Fin d), ∃ q : ℚ, z j i = (q : ℝ)) ∧
      (∀ j : ℕ, ∃ k : ℤ, r j = (3 : ℝ) ^ k) ∧
      (∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
        (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) → (∃ k : ℤ, r' = (3 : ℝ) ^ k) →
        (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)) →
        ∃ j : ℕ, z j = z' ∧ r j = r') := by
  obtain ⟨resp, constants, respE, respF, eventE, eventF, root, hunit,
    Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey,
    cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hE, hF⟩ := hCat
  have hgeom := hE.2.2.2.2.2.2.2.2.2.2
  exact ⟨root, hgeom.1, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.1⟩

/-- A cube is contained in a centred cube of triadic side `3 ^ k` for `k` large. -/
theorem aux_thm_c1_cube_subset_big {d : ℕ} (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r') :
    ∃ k : ℕ, (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k) (pow_pos (by norm_num) k) :
        Set (SpatialCoordinates d)) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * ‖z'‖ + r') (by norm_num : (1 : ℝ) < 3)
  refine ⟨k, ?_⟩
  change Metric.ball z' (r' / 2) ⊆ Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ k / 2)
  refine Metric.ball_subset_ball' ?_
  rw [dist_zero_right]
  linarith [norm_nonneg z']

/-- **The whole family.**  The catalogue blocks together with the cubes `Q(0, 3 ^ k)` exhaust the
rational triadic cubes: every family cube is rational triadic, and every rational triadic cube of
`ℝ^d` occurs in the family. -/
theorem aux_thm_c1_global_family (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta beta t : ℝ)
    (hCat : aux_thm_c1_catalogues d hd model H Ω P field z r hr Sspace NE NF alpha eta beta t)
    (qidx : ℕ → ℕ) (hq : ∀ k, z (qidx k) = 0 ∧ r (qidx k) = (3 : ℝ) ^ k) :
    (∀ i : ℕ, (∀ c : Fin d, ∃ q : ℚ, z i c = (q : ℝ)) ∧ ∃ m : ℤ, r i = (3 : ℝ) ^ m) ∧
    (∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
      (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, z i = z' ∧ r i = r') := by
  choose e hcover hcat using hCat
  constructor
  · intro i
    obtain ⟨j, hj⟩ := hcover i i le_rfl
    obtain ⟨root, -, hrat, htri, -⟩ := aux_thm_c1_catalogue_geometry d hd model H Ω P field
      (z ∘ e i) (r ∘ e i) (fun j => hr (e i j)) (fun j => Sspace (e i j)) NE NF alpha eta
      (hcat i)
    have h1 := hrat j
    have h2 := htri j
    simp only [Function.comp_apply, hj] at h1 h2
    exact ⟨h1, h2⟩
  · intro z' r' hz' hr'
    have hr'pos : 0 < r' := by
      obtain ⟨m, hm⟩ := hr'
      rw [hm]
      exact zpow_pos (by norm_num) m
    obtain ⟨k, hk⟩ := aux_thm_c1_cube_subset_big z' r' hr'pos
    obtain ⟨j, hj⟩ := hcover (qidx k) (qidx k) le_rfl
    obtain ⟨root, hsub, -, -, hcov⟩ := aux_thm_c1_catalogue_geometry d hd model H Ω P field
      (z ∘ e (qidx k)) (r ∘ e (qidx k)) (fun j => hr (e (qidx k) j))
      (fun j => Sspace (e (qidx k) j)) NE NF alpha eta (hcat (qidx k))
    have hQ := hsub j
    simp only [Function.comp_apply, hj] at hQ
    have hz0 := (hq k).1
    have hr0 := (hq k).2
    have hincl : (centeredCube z' r' hr'pos : Set (SpatialCoordinates d)) ⊆
        (centeredCube ((z ∘ e (qidx k)) root) ((r ∘ e (qidx k)) root)
          ((fun j => hr (e (qidx k) j)) root) : Set (SpatialCoordinates d)) := by
      refine hk.trans ?_
      have hcube : (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k) (pow_pos (by norm_num) k) :
          Set (SpatialCoordinates d)) =
          (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) : Set (SpatialCoordinates d)) := by
        simp only [centeredCube, hz0, hr0]
      rw [hcube]
      exact hQ
    obtain ⟨j', hj'⟩ := hcov z' r' hr'pos (fun c => hz' c) hr' hincl
    exact ⟨e (qidx k) j', hj'⟩

/-- `cor_37`, transferred to the probability space of the candidates. -/
theorem aux_thm_c1_cal (d : ℕ) (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d),
        Measurable field → Measure.map field P = (chaosSampleLaw model).toMeasure →
      ∀ (Poincare : ℕ → ℝ≥0)
        (hPoincare : ∀ k (u : killedSobolevGraph
            (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
              (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))),
          ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d)
              ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))).1‖ ≤
            Poincare k * ‖subspaceGradient
              (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
                ((3 : ℝ) ^ k) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))) u‖)
        (L : ℕ → ℕ → Ω → ℝ) (vol : ℕ → ℝ) (p : Fin d → ℝ),
        (∀ k, vol k = (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal) →
        (∀ᵐ omega ∂P, ∀ k N,
          L k N omega =
            affineDirichletResponse
              (centeredCube_isBounded (0 : SpatialCoordinates d)
                (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))
              ⟨Poincare k, hPoincare k⟩
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model
                (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (field omega) N 0
                (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) p) →
        ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ N,
          ∫ ω, |L k N ω / vol k - ∑ j : Fin d, p j ^ 2| ∂P ≤ eps := by
  obtain ⟨dC, hdC, hcor⟩ := cor_37 d hd hJ
  refine ⟨dC, hdC, ?_⟩
  intro _ _ model hmodel Ω _ P field hfield hmap Poincare hPoincare L vol p hvolQ hL eps heps
  obtain ⟨k0, hk0⟩ := hcor model hmodel (fun k => ⟨Poincare k, hPoincare k⟩) p eps heps
  refine ⟨k0, fun k hk N => ?_⟩
  exact (aux_thm_c1_transfer model P field hfield hmap k N ⟨Poincare k, hPoincare k⟩ p
    (fun ω => L k N ω) (vol k) (hL.mono fun ω h => h k N) (hvolQ k)).trans_le
    (hk0 k hk N)

/-- The normalizer `vol k` is the volume of `Q_{3^k}`. -/
theorem aux_thm_c1_volQ {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (qidx : ℕ → ℕ)
    (hq : ∀ k, z (qidx k) = 0 ∧ r (qidx k) = (3 : ℝ) ^ k) (k : ℕ) :
    (volume (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
        Set (SpatialCoordinates d))).toReal =
      (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal := by
  have h1 := centeredCube_volume_real (z (qidx k)) (hr (qidx k))
  have h2 := centeredCube_volume_real (0 : SpatialCoordinates d)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  rw [measureReal_def] at h1 h2
  rw [h1, h2, (hq k).2]

theorem aux_thm_c1_volQ_pos {d : ℕ} (k : ℕ) :
    0 < (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal := by
  have h2 := centeredCube_volume_pos (0 : SpatialCoordinates d)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  rwa [measureReal_def] at h2

/-- The first unit loading `e_0`. -/
noncomputable def aux_thm_c1_e0 (d : ℕ) (hd0 : 0 < d) : Fin d → ℝ :=
  fun j => if j = ⟨0, hd0⟩ then 1 else 0

theorem aux_thm_c1_e0_sq (d : ℕ) (hd0 : 0 < d) :
    (1 : ℝ) ^ 2 = ∑ j : Fin d, aux_thm_c1_e0 d hd0 j ^ 2 := by
  simp [aux_thm_c1_e0, apply_ite (fun x : ℝ => x ^ 2), Finset.sum_ite_eq']

theorem aux_thm_c1_vol_pos {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    0 < (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  have h := centeredCube_volume_pos z hr
  rwa [measureReal_def] at h

/-- The uniform moment input gives integrability of every normalized response. -/
theorem aux_thm_c1_int_of_moment {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (f : ℕ → Ω → ℝ)
    (h : ∃ q : ℝ≥0∞, 1 < q ∧ q ≠ ∞ ∧ ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ N,
      MemLp (f N) q P ∧ eLpNorm (f N) q P ≤ B) (N : ℕ) :
    Integrable (f N) P := by
  obtain ⟨q, hq1, -, B, -, hB⟩ := h
  exact (hB N).1.integrable hq1.le

/-- The scalar core of the proof : the calibration passes to both
candidate responses by Fatou, and proportional responses force `c = 1`. -/
theorem aux_thm_c1_core {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (LN : ℕ → ℕ → Ω → ℝ) (LE LF : ℕ → Ω → ℝ) (vol : ℕ → ℝ) (hvol : ∀ k, 0 < vol k)
    (NE NF : ℕ → ℕ) (s : ℝ) (hs : (1 : ℝ) ^ 2 = s)
    (hint : ∀ k N, Integrable (fun ω => LN k N ω / vol k) P)
    (hEconv : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => LN k (NE n) ω) atTop (𝓝 (LE k ω)))
    (hFconv : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => LN k (NF n) ω) atTop (𝓝 (LF k ω)))
    (hcal : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ N,
      ∫ ω, |LN k N ω / vol k - s| ∂P ≤ eps)
    (c : ℝ) (hc : 0 < c) (hscale : ∀ k, ∀ᵐ ω ∂P, LF k ω = c * LE k ω) : c = 1 := by
  have hElim := aux_thm_c1_limit_calibration P LN LE vol s NE hint hEconv hcal
  have hFlim := aux_thm_c1_limit_calibration P LN LF vol s NF hint hFconv hcal
  refine thm_c1_scalar c hc 1 one_pos (fun k => ∫ ω, LE k ω ∂P) (fun k => ∫ ω, LF k ω ∂P)
    vol hvol ?_ ?_ ?_
  · intro k
    show ∫ ω, LF k ω ∂P = c * ∫ ω, LE k ω ∂P
    rw [integral_congr_ae (hscale k), integral_const_mul]
  · rw [hs]
    exact aux_thm_c1_expect_tendsto P LE vol s hElim
  · rw [hs]
    exact aux_thm_c1_expect_tendsto P LF vol s hFlim

/-- Almost-sure scalar response scaling of the boundary minima on the padded roots. -/
theorem aux_thm_c1_scale_ae {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Qc : ℕ → Opens (SpatialCoordinates d))
    (E F E0 F0 : (i : ℕ) → Ω →
      _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Qc i : Set (SpatialCoordinates d))))
    (GamE : ∀ i ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E i ω))
    (GamF : ∀ i ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (F i ω))
    (GamE0 : ∀ i ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E0 i ω))
    (GamF0 : ∀ i ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (F0 i ω))
    (rho : ℕ → Ω → SpatialCoordinates d → ℝ)
    (GE GF : (i : ℕ) → Ω → DomainL2 (Qc i) →L[ℝ] DomainL2 (Qc i))
    (hwE : ∀ᵐ ω ∂P, ∀ i,
      _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm (E i ω) (E0 i ω) (GamE i ω) (rho i ω))
    (hwF : ∀ᵐ ω ∂P, ∀ i,
      _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm (F i ω) (F0 i ω) (GamF i ω) (rho i ω))
    (hE : ∀ᵐ ω ∂P, ∀ i u, (E i ω).energy u = limitFormEnergy (GE i ω) u)
    (hF : ∀ᵐ ω ∂P, ∀ i u, (F i ω).energy u = limitFormEnergy (GF i ω) u)
    (hGS : ∀ᵐ ω ∂P, ∀ i (c : ℝ), 0 < c →
      (F i ω).domain = (E i ω).domain →
      (∀ u ∈ (E i ω).domain, (F i ω).form u u = c * (E i ω).form u u) →
      ∀ u ∈ (E i ω).domain,
        (GamF i ω).measure u = ENNReal.ofReal c • (GamE i ω).measure u)
    (hG0S : ∀ᵐ ω ∂P, ∀ i (c : ℝ), 0 < c →
      (F0 i ω).domain = (E0 i ω).domain →
      (∀ u ∈ (E0 i ω).domain, (F0 i ω).form u u = c * (E0 i ω).form u u) →
      ∀ u ∈ (E0 i ω).domain,
        (GamF0 i ω).measure u = ENNReal.ofReal c • (GamE0 i ω).measure u)
    (c : ℝ) (hc : 0 < c)
    (hpc : ∀ᵐ ω ∂P, ∀ i : ℕ,
      limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
      ∀ u : DomainL2 (Qc i), u ∈ limitFormDomain (GE i ω) →
        (limitFormEnergy (GF i ω) u).toReal = c * (limitFormEnergy (GE i ω) u).toReal)
    (root : ℕ) (A : (SpatialCoordinates d → ℝ) → Prop)
    (B : DomainL2 (Qc root) → (SpatialCoordinates d → ℝ) → Prop)
    (C : (SpatialCoordinates d → ℝ) → Prop) (S : Set (SpatialCoordinates d))
    (LE LF : Ω → ℝ)
    (hLE : ∀ᵐ ω ∂P, LE ω = sInf {e : ℝ | ∃ U : DomainL2 (Qc root),
      U ∈ (E0 root ω).domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamE0 root ω).measure U S).toReal})
    (hLF : ∀ᵐ ω ∂P, LF ω = sInf {e : ℝ | ∃ U : DomainL2 (Qc root),
      U ∈ (F0 root ω).domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
        A Uc ∧ B U Uc ∧ C Uc ∧ e = ((GamF0 root ω).measure U S).toReal}) :
    ∀ᵐ ω ∂P, LF ω = c * LE ω := by
  filter_upwards [hpc, hwE, hwF, hE, hF, hGS, hG0S, hLE, hLF] with ω hpω hwEω hwFω hEω hFω
    hGSω hG0Sω hLEω hLFω
  rw [hLEω, hLFω]
  exact aux_thm_c1_sInf_scale (E root ω) (F root ω) (E0 root ω) (F0 root ω) (GamE root ω)
    (GamF root ω) (GamE0 root ω) (GamF0 root ω) (rho root ω) (GE root ω) (GF root ω)
    (hwEω root) (hwFω root) (hEω root) (hFω root) c hc (hpω root) (hGSω root c hc)
    (hG0Sω root c hc) A B C S

/-- With `c = 1`, the proportionality clause and the operator uniqueness interface give
the coincidence of the candidates. -/
theorem aux_thm_c1_coincide {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Qc : ℕ → Opens (SpatialCoordinates d))
    (GE GF : (i : ℕ) → Ω → DomainL2 (Qc i) →L[ℝ] DomainL2 (Qc i)) (c : ℝ) (hc1 : c = 1)
    (hpc : ∀ᵐ ω ∂P, ∀ i : ℕ,
      limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
      ∀ u : DomainL2 (Qc i), u ∈ limitFormDomain (GE i ω) →
        (limitFormEnergy (GF i ω) u).toReal = c * (limitFormEnergy (GE i ω) u).toReal)
    (hop : ∀ᵐ ω ∂P, ∀ i,
      limitFormDomain (GE i ω) = limitFormDomain (GF i ω) →
      (∀ u : DomainL2 (Qc i), u ∈ limitFormDomain (GE i ω) →
        limitFormEnergy (GE i ω) u = limitFormEnergy (GF i ω) u) →
      GE i ω = GF i ω) :
    ∀ᵐ ω ∂P, ∀ i : ℕ,
      GE i ω = GF i ω ∧
      limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
      ∀ u : DomainL2 (Qc i), limitFormEnergy (GE i ω) u = limitFormEnergy (GF i ω) u := by
  filter_upwards [hpc, hop] with ω hω hopω i
  obtain ⟨hdom, hen⟩ := hω i
  have heq := aux_thm_c1_energy_eq (GE i ω) (GF i ω) c hc1 hdom hen
  exact ⟨hopω i hdom (fun u _ => heq u), hdom, heq⟩



theorem thm_c1
    (d : ℕ) (hd : 2 ≤ d) [NeZero d] (hJ : in_J d)
    (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd hJ)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd hJ)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
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
    (_hResp :
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
              ENNReal.ofReal C)
    (t beta : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hbeta : 1 / 2 < beta) (_hbetaAlpha : beta < aux_thm_prop_alpha d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        ∀ (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF),
        ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
          (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model hJ Sreg),
        ∀ (_hBounds : _root_.SubdiffusiveProcess.Paper.aux_thm_prop_bounds_pointwise d hd model H z r hr Sspace NE NF)
          (_hEnum : _root_.SubdiffusiveProcess.Paper.in_represented_enum d z r hr),
        @aux_thm_c1_catalogues d hd _ _ model H Ω _ P hJoint.1 field z r hr Sspace NE NF
          (aux_thm_prop_alpha d hd) (1 / 128) beta t →
        (∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) →
      ∀ (qidx rootidx : ℕ → ℕ),
        (∀ k, z (qidx k) = 0 ∧ r (qidx k) = (3 : ℝ) ^ k) →
        (∀ k, z (rootidx k) = 0 ∧ r (rootidx k) = 3 * ((3 : ℝ) ^ k)) →
        (∀ k, (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
          Set (SpatialCoordinates d)) ⊆
          (centeredCube (z (rootidx k)) (r (rootidx k)) (hr (rootidx k)) :
            Set (SpatialCoordinates d))) →
      (let vol : ℕ → ℝ := fun k =>
          (volume (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
            Set (SpatialCoordinates d))).toReal;
      ∀ (rho : ℕ → Ω → SpatialCoordinates d → ℝ)
        (Eform Fform E0form F0form :
          (i : ℕ) → Ω → _root_.SubdiffusiveProcess.DirichletForm
            (volume.restrict (centeredCube (z i) (r i) (hr i) :
              Set (SpatialCoordinates d))))
        (GammaE : ∀ i (omega : Ω),
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Eform i omega).toClosedForm)
        (GammaF : ∀ i (omega : Ω),
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Fform i omega).toClosedForm)
        (GammaE0 : ∀ i (omega : Ω),
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E0form i omega).toClosedForm)
        (GammaF0 : ∀ i (omega : Ω),
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (F0form i omega).toClosedForm)
        (GE0 GF0 : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (_hweightE : ∀ᵐ omega ∂P, ∀ i,
          _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm
            (Eform i omega).toClosedForm (E0form i omega).toClosedForm
            (GammaE i omega) (rho i omega))
        (_hweightF : ∀ᵐ omega ∂P, ∀ i,
          _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm
            (Fform i omega).toClosedForm (F0form i omega).toClosedForm
            (GammaF i omega) (rho i omega))
        (_hGammaScale : ∀ᵐ omega ∂P, ∀ i (c : ℝ), 0 < c →
          (Fform i omega).toClosedForm.domain = (Eform i omega).toClosedForm.domain →
          (∀ u ∈ (Eform i omega).toClosedForm.domain,
            (Fform i omega).toClosedForm.form u u =
              c * (Eform i omega).toClosedForm.form u u) →
          ∀ u ∈ (Eform i omega).toClosedForm.domain,
            (GammaF i omega).measure u = ENNReal.ofReal c • (GammaE i omega).measure u)
        (_hGamma0Scale : ∀ᵐ omega ∂P, ∀ i (c : ℝ), 0 < c →
          (F0form i omega).toClosedForm.domain = (E0form i omega).toClosedForm.domain →
          (∀ u ∈ (E0form i omega).toClosedForm.domain,
            (F0form i omega).toClosedForm.form u u =
              c * (E0form i omega).toClosedForm.form u u) →
          ∀ u ∈ (E0form i omega).toClosedForm.domain,
            (GammaF0 i omega).measure u = ENNReal.ofReal c • (GammaE0 i omega).measure u)
        (_hrho : ∀ᵐ omega ∂P, ∀ i x,
          rho i omega x = Real.exp (-(H (field omega)) x))
        (_hEform : ∀ᵐ omega ∂P, ∀ i u,
          (Eform i omega).toClosedForm.energy u = limitFormEnergy (GE i omega) u)
        (_hFform : ∀ᵐ omega ∂P, ∀ i u,
          (Fform i omega).toClosedForm.energy u = limitFormEnergy (GF i omega) u)
        (_hE0form : ∀ᵐ omega ∂P, ∀ i u,
          (E0form i omega).toClosedForm.energy u = limitFormEnergy (GE0 i omega) u)
        (_hF0form : ∀ᵐ omega ∂P, ∀ i u,
          (F0form i omega).toClosedForm.energy u = limitFormEnergy (GF0 i omega) u)
        (_hrhocont : ∀ᵐ omega ∂P, ∀ i,
          ContinuousOn (rho i omega)
            (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))))
        (_hrhopos : ∀ᵐ omega ∂P, ∀ i x,
          x ∈ closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) →
            0 < rho i omega x)
        (LamN0 : ℕ → ℕ → (Fin d → ℝ) → Ω → ℝ)
        (LamE0 LamF0 : ℕ → (Fin d → ℝ) → Ω → ℝ)
        (Poincare : ℕ → ℝ≥0)
        (hPoincare : ∀ k (u : killedSobolevGraph
            (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
              (pow_pos (by norm_num) k))),
          ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d)
              ((3 : ℝ) ^ k) (pow_pos (by norm_num) k))).1‖ ≤
            Poincare k * ‖subspaceGradient
              (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d)
                ((3 : ℝ) ^ k) (pow_pos (by norm_num) k))) u‖)
        (_hLamN0 : ∀ᵐ omega ∂P, ∀ k N p,
          LamN0 k N p omega =
            affineDirichletResponse
              (centeredCube_isBounded (0 : SpatialCoordinates d)
                (pow_pos (by norm_num) k))
              ⟨Poincare k, hPoincare k⟩
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model
                (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (field omega) N 0
                (pow_pos (by norm_num) k)) p)
        (_hLamEconv : ∀ k p, ∀ᵐ omega ∂P,
          Tendsto (fun n => LamN0 k (NE n) p omega) atTop
            (𝓝 (LamE0 k p omega)))
        (_hLamFconv : ∀ k p, ∀ᵐ omega ∂P,
          Tendsto (fun n => LamN0 k (NF n) p omega) atTop
            (𝓝 (LamF0 k p omega)))
        (_hmoment : ∀ k p, ∃ q : ℝ≥0∞, 1 < q ∧ q ≠ ∞ ∧
          ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ N,
            MemLp (fun omega =>
              LamN0 k N p omega / vol k) q P ∧
            eLpNorm (fun omega =>
              LamN0 k N p omega / vol k) q P ≤ B)
        (_hLamEboundary : ∀ k p, ∀ᵐ omega ∂P,
          LamE0 k p omega =
            sInf {e : ℝ | ∃ U : DomainL2
              (centeredCube (z (rootidx k)) (r (rootidx k)) (hr (rootidx k))),
              U ∈ (E0form (rootidx k) omega).toClosedForm.domain ∧
              ∃ Uc : SpatialCoordinates d → ℝ,
                ContinuousOn Uc
                    (closure (centeredCube (z (rootidx k)) (r (rootidx k))
                      (hr (rootidx k)) : Set (SpatialCoordinates d))) ∧
                (U : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube (z (rootidx k)) (r (rootidx k))
                    (hr (rootidx k)) : Set (SpatialCoordinates d))] Uc ∧
                (∀ x ∈ frontier (centeredCube (z (qidx k)) (r (qidx k))
                    (hr (qidx k)) : Set (SpatialCoordinates d)),
                  Uc x = ∑ j : Fin d, p j * x j) ∧
                e = ((GammaE0 (rootidx k) omega).measure U
                  (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
                    Set (SpatialCoordinates d))).toReal})
        (_hLamFboundary : ∀ k p, ∀ᵐ omega ∂P,
          LamF0 k p omega =
            sInf {e : ℝ | ∃ U : DomainL2
              (centeredCube (z (rootidx k)) (r (rootidx k)) (hr (rootidx k))),
              U ∈ (F0form (rootidx k) omega).toClosedForm.domain ∧
              ∃ Uc : SpatialCoordinates d → ℝ,
                ContinuousOn Uc
                    (closure (centeredCube (z (rootidx k)) (r (rootidx k))
                      (hr (rootidx k)) : Set (SpatialCoordinates d))) ∧
                (U : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube (z (rootidx k)) (r (rootidx k))
                    (hr (rootidx k)) : Set (SpatialCoordinates d))] Uc ∧
                (∀ x ∈ frontier (centeredCube (z (qidx k)) (r (qidx k))
                    (hr (qidx k)) : Set (SpatialCoordinates d)),
                  Uc x = ∑ j : Fin d, p j * x j) ∧
                e = ((GammaF0 (rootidx k) omega).measure U
                  (centeredCube (z (qidx k)) (r (qidx k)) (hr (qidx k)) :
                    Set (SpatialCoordinates d))).toReal})
        (_hoperator_of_energy : ∀ᵐ omega ∂P, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) →
          (∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            limitFormEnergy (GE i omega) u = limitFormEnergy (GF i omega) u) →
          GE i omega = GF i omega),
        (∀ c : ℝ, 0 < c →
          (∀ᵐ omega ∂P, ∀ i : ℕ,
            limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
              (limitFormEnergy (GF i omega) u).toReal =
                c * (limitFormEnergy (GE i omega) u).toReal) →
          c = 1) ∧
        (∀ᵐ omega ∂P, ∀ i : ℕ,
          GE i omega = GF i omega ∧
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            limitFormEnergy (GE i omega) u = limitFormEnergy (GF i omega) u)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨δG, C0, hδG, hC0, hglob⟩ := thm_prop_global d hd hJ _X _Sob _Step _MeyersMorrey Pin D Cp Interp hES BD BDQ EM hcontract
  have hCc := aux_thm_c1_cal d hd hJ
  refine ⟨min δG hCc.choose, lt_min hδG hCc.choose_spec.1, ?_⟩
  intro _ _ model hmodel H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint Rm Sreg _It hBounds
    hEnum hCat hNonzero qidx rootidx hq
    hroot hsub vol rho Eform Fform E0form F0form GammaE GammaF GammaE0 GammaF0 GE0 GF0
    hweightE hweightF hGammaScale hGamma0Scale hrho hEform hFform hE0form hF0form hrhocont
    hrhopos LamN0 LamE0 LamF0 Poincare hPoincare hLamN0 hLamEconv hLamFconv hmoment
    hLamEboundary hLamFboundary hoperator_of_energy
  have hJ3 := aux_thm_c1_joint d model H Ω P field z r hr Sspace GN GE GF NE NF hJoint
  have := hJ3.1
  have hvolQ : ∀ k, vol k = (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal :=
    aux_thm_c1_volQ z r hr qidx hq
  have hvol_pos : ∀ k, 0 < vol k := fun k =>
    aux_thm_c1_vol_pos (z (qidx k)) (r (qidx k)) (hr (qidx k))
  -- calibration (`cor_37`) on the candidates' probability space, loading `e_0`
  have hcal0 := hCc.choose_spec.2 model (le_trans hmodel (min_le_right _ _)) Ω P field
    hJ3.2.1 hJ3.2.2 Poincare hPoincare (fun k N ω => LamN0 k N (aux_thm_c1_e0 d hd0) ω) vol
    (aux_thm_c1_e0 d hd0) hvolQ (hLamN0.mono fun ω h k N => h k N (aux_thm_c1_e0 d hd0))
  have hint : ∀ k N, Integrable (fun ω => LamN0 k N (aux_thm_c1_e0 d hd0) ω / vol k) P :=
    fun k => aux_thm_c1_int_of_moment P _ (hmoment k (aux_thm_c1_e0 d hd0))
  -- first conclusion: every proportionality constant is `1`
  have part1 : ∀ c : ℝ, 0 < c →
      (∀ᵐ omega ∂P, ∀ i : ℕ,
        limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
        ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
          u ∈ limitFormDomain (GE i omega) →
          (limitFormEnergy (GF i omega) u).toReal =
            c * (limitFormEnergy (GE i omega) u).toReal) →
      c = 1 := fun c hc hpc =>
    aux_thm_c1_core P (fun k N ω => LamN0 k N (aux_thm_c1_e0 d hd0) ω)
      (fun k ω => LamE0 k (aux_thm_c1_e0 d hd0) ω) (fun k ω => LamF0 k (aux_thm_c1_e0 d hd0) ω)
      vol hvol_pos NE NF _ (aux_thm_c1_e0_sq d hd0) hint
      (fun k => hLamEconv k (aux_thm_c1_e0 d hd0)) (fun k => hLamFconv k (aux_thm_c1_e0 d hd0))
      hcal0 c hc (fun k =>
        aux_thm_c1_scale_ae P (fun i => centeredCube (z i) (r i) (hr i))
          (fun i ω => (Eform i ω).toClosedForm) (fun i ω => (Fform i ω).toClosedForm)
          (fun i ω => (E0form i ω).toClosedForm) (fun i ω => (F0form i ω).toClosedForm)
          GammaE GammaF GammaE0 GammaF0 rho GE GF hweightE hweightF hEform hFform
          hGammaScale hGamma0Scale c hc hpc (rootidx k) _ _ _ _
          (fun ω => LamE0 k (aux_thm_c1_e0 d hd0) ω) (fun ω => LamF0 k (aux_thm_c1_e0 d hd0) ω)
          (hLamEboundary k (aux_thm_c1_e0 d hd0)) (hLamFboundary k (aux_thm_c1_e0 d hd0)))
  refine ⟨part1, ?_⟩
  -- second conclusion: the candidates coincide.  The catalogue blocks and the cubes `Q(0, 3^k)` give
  -- the whole rational triadic family, so the global proportionality applies directly.
  have hglobal := aux_thm_c1_global_family d hd model H Ω P field z r hr Sspace NE NF
    (aux_thm_prop_alpha d hd) (1 / 128) beta t hCat qidx hq
  obtain ⟨c, hc1, hc2, hcae⟩ := hglob model (le_trans hmodel (min_le_left _ _)) H Ω P field z r hr
    Sspace GN GE GF NE NF hJoint Rm Sreg _It hglobal.1 hglobal.2 hNonzero
  have hc : ∃ c : ℝ, 0 < c ∧ ∀ᵐ omega ∂P, ∀ i : ℕ,
      limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
      ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
        u ∈ limitFormDomain (GE i omega) →
        (limitFormEnergy (GF i omega) u).toReal =
          c * (limitFormEnergy (GE i omega) u).toReal :=
    ⟨c, lt_of_lt_of_le (inv_pos.2 (lt_of_lt_of_le one_pos hC0)) hc1,
      hcae.mono fun omega h i => (h.1 i)⟩
  exact aux_thm_c1_coincide P (fun i => centeredCube (z i) (r i) (hr i)) GE GF hc.choose
    (part1 hc.choose hc.choose_spec.1 hc.choose_spec.2) hc.choose_spec.2 hoperator_of_energy

end SubdiffusiveProcess.Paper

