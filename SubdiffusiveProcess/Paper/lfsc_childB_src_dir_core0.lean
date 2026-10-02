import SubdiffusiveProcess.FiniteStopping.SourcedStageAt
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
import SubdiffusiveProcess.Sobolev.DirichletComparison
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.lem_finite_stopping_crude_cost
import SubdiffusiveProcess.Paper.lem_finite_stopping_moments
import SubdiffusiveProcess.Paper.lfsc_childB_src_dir_core

/-!
# `lfsc_childB_src_dir_core0` — sourced ChildB (Dirichlet), infrared cutoff zero, by weight transfer

Paper `\label{mfd:lem-finite-source-comparison}`, last paragraph of the proof: for `A_N^0 = e^{-H}A_N` the estimates follow
from the same regularity argument; the common weight `w = e^{-H}` is bounded on the working cube by `e^{‖H‖_{L^∞(Q)}}`, a random
constant with every finite moment, added to the finite list of constants.  Here the solution `u` of the flag-0 problem
has its Hölder representative and global energy bound from the flag-0 growth input (`hG`, coefficient `0`); the
extension estimate is used for the infrared coefficient `e^{H}A_T` (`hKe3`), and the response for the target coefficient
`A^0_T` is compared with it by the Dirichlet principle: `resp(A^0_T) ≤ (sup e^{-H}) resp(A^H_T)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

/-- The zero-infrared coefficient is `e^{-H}` times the infrared coefficient. -/
theorem aux_lfsc_childB_src_dir_core0_coeff {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (T : ℕ)
    (x : SpatialCoordinates d) :
    cutoffCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega T x =
      Real.exp (-(H omega x)) * cutoffCoefficient model H omega T x := by
  unfold cutoffCoefficient cutoffPotential
  simp only [Pi.zero_apply, ContinuousMap.zero_apply, zero_add]
  rw [show H omega x + ∑ j ∈ Finset.range (T + 1), (omega (-(Int.ofNat j))) x -
      ((T : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P =
      H omega x + (∑ j ∈ Finset.range (T + 1), (omega (-(Int.ofNat j))) x -
      ((T : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) by ring, Real.exp_add]
  have : Real.exp (-(H omega x)) * ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model T)⁻¹ *
      (Real.exp (H omega x) * Real.exp (∑ j ∈ Finset.range (T + 1), (omega (-(Int.ofNat j))) x -
      ((T : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom model T)⁻¹ *
        (Real.exp (-(H omega x)) * Real.exp (H omega x)) *
        Real.exp (∑ j ∈ Finset.range (T + 1), (omega (-(Int.ofNat j))) x -
        ((T : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := by ring
  rw [this, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  ring

/-- **Weight transfer for the response**: the target response for the zero-infrared coefficient is at most the
sup of the weight `e^{-H}` on the root times the response for the infrared coefficient. -/
theorem aux_lfsc_childB_src_dir_core0_resp_transfer {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (T : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (W : ℝ)
    (hW : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), Real.exp (-(H omega x)) ≤ W)
    (u : weakSobolevGraph (centeredCube z r hr)) {U : Opens (SpatialCoordinates d)}
    (hU : U ≤ centeredCube z r hr)
    (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
      ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖) :
    SubdiffusiveProcess.FiniteStopping.respOn
        (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega T z hr)
        u hU hPU ≤
      W * SubdiffusiveProcess.FiniteStopping.respOn (cutoffPositiveCoefficient model H omega T z hr) u hU hPU := by
  have hzmem : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := Metric.mem_closedBall_self (by positivity)
  have hWpos : 0 < W := lt_of_lt_of_le (Real.exp_pos _) (hW z hzmem)
  unfold SubdiffusiveProcess.FiniteStopping.respOn
  set S := killedResponseSpace hPU with hS
  set aH' := positiveCoefficientRestrict hU (cutoffPositiveCoefficient model H omega T z hr) with haH'
  set a0' := positiveCoefficientRestrict hU
    (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega T z hr) with ha0'
  have hab : ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      a0'.val x ≤ (scalePositiveCoefficient W hWpos aH').val x := by
    have hrep0 := (cutoffPositiveCoefficient_representative model
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega T z hr).2.2.2
    have hrepH := (cutoffPositiveCoefficient_representative model H omega T z hr).2.2.2
    filter_upwards [positiveCoefficientRestrict_coeFn hU
        (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega T z hr),
      positiveCoefficientRestrict_coeFn hU (cutoffPositiveCoefficient model H omega T z hr),
      scalePositiveCoefficient_coeFn W hWpos aH',
      ae_restrict_of_ae_restrict_of_subset hU hrep0, ae_restrict_of_ae_restrict_of_subset hU hrepH,
      ae_restrict_mem U.isOpen.measurableSet] with x h0 hH' hs r0 rH hxU
    have hxc : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) :=
      centeredCube_subset_closedCube z hr (hU hxU)
    rw [hs, ha0', h0, r0, aux_lfsc_childB_src_dir_core0_coeff model H omega T x, haH', hH', rH]
    exact mul_le_mul_of_nonneg_right (hW x hxc)
      (cutoffCoefficient_pos model H omega T x).le
  calc dirichletResponse S a0' ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩
      ≤ dirichletResponse S (scalePositiveCoefficient W hWpos aH')
        ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩ :=
        dirichletResponse_mono S _ _ hab _
    _ = W * dirichletResponse S aH' ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩ :=
        dirichletResponse_scale_coefficient S W hWpos aH' _

/-- The random constant `e^{‖H‖_{L^∞(K)}}` of the weight transfer has an `L¹` bound. -/
theorem aux_lfsc_childB_src_dir_core0_wbank {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (Kc : Compacts (SpatialCoordinates d)) :
    ∃ CW : ℝ, MemLp (fun omega : BilateralField d => Real.exp ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ∧
      eLpNorm (fun omega : BilateralField d => Real.exp ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal CW := by
  obtain ⟨CH, hCH0, hmom⟩ :=
    SubdiffusiveProcess.exists_uniform_compactExponentialMoment_of_infraredCharacterization (d := d) hd
  obtain ⟨hint, hle⟩ := hmom model H hH Kc 1 zero_le_one
  simp only [one_mul] at hint hle
  refine ⟨2 * Real.exp (CH Kc * 1 ^ 2 * model.delta ^ 2), ?_, ?_⟩
  · rw [ENNReal.ofReal_one, memLp_one_iff_integrable]
    exact hint
  · rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm]
    have h1 : ∫⁻ omega, ‖Real.exp ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖‖ₑ
        ∂(chaosSampleLaw model).toMeasure =
        ENNReal.ofReal (∫ omega, Real.exp ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖
          ∂(chaosSampleLaw model).toMeasure) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun omega => (Real.exp_pos _).le))]
      congr 1
      ext omega
      exact Real.enorm_of_nonneg (Real.exp_pos _).le
    rw [h1]
    exact ENNReal.ofReal_le_ofReal hle

theorem aux_lfsc_childB_src_dir_core0_five {ε : ℝ} {N : ℕ} {a b c e : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (he0 : 0 ≤ e)
    (ha : a ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ))) (hb : b ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)))
    (hc : c ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ))) (he : e ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ))) :
    a * b * c ^ 2 * e ≤ (3 : ℝ) ^ (ε * (N : ℝ)) := by
  set E := (3 : ℝ) ^ (ε / 5 * (N : ℝ)) with hE
  have hE5 : E * E * E * E * E = (3 : ℝ) ^ (ε * (N : ℝ)) := by
    rw [hE, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hE0 : 0 ≤ E := ha0.trans ha
  have h1 : a * b ≤ E * E := mul_le_mul ha hb hb0 hE0
  have h2 : a * b * c ≤ E * E * E := mul_le_mul h1 hc hc0 (mul_nonneg hE0 hE0)
  have h3 : a * b * c * c ≤ E * E * E * E := mul_le_mul h2 hc hc0 (mul_nonneg (mul_nonneg hE0 hE0) hE0)
  have h4 : a * b * c * c * e ≤ E * E * E * E * E :=
    mul_le_mul h3 he he0 (mul_nonneg (mul_nonneg (mul_nonneg hE0 hE0) hE0) hE0)
  calc a * b * c ^ 2 * e = a * b * c * c * e := by ring
    _ ≤ _ := h4
    _ = _ := hE5

theorem aux_lfsc_childB_src_dir_core0_two {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ))) (hb : b ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ))) :
    a * b ≤ (3 : ℝ) ^ (ε * (N : ℝ)) := by
  set E := (3 : ℝ) ^ (ε / 5 * (N : ℝ)) with hE
  have hE1 : 1 ≤ E := Real.one_le_rpow (by norm_num) (by positivity)
  have hE5 : E * E * E * E * E = (3 : ℝ) ^ (ε * (N : ℝ)) := by
    rw [hE, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have h1 : a * b ≤ E * E := mul_le_mul ha hb hb0 (ha0.trans ha)
  have h2 : E * E ≤ E * E * E * E * E := by
    have hEE : 1 ≤ E * E * E := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ E) (by linarith : (0 : ℝ) ≤ E)]
  exact h1.trans (h2.trans (le_of_eq hE5))

/-- **Union of three event families** (shared by the assemblies of `lfsc_childB_src_dir` and `lfsc_childB_src_neu`):
if each of three properties `Q₁, Q₂, Q₃` of a sample holds outside an event of probability `≤ C_i 3^{-γ_i N}`
(for `N ≥ N₀^i`), then their conjunction holds outside one event of probability `≤ C 3^{-γ N}`. -/
theorem aux_lfsc_childB_src_dir_core0_union {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q1 Q2 Q3 : ℕ → ℕ → Bool → ℝ → Ω → Prop)
    (h1 : ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool, ∃ Bad : Set Ω, MeasurableSet Bad ∧
        μ Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧ ∀ omega ∉ Bad, Q1 N M reverse ε omega)
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool, ∃ Bad : Set Ω, MeasurableSet Bad ∧
        μ Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧ ∀ omega ∉ Bad, Q2 N M reverse ε omega)
    (h3 : ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool, ∃ Bad : Set Ω, MeasurableSet Bad ∧
        μ Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧ ∀ omega ∉ Bad, Q3 N M reverse ε omega) :
    ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool, ∃ Bad : Set Ω, MeasurableSet Bad ∧
        μ Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
        ∀ omega ∉ Bad, Q1 N M reverse ε omega ∧ Q2 N M reverse ε omega ∧ Q3 N M reverse ε omega := by
  intro ε hε
  obtain ⟨C1, g1, N1, hC1, hg1, hE1⟩ := h1 ε hε
  obtain ⟨C2, g2, N2, hC2, hg2, hE2⟩ := h2 ε hε
  obtain ⟨C3, g3, N3, hC3, hg3, hE3⟩ := h3 ε hε
  refine ⟨C1 + C2 + C3, min g1 (min g2 g3), max N1 (max N2 N3), by positivity,
    lt_min hg1 (lt_min hg2 hg3), ?_⟩
  intro N M hN hNM reverse
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2 : N2 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : N3 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  obtain ⟨B1, hm1, hp1, hq1⟩ := hE1 N M hN1 hNM reverse
  obtain ⟨B2, hm2, hp2, hq2⟩ := hE2 N M hN2 hNM reverse
  obtain ⟨B3, hm3, hp3, hq3⟩ := hE3 N M hN3 hNM reverse
  have hmono : ∀ g : ℝ, min g1 (min g2 g3) ≤ g → (3 : ℝ) ^ (-g * (N : ℝ)) ≤
      (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ)) := by
    intro g hg
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : min g1 (min g2 g3) * (N : ℝ) ≤ g * (N : ℝ) := mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg N)
    linarith
  have hpos : 0 < (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨B1 ∪ B2 ∪ B3, (hm1.union hm2).union hm3, ?_, ?_⟩
  · have e1 : C1 * (3 : ℝ) ^ (-g1 * (N : ℝ)) ≤ C1 * (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmono g1 (min_le_left _ _)) hC1.le
    have e2 : C2 * (3 : ℝ) ^ (-g2 * (N : ℝ)) ≤ C2 * (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmono g2 ((min_le_right _ _).trans (min_le_left _ _))) hC2.le
    have e3 : C3 * (3 : ℝ) ^ (-g3 * (N : ℝ)) ≤ C3 * (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmono g3 ((min_le_right _ _).trans (min_le_right _ _))) hC3.le
    calc μ (B1 ∪ B2 ∪ B3) ≤ μ (B1 ∪ B2) + μ B3 := measure_union_le _ _
      _ ≤ (μ B1 + μ B2) + μ B3 := by gcongr; exact measure_union_le _ _
      _ ≤ (ENNReal.ofReal (C1 * (3 : ℝ) ^ (-g1 * (N : ℝ))) +
            ENNReal.ofReal (C2 * (3 : ℝ) ^ (-g2 * (N : ℝ)))) +
            ENNReal.ofReal (C3 * (3 : ℝ) ^ (-g3 * (N : ℝ))) := by gcongr
      _ ≤ (ENNReal.ofReal (C1 * (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ))) +
            ENNReal.ofReal (C2 * (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ)))) +
            ENNReal.ofReal (C3 * (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ))) := by
          exact add_le_add (add_le_add (ENNReal.ofReal_le_ofReal e1) (ENNReal.ofReal_le_ofReal e2))
            (ENNReal.ofReal_le_ofReal e3)
      _ = ENNReal.ofReal ((C1 + C2 + C3) * (3 : ℝ) ^ (-(min g1 (min g2 g3)) * (N : ℝ))) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  · intro omega hom
    exact ⟨hq1 omega (fun h => hom (Or.inl (Or.inl h))), hq2 omega (fun h => hom (Or.inl (Or.inr h))),
      hq3 omega (fun h => hom (Or.inr h))⟩

/-- **Sourced ChildB (Dirichlet), infrared cutoff zero**: for the coefficient `A^0 = e^{-H}A` (flag `0`), one event `Bad`
before all data, outside of which the zero-infrared final-depth responses and global energy are at most `3^{εN}` times the
data norm.  The growth input `hG` is for the coefficient `0`; the extension estimate `hKe3` is the infrared one. -/
theorem lfsc_childB_src_dir_core0 {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : Paper.in_J d)
    {σ α β η t C1 : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) (hβα : β ≤ α) (hαβ1 : α - β ≤ 1)
    (hσ : 2 - 2 * α + η ≤ σ) (hC1 : 0 < C1)
    (h1 : aux_lem_finite_stopping_crude_cost_ClauseOne Jc β C1)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ) (hH1 : 0 < H1)
    (Kg : ℕ → BilateralField d → ℝ) (Cg : Fin 1 → ℝ)
    (hG : aux_lem_finite_stopping_crude_cost_GrowthBody model
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z ((3 : ℝ) ^ j)
      (zpow_pos (by norm_num) j) t α 1 (fun _ => 1) Kg Cg)
    (Ke : ℕ → BilateralField d → ℝ) (Ce : ℝ)
    (hKe1 : ∀ N, MemLp (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hKe2 : ∀ N, eLpNorm (Ke N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Ce)
    (hKe3 : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η om (fun N => Ke N om)) :
    ∀ ε : ℝ, 0 < ε → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad, aux_lfsc_childB_src_dir_data σ model
        (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z j H1 N M reverse ε omega := by
  intro ε hε
  set P := (chaosSampleLaw model).toMeasure with hPdef
  have hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  set Wc : BilateralField d → ℝ := fun omega =>
    Real.exp ‖(H omega).restrict (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))‖ with hWc
  obtain ⟨CW, hWmem, hWbd⟩ := aux_lfsc_childB_src_dir_core0_wbank hd model H hH
    (closedCube z ((3 : ℝ) ^ j) hr)
  have hmem : ∀ (i : Fin 3) (J : ℕ), MemLp (![Kg, Ke, fun _ => Wc] i J) (ENNReal.ofReal 1) P := by
    intro i J
    fin_cases i
    · exact hG.1 0 J
    · exact hKe1 J
    · exact hWmem
  have hbd : ∀ (i : Fin 3) (J : ℕ),
      eLpNorm (![Kg, Ke, fun _ => Wc] i J) (ENNReal.ofReal 1) P ≤
        ENNReal.ofReal (max (max (Cg 0) Ce) CW) := by
    intro i J
    fin_cases i
    · exact (hG.2.1 0 J).trans (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_left _ _)))
    · exact (hKe2 J).trans (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_left _ _)))
    · exact hWbd.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  obtain ⟨Ctail, hCt, hloc⟩ :=
    Paper.lem_finite_stopping_moments d model 3 1 (max (max (Cg 0) Ce) CW) le_rfl
      ![Kg, Ke, fun _ => Wc] hmem hbd
  have hε5 : 0 < ε / 5 := by positivity
  obtain ⟨N1, hN1⟩ := aux_lem_finite_stopping_crude_cost_exists_nat_const_le_rpow
    (max (C1 * d) (((3 : ℝ) ^ d) ^ j.toNat)) _ hε5
  refine ⟨Ctail, ε / 5, max (max (4 * j.natAbs) (4 * H1)) N1, hCt, hε5, ?_⟩
  intro N M hN hNM reverse
  have hNj : 4 * j.natAbs ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNH : 4 * H1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN1 : N1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨Bad0, hBad0m, hBad0P, hBad0⟩ := hloc (ε / 5) hε5 N M
  have hGae : ∀ᵐ om ∂P, aux_lem_finite_stopping_crude_cost_GrowthAt model
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z ((3 : ℝ) ^ j)
      hr t α om (fun N => Kg N om) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η om (fun N => Ke N om) :=
    hG.2.2.2.and hKe3
  set Gc := {om | ¬ (aux_lem_finite_stopping_crude_cost_GrowthAt model
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z ((3 : ℝ) ^ j)
      hr t α om (fun N => Kg N om) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η om (fun N => Ke N om))}
    with hGc
  have hGc0 : P Gc = 0 := ae_iff.1 hGae
  refine ⟨Bad0 ∪ toMeasurable P Gc, hBad0m.union (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · calc P (Bad0 ∪ toMeasurable P Gc) ≤ P Bad0 + P (toMeasurable P Gc) := measure_union_le _ _
      _ = P Bad0 := by rw [measure_toMeasurable, hGc0, add_zero]
      _ ≤ ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-1 * (ε / 5) * (N : ℝ))) := hBad0P
      _ = ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-(ε / 5) * (N : ℝ))) := by ring_nf
  intro omega homega
  have hω0 : omega ∉ Bad0 := fun h => homega (Or.inl h)
  have hωG : aux_lem_finite_stopping_crude_cost_GrowthAt model
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z ((3 : ℝ) ^ j)
      hr t α omega (fun N => Kg N omega) ∧
      aux_lem_finite_stopping_crude_cost_ClauseTwoAt Jc model H z j β η omega (fun N => Ke N omega) := by
    by_contra h
    exact homega (Or.inr (subset_toMeasurable P Gc h))
  have hK := hBad0 omega hω0
  have hKgN : |Kg N omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 0).1
  have hKgM : |Kg M omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 0).2
  have hKeN : |Ke N omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 1).1
  have hKeM : |Ke M omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 1).2
  have hWω : |Wc omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (hK 2).1
  have hWpos : 0 ≤ Wc omega := (Real.exp_pos _).le
  have hWω' : Wc omega ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := (le_abs_self _).trans hWω
  have hmono : (3 : ℝ) ^ (ε / 5 * (N1 : ℝ)) ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hNN1) hε5.le)
  have hC1d : C1 * d ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := ((le_max_left _ _).trans hN1).trans hmono
  have h3d : ((3 : ℝ) ^ d) ^ j.toNat ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) :=
    ((le_max_right _ _).trans hN1).trans hmono
  have hT : N ≤ (if reverse then M else N) := by cases reverse <;> simp [hNM]
  have hKeT : |Ke (if reverse then M else N) omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := by
    cases reverse
    · exact hKeN
    · exact hKeM
  have hKgS : |Kg (if reverse then N else M) omega| ≤ (3 : ℝ) ^ (ε / 5 * (N : ℝ)) := by
    cases reverse
    · exact hKgM
    · exact hKgN
  have hC1d0 : 0 ≤ C1 * d := mul_nonneg hC1.le (Nat.cast_nonneg d)
  have hcellc := aux_lfsc_childB_src_dir_core0_five hC1d0 (abs_nonneg _) (abs_nonneg _) hWpos
    hC1d hKeT hKgS hWω'
  have hrootc := aux_lfsc_childB_src_dir_core0_two hε.le
    (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ d) ^ j.toNat) (abs_nonneg _) h3d hKgS
  intro F Kf hKf hFm hFb phi hphi b u hb hsol
  have hfin := aux_lfsc_childB_src_dir_omega (Hs := (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
    (Ht := H) hd Jc hβ hβα hαβ1 hσ hC1 h1 z j hr H1 hH1
    N hNj hNH (if reverse then M else N) (if reverse then N else M) hT omega
    (fun N => Kg N omega) (fun N => Ke N omega) hωG.1 hωG.2 F Kf hKf hFm hFb phi hphi b u hb hsol
  obtain ⟨hcell, hroot⟩ := hfin
  have hg0 : 0 ≤ c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi :=
    aux_lem_finite_stopping_crude_cost_c2Norm_nonneg _ _
  have hBd : 0 ≤ (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2 :=
    sq_nonneg _
  have hWpt : ∀ x ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
      Real.exp (-(H omega x)) ≤ Wc omega := by
    intro x hx
    rw [hWc]
    apply Real.exp_le_exp.mpr
    have hb := ((H omega).restrict (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))).norm_coe_le_norm
      ⟨x, hx⟩
    have : -(H omega x) ≤ |H omega x| := neg_le_abs _
    exact this.trans (by rw [← Real.norm_eq_abs]; exact hb)
  refine ⟨fun w0 w => ?_, hroot.trans ?_⟩
  · refine (aux_lfsc_childB_src_dir_core0_resp_transfer model H omega (if reverse then M else N) z hr
      (Wc omega) hWpt u _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (hcell w0 w) hWpos).trans ?_
    have hside := Real.rpow_nonneg (descendantSide_pos (subdivisionHalfWidth H1)
      (SubdiffusiveProcess.FiniteStopping.obsB H1 N)
      (descendantSide_pos 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) hr)).le ((d : ℝ) - σ)
    calc Wc omega * (C1 * (d : ℝ) * |Ke (if reverse then M else N) omega| *
          |Kg (if reverse then N else M) omega| ^ 2 *
          (descendantSide (subdivisionHalfWidth H1) (SubdiffusiveProcess.FiniteStopping.obsB H1 N)
            (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))) ^
              ((d : ℝ) - σ) *
            (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2)
        = (C1 * (d : ℝ) * |Ke (if reverse then M else N) omega| *
          |Kg (if reverse then N else M) omega| ^ 2 * Wc omega) *
          (descendantSide (subdivisionHalfWidth H1) (SubdiffusiveProcess.FiniteStopping.obsB H1 N)
            (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))) ^
              ((d : ℝ) - σ) *
            (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2 := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hBd
        exact mul_le_mul_of_nonneg_right hcellc hside
  · exact mul_le_mul_of_nonneg_right hrootc hBd

end Paper
