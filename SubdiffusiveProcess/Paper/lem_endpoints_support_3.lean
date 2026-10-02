import Mathlib.Tactic
import SubdiffusiveProcess.Paper.lem_endpoints_support_2

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper

theorem aux_lem_endpoints_support_3_candidates_symm_nonneg (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) :
    ∀ᵐ omega ∂P, ∀ i : ℕ,
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GE i omega x))) ∧
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GF i omega x))) := by
  obtain ⟨-, -, -, -, -, -, hGN, hconv⟩ := hJoint
  filter_upwards [hconv] with omega hconvomega i
  have hsym : ∀ N (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GN i N omega x) y = inner ℝ x (GN i N omega y) := by
    intro N x y
    rw [hGN i N omega x, hGN i N omega y, real_inner_comm]
    exact volumeResponse_pairing_symm _ _ y x
  have hpos : ∀ N (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      0 ≤ inner ℝ x (GN i N omega x) := by
    intro N x
    rw [hGN i N omega x]
    exact volumeResponse_pairing_nonneg _ _ x
  exact ⟨lem_endpoints_support_2 _ _ (hconvomega i).1 (fun n => hsym (NE n))
      (fun n => hpos (NE n)),
    lem_endpoints_support_2 _ _ (hconvomega i).2 (fun n => hsym (NF n))
      (fun n => hpos (NF n))⟩

theorem aux_lem_endpoints_support_3_energy_range {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) (f : DomainL2 Q) :
    limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun g => EReal.coe_le_coe_iff.mpr ?_
    have h := hpos (g - f)
    have h1 : inner ℝ (g - f) (G (g - f)) =
        inner ℝ g (G g) - 2 * inner ℝ g (G f) + inner ℝ f (G f) := by
      have hgf : inner ℝ f (G g) = inner ℝ g (G f) := by
        rw [← hsym f g, real_inner_comm]
      simp only [map_sub, inner_sub_left, inner_sub_right, hgf]
      ring
    linarith
  · refine le_iSup_of_le f (EReal.coe_le_coe_iff.mpr (le_of_eq ?_))
    ring

theorem aux_lem_endpoints_support_3_response_of_ne_zero {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) (hG : G ≠ 0) :
    ∃ f : DomainL2 Q, 0 < inner ℝ f (G f) := by
  by_contra hcon
  push_neg at hcon
  have h0 : ∀ f : DomainL2 Q, inner ℝ f (G f) = 0 := fun f => le_antisymm (hcon f) (hpos f)
  have hmix : ∀ f g : DomainL2 Q, inner ℝ f (G g) = 0 := by
    intro f g
    have h1 := h0 (f + g)
    have hgf : inner ℝ g (G f) = inner ℝ f (G g) := by rw [← hsym g f, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right, h0 f, h0 g, hgf] at h1
    linarith
  apply hG
  ext1 g
  have h2 := hmix (G g) g
  rw [real_inner_self_eq_norm_sq] at h2
  simpa using h2

theorem aux_lem_endpoints_support_3_dual_shift {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (u f h : DomainL2 Q) :
    2 * inner ℝ (h + f) u - inner ℝ (h + f) (G (h + f)) =
      (2 * inner ℝ h (u - G f) - inner ℝ h (G h)) +
        (2 * inner ℝ f u - inner ℝ f (G f)) := by
  have hfh : inner ℝ f (G h) = inner ℝ h (G f) := by
    rw [← hsym f h, real_inner_comm]
  simp only [map_add, inner_add_left, inner_add_right, inner_sub_right, hfh]
  ring

theorem aux_lem_endpoints_support_3_core_closure {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (GE x) y = inner ℝ x (GE y))
    (S : Set (DomainL2 Q)) (hS : Dense S) (K : ℝ) (hK : 0 ≤ K)
    (hcore : ∀ f ∈ S,
      limitFormEnergy GF (GE f) ≤ ((K * inner ℝ f (GE f) : ℝ) : EReal)) :
    ∀ u ∈ limitFormDomain GE,
      limitFormEnergy GF u ≤ ((K * (limitFormEnergy GE u).toReal : ℝ) : EReal) := by
  intro u hu
  have hu' : limitFormEnergy GE u < ⊤ := hu
  have hE0 := limitFormEnergy_nonneg GE u
  obtain ⟨e, hEu⟩ : ∃ e : ℝ, limitFormEnergy GE u = (e : EReal) :=
    ⟨_, (EReal.coe_toReal (ne_of_lt hu')
      (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hE0))).symm⟩
  rw [hEu, EReal.toReal_coe]
  have he0 : 0 ≤ e := by
    rw [hEu] at hE0
    exact EReal.coe_nonneg.mp hE0
  have hφ : ∀ g : DomainL2 Q, 2 * inner ℝ g u - inner ℝ g (GE g) ≤ e := by
    intro g
    have h1 : ((2 * inner ℝ g u - inner ℝ g (GE g) : ℝ) : EReal) ≤ limitFormEnergy GE u :=
      le_iSup (fun g : DomainL2 Q => ((2 * inner ℝ g u - inner ℝ g (GE g) : ℝ) : EReal)) g
    rw [hEu] at h1
    exact EReal.coe_le_coe_iff.mp h1
  have hdist : ∀ f : DomainL2 Q, ‖u - GE f‖ ^ 2 ≤
      (‖GE‖ + 1) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) := by
    intro f
    have hn : 0 < ‖GE‖ + 1 := by positivity
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = (‖GE‖ + 1)⁻¹ := ⟨_, rfl⟩
    have ht : 0 < t := by rw [ht_def]; exact inv_pos.mpr hn
    have h1 := hφ (t • (u - GE f) + f)
    rw [aux_lem_endpoints_support_3_dual_shift GE hsym u f (t • (u - GE f))] at h1
    simp only [real_inner_smul_left, map_smul, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at h1
    have hGv : inner ℝ (u - GE f) (GE (u - GE f)) ≤ ‖GE‖ * ‖u - GE f‖ ^ 2 := by
      calc inner ℝ (u - GE f) (GE (u - GE f)) ≤ ‖u - GE f‖ * ‖GE (u - GE f)‖ :=
            real_inner_le_norm _ _
        _ ≤ ‖u - GE f‖ * (‖GE‖ * ‖u - GE f‖) := by
            gcongr
            exact GE.le_opNorm _
        _ = ‖GE‖ * ‖u - GE f‖ ^ 2 := by ring
    have htG : t * ‖GE‖ ≤ 1 := by
      rw [ht_def, inv_mul_le_iff₀ hn]
      linarith
    have h2 : t * inner ℝ (u - GE f) (GE (u - GE f)) ≤ ‖u - GE f‖ ^ 2 := by
      calc t * inner ℝ (u - GE f) (GE (u - GE f)) ≤ t * (‖GE‖ * ‖u - GE f‖ ^ 2) := by
            gcongr
        _ = (t * ‖GE‖) * ‖u - GE f‖ ^ 2 := by ring
        _ ≤ 1 * ‖u - GE f‖ ^ 2 := by gcongr
        _ = ‖u - GE f‖ ^ 2 := one_mul _
    have h3 : t * (t * inner ℝ (u - GE f) (GE (u - GE f))) ≤ t * ‖u - GE f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 ht.le
    have key : t * ‖u - GE f‖ ^ 2 ≤ e - (2 * inner ℝ f u - inner ℝ f (GE f)) := by
      linarith
    calc ‖u - GE f‖ ^ 2 = (‖GE‖ + 1) * (t * ‖u - GE f‖ ^ 2) := by
          rw [ht_def, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
      _ ≤ (‖GE‖ + 1) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) :=
          mul_le_mul_of_nonneg_left key hn.le
  refine iSup_le fun g => ?_
  rw [EReal.coe_le_coe_iff]
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have hKe : 0 ≤ K * e := mul_nonneg hK he0
  obtain ⟨τ, hτpos, hτhalf, hτδ⟩ : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ 2 * (K * e) * τ ≤ δ / 3 := by
    refine ⟨min (1 / 2) (δ / (6 * (K * e + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    calc 2 * (K * e) * min (1 / 2) (δ / (6 * (K * e + 1)))
        ≤ 2 * (K * e) * (δ / (6 * (K * e + 1))) := by gcongr; exact min_le_right _ _
      _ = δ / 3 * ((K * e) / (K * e + 1)) := by field_simp; ring
      _ ≤ δ / 3 * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = δ / 3 := mul_one _
  obtain ⟨ρ0, hρ0pos, hρ0⟩ : ∃ ρ0 : ℝ, 0 < ρ0 ∧ 2 * (‖g‖ * ρ0) < δ / 3 := by
    refine ⟨δ / (6 * (‖g‖ + 1)), by positivity, ?_⟩
    have hx : 2 * (‖g‖ * (δ / (6 * (‖g‖ + 1)))) = δ / 3 * (‖g‖ / (‖g‖ + 1)) := by
      field_simp; ring
    rw [hx]
    have hlt : ‖g‖ / (‖g‖ + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hδ3 : 0 < δ / 3 := by positivity
    calc δ / 3 * (‖g‖ / (‖g‖ + 1)) < δ / 3 * 1 := by gcongr
      _ = δ / 3 := mul_one _
  obtain ⟨η0, hη0pos, hη0K, hη0ρ⟩ : ∃ η0 : ℝ, 0 < η0 ∧ K * η0 ≤ τ * (δ / 3) ∧
      (‖GE‖ + 1) * η0 ≤ ρ0 ^ 2 := by
    refine ⟨min (τ * (δ / 3) / (K + 1)) (ρ0 ^ 2 / (‖GE‖ + 1)),
      lt_min (by positivity) (by positivity), ?_, ?_⟩
    · calc K * min (τ * (δ / 3) / (K + 1)) (ρ0 ^ 2 / (‖GE‖ + 1))
          ≤ K * (τ * (δ / 3) / (K + 1)) := by gcongr; exact min_le_left _ _
        _ = τ * (δ / 3) * (K / (K + 1)) := by field_simp
        _ ≤ τ * (δ / 3) * 1 := by
            gcongr
            rw [div_le_one (by positivity)]
            linarith
        _ = τ * (δ / 3) := mul_one _
    · calc (‖GE‖ + 1) * min (τ * (δ / 3) / (K + 1)) (ρ0 ^ 2 / (‖GE‖ + 1))
          ≤ (‖GE‖ + 1) * (ρ0 ^ 2 / (‖GE‖ + 1)) := by gcongr; exact min_le_right _ _
        _ = ρ0 ^ 2 := by field_simp
  -- a source in `S` whose dual value is within `η0` of `E(u)`
  obtain ⟨f, hfS, hfU⟩ : ∃ f ∈ S, e - η0 < 2 * inner ℝ f u - inner ℝ f (GE f) := by
    have hlt : ((e - η0 / 2 : ℝ) : EReal) <
        ⨆ g : DomainL2 Q, ((2 * inner ℝ g u - inner ℝ g (GE g) : ℝ) : EReal) := by
      change _ < limitFormEnergy GE u
      rw [hEu]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨g0, hg0⟩ := lt_iSup_iff.mp hlt
    have hg0' : e - η0 / 2 < 2 * inner ℝ g0 u - inner ℝ g0 (GE g0) :=
      EReal.coe_lt_coe_iff.mp hg0
    have hcont : Continuous fun f : DomainL2 Q => 2 * inner ℝ f u - inner ℝ f (GE f) :=
      (continuous_const.mul (continuous_id.inner continuous_const)).sub
        (continuous_id.inner GE.continuous)
    have hopen : IsOpen {f : DomainL2 Q | e - η0 < 2 * inner ℝ f u - inner ℝ f (GE f)} :=
      isOpen_lt continuous_const hcont
    obtain ⟨f, hfS, hfU⟩ := hS.exists_mem_open hopen ⟨g0, by
      show e - η0 < 2 * inner ℝ g0 u - inner ℝ g0 (GE g0)
      linarith⟩
    exact ⟨f, hfS, hfU⟩
  have hφf := hφ f
  -- the distance `‖u - G_E f‖ < ρ0`
  have hv : ‖u - GE f‖ < ρ0 := by
    have h1 := hdist f
    have h2 : (‖GE‖ + 1) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) < ρ0 ^ 2 := by
      have hn : 0 < ‖GE‖ + 1 := by positivity
      calc (‖GE‖ + 1) * (e - (2 * inner ℝ f u - inner ℝ f (GE f)))
          < (‖GE‖ + 1) * η0 := by gcongr; linarith
        _ ≤ ρ0 ^ 2 := hη0ρ
    exact lt_of_pow_lt_pow_left₀ 2 hρ0pos.le (lt_of_le_of_lt h1 h2)
  -- the energy `⟨f, G_E f⟩ ≤ e + 2 e τ + η / τ`
  have ha_bd : τ * (1 - τ) * inner ℝ f (GE f) ≤
      τ * e + (1 - τ) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) := by
    have h := hφ ((1 - τ) • f)
    simp only [real_inner_smul_left, map_smul, real_inner_smul_right] at h
    nlinarith [h]
  have hτ1 : 0 < 1 - τ := by linarith
  have ha : K * inner ℝ f (GE f) ≤ K * e + δ / 3 + δ / 3 := by
    have hpp : 0 < τ * (1 - τ) := mul_pos hτpos hτ1
    have hRHS : (e + 2 * e * τ + (e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ) *
        (τ * (1 - τ)) = τ * e + (1 - τ) * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) +
          e * τ ^ 2 * (1 - 2 * τ) := by
      field_simp
      ring
    have hnn : 0 ≤ e * τ ^ 2 * (1 - 2 * τ) := by
      have : 0 ≤ 1 - 2 * τ := by linarith
      positivity
    have hA : inner ℝ f (GE f) ≤
        e + 2 * e * τ + (e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ := by
      refine le_of_mul_le_mul_right ?_ hpp
      rw [hRHS]
      nlinarith [ha_bd]
    have hη : K * ((e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ) ≤ δ / 3 := by
      rw [mul_div_assoc', div_le_iff₀ hτpos]
      have : K * (e - (2 * inner ℝ f u - inner ℝ f (GE f))) ≤ K * η0 :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      linarith
    calc K * inner ℝ f (GE f)
        ≤ K * (e + 2 * e * τ + (e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ) :=
          mul_le_mul_of_nonneg_left hA hK
      _ = K * e + 2 * (K * e) * τ +
          K * ((e - (2 * inner ℝ f u - inner ℝ f (GE f))) / τ) := by ring
      _ ≤ K * e + δ / 3 + δ / 3 := by linarith
  -- `ψ_g(G_E f) ≤ F(G_E f) ≤ K ⟨f, G_E f⟩`
  have hF : 2 * inner ℝ g (GE f) - inner ℝ g (GF g) ≤ K * inner ℝ f (GE f) := by
    have h1 : ((2 * inner ℝ g (GE f) - inner ℝ g (GF g) : ℝ) : EReal) ≤
        limitFormEnergy GF (GE f) :=
      le_iSup (fun g : DomainL2 Q =>
        ((2 * inner ℝ g (GE f) - inner ℝ g (GF g) : ℝ) : EReal)) g
    exact EReal.coe_le_coe_iff.mp (h1.trans (hcore f hfS))
  have hsplit : 2 * inner ℝ g u - inner ℝ g (GF g) =
      (2 * inner ℝ g (GE f) - inner ℝ g (GF g)) + 2 * inner ℝ g (u - GE f) := by
    rw [inner_sub_right]
    ring
  have hcs : inner ℝ g (u - GE f) ≤ ‖g‖ * ‖u - GE f‖ := real_inner_le_norm _ _
  have hgv : 2 * (‖g‖ * ‖u - GE f‖) ≤ 2 * (‖g‖ * ρ0) := by
    gcongr
  rw [hsplit]
  linarith

theorem aux_lem_endpoints_support_3_energy_coe {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) (hu : u ∈ limitFormDomain G) :
    limitFormEnergy G u = ((limitFormEnergy G u).toReal : EReal) := by
  have hu' : limitFormEnergy G u < ⊤ := hu
  exact (EReal.coe_toReal (ne_of_lt hu')
    (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg G u)))).symm

theorem aux_lem_endpoints_support_3_norm_sub_measurable_of_inner {X : Type*} [MeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SeparableSpace E]
    (F : X → E) (hF : ∀ g : E, Measurable (fun x => inner ℝ g (F x))) (c : E) :
    Measurable (fun x => ‖F x - c‖) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  haveI : Countable D := hDc.to_subtype
  have key : ∀ (v : E) (t : ℝ), 0 ≤ t → (‖v‖ ≤ t ↔ ∀ g ∈ D, inner ℝ g v ≤ t * ‖g‖) := by
    intro v t ht
    constructor
    · intro hv g _
      calc inner ℝ g v ≤ ‖g‖ * ‖v‖ := real_inner_le_norm g v
        _ ≤ ‖g‖ * t := mul_le_mul_of_nonneg_left hv (norm_nonneg g)
        _ = t * ‖g‖ := mul_comm _ _
    · intro h
      have hclosed : IsClosed {g : E | inner ℝ g v ≤ t * ‖g‖} :=
        isClosed_le (continuous_id.inner continuous_const) (continuous_const.mul continuous_norm)
      have huniv : Set.univ ⊆ {g : E | inner ℝ g v ≤ t * ‖g‖} := by
        rw [← hDd.closure_eq]
        exact hclosed.closure_subset_iff.mpr fun g hg => h g hg
      have hvv : inner ℝ v v ≤ t * ‖v‖ := huniv (Set.mem_univ v)
      rw [real_inner_self_eq_norm_sq] at hvv
      by_cases hv : v = 0
      · rw [hv, norm_zero]
        exact ht
      · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
        have h3 : ‖v‖ * ‖v‖ ≤ t * ‖v‖ := by rwa [pow_two] at hvv
        exact le_of_mul_le_mul_right h3 hvpos
  have keyc : ∀ (v : E) (t : ℝ), 0 ≤ t →
      (‖v - c‖ ≤ t ↔ ∀ g ∈ D, inner ℝ g v - inner ℝ g c ≤ t * ‖g‖) := by
    intro v t ht
    rw [key (v - c) t ht]
    constructor
    · intro h g hg
      have h' := h g hg
      rwa [inner_sub_right] at h'
    · intro h g hg
      rw [inner_sub_right]
      exact h g hg
  refine measurable_of_Iic (fun t => ?_)
  by_cases ht : 0 ≤ t
  · have hset : (fun x => ‖F x - c‖) ⁻¹' Iic t
        = ⋂ g : D, {x : X | inner ℝ (g : E) (F x) - inner ℝ (g : E) c ≤ t * ‖(g : E)‖} := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_iInter, mem_setOf_eq]
      rw [keyc (F x) t ht]
      constructor
      · intro h g
        exact h g g.2
      · intro h g hg
        exact h ⟨g, hg⟩
    rw [hset]
    exact MeasurableSet.iInter fun g : D =>
      measurableSet_le ((hF (g : E)).sub_const (inner ℝ (g : E) c)) measurable_const
  · have hset : (fun x => ‖F x - c‖) ⁻¹' Iic t = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.mp ht) (norm_nonneg (F x - c))
    rw [hset]
    exact MeasurableSet.empty

theorem aux_lem_endpoints_support_3_stronglyMeasurable_of_norm_sub {X : Type*} [MeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [SeparableSpace E]
    (F : X → E) (hF : ∀ c : E, Measurable (fun x => ‖F x - c‖)) :
    StronglyMeasurable F := by
  classical
  borelize E
  haveI : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  apply Measurable.stronglyMeasurable
  apply measurable_of_isOpen
  intro U hU
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense E
  haveI : Countable ↑D := hDc.to_subtype
  rw [Metric.isOpen_iff] at hU
  have hpre : F ⁻¹' U =
      ⋃ (p : {q : ↑D × ℚ // Metric.ball (q.1 : E) ((q.2 : ℚ) : ℝ) ⊆ U}),
        {x : X | ‖F x - (p.1.1 : E)‖ < ((p.1.2 : ℚ) : ℝ)} := by
    ext x
    constructor
    · intro hx
      rw [mem_preimage] at hx
      obtain ⟨ε, hε, hεU⟩ := hU (F x) hx
      obtain ⟨c, hcD, hcd⟩ := hDd.exists_dist_lt (F x) (show (0 : ℝ) < ε / 4 by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (ε / 4 : ℝ) < ε / 2 by linarith)
      have hcond : Metric.ball c ((q : ℚ) : ℝ) ⊆ U := by
        intro y hy
        rw [Metric.mem_ball, dist_eq_norm] at hy
        rw [dist_eq_norm] at hcd
        refine hεU ?_
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : ‖y - F x‖ ≤ ‖y - c‖ + ‖c - F x‖ := by
          rw [show y - F x = (y - c) + (c - F x) by abel]
          exact norm_add_le _ _
        rw [norm_sub_rev c (F x)] at h1
        linarith
      refine mem_iUnion.mpr ⟨⟨(⟨c, hcD⟩, q), hcond⟩, ?_⟩
      rw [dist_eq_norm] at hcd
      exact lt_trans hcd hq1
    · intro hx
      rw [mem_iUnion] at hx
      obtain ⟨p, hp⟩ := hx
      rw [mem_preimage]
      exact p.2 (by rw [Metric.mem_ball, dist_eq_norm]; exact hp)
  rw [hpre]
  apply MeasurableSet.iUnion
  intro p
  exact measurableSet_lt (hF (p.1.1 : E)) measurable_const

theorem aux_lem_endpoints_support_3_stronglyMeasurable_of_inner {X : Type*} [MeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SeparableSpace E]
    (F : X → E) (hF : ∀ g : E, Measurable (fun x => inner ℝ g (F x))) :
    StronglyMeasurable F :=
  aux_lem_endpoints_support_3_stronglyMeasurable_of_norm_sub F (aux_lem_endpoints_support_3_norm_sub_measurable_of_inner F hF)

theorem aux_lem_endpoints_support_3_polarization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E) (hsym : ∀ x y : E, inner ℝ (G x) y = inner ℝ x (G y)) (f g : E) :
    inner ℝ g (G f) =
      (inner ℝ (f + g) (G (f + g)) - inner ℝ (f - g) (G (f - g))) / 4 := by
  have hgf : inner ℝ f (G g) = inner ℝ g (G f) := by rw [← hsym f g, real_inner_comm]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, hgf]
  ring

theorem aux_lem_endpoints_support_3_pairing_eq_inverseResponse {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (h : DomainL2 Ω) :
    inner ℝ h (responseSolution S a ((sobolevVolumeLoad h).comp S.space.subtypeL)).val.1 =
      inverseResponse S a ((sobolevVolumeLoad h).comp S.space.subtypeL) := by
  rw [inverseResponse_eq_load]
  rfl

noncomputable def aux_lem_endpoints_support_3_logPotential {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
    ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
    (H om + ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)))

theorem aux_lem_endpoints_support_3_logPotential_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) :
    Measurable (aux_lem_endpoints_support_3_logPotential M H N) := by
  unfold aux_lem_endpoints_support_3_logPotential
  exact measurable_const.add
    (hH.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i))))

theorem aux_lem_endpoints_support_3_rootLog_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    continuousPositiveLog (Lane4.cutoffCoefficientCM M H om N z hr)
        (Lane4.cutoffCoefficientCM_pos M H om N z hr) =
      (aux_lem_endpoints_support_3_logPotential M H N om).restrict
        (closedCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  simp only [continuousPositiveLog, aux_lem_endpoints_support_3_logPotential,
    Lane4.cutoffCoefficientCM, ContinuousMap.coe_mk]
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
    (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  simp only [cutoffPotential]
  dsimp [ContinuousMap.restrict]
  simp only [ContinuousMap.sum_apply]
  ring

theorem aux_lem_endpoints_support_3_coeff_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    [Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr)] :
    Lane4.cutoffPositiveCoefficient M H om N z hr =
      expPotentialCoefficient (compactPotentialToLp (closedCube z r hr)
        ((aux_lem_endpoints_support_3_logPotential M H N om).restrict
          (closedCube z r hr : Set (SpatialCoordinates d)))) := by
  unfold Lane4.cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
  rw [aux_lem_endpoints_support_3_rootLog_eq]
  simp only [Real.log_one, ContinuousMap.const_zero, sub_zero]

theorem aux_lem_endpoints_support_3_inverseResponse_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (S : ResponseSpace (centeredCube z r hr))
    (L : S.space →L[ℝ] ℝ) :
    Measurable (fun om : BilateralField d =>
      inverseResponse S (Lane4.cutoffPositiveCoefficient M H om N z hr) L) := by
  haveI : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hD := ((continuous_inverseResponse_compact S (closedCube z r hr) L).comp
    (ContinuousMap.continuous_restrict
      (closedCube z r hr : Set (SpatialCoordinates d)))).measurable.comp
      (aux_lem_endpoints_support_3_logPotential_measurable M H hH N)
  convert hD using 1
  funext om
  rw [aux_lem_endpoints_support_3_coeff_eq M H N om z hr]
  rfl

theorem aux_lem_endpoints_support_3_canonical_response (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization model H)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))) :
    ∃ GNc : (i : ℕ) → ℕ → BilateralField d →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)),
      (∀ i N x f, GNc i N x f =
        (responseSolution (Sspace i)
          (Lane4.cutoffPositiveCoefficient model H x N (z i) (hr i))
          ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1) ∧
      (∀ i N (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
        StronglyMeasurable (fun x : BilateralField d => GNc i N x f)) := by
  choose GNc hGNc using fun i N (x : BilateralField d) =>
    (existsUnique_volumeResponseOperator (Sspace i)
      (Lane4.cutoffPositiveCoefficient model H x N (z i) (hr i))).exists
  refine ⟨GNc, hGNc, fun i N f => ?_⟩
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  apply aux_lem_endpoints_support_3_stronglyMeasurable_of_inner
  intro g
  have hsym : ∀ x (u v : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GNc i N x u) v = inner ℝ u (GNc i N x v) := by
    intro x u v
    rw [hGNc i N x u, hGNc i N x v, real_inner_comm]
    exact volumeResponse_pairing_symm _ _ v u
  have hfun : (fun x => inner ℝ g (GNc i N x f)) = fun x =>
      (inverseResponse (Sspace i) (Lane4.cutoffPositiveCoefficient model H x N (z i) (hr i))
          ((sobolevVolumeLoad (f + g)).comp (Sspace i).space.subtypeL) -
        inverseResponse (Sspace i) (Lane4.cutoffPositiveCoefficient model H x N (z i) (hr i))
          ((sobolevVolumeLoad (f - g)).comp (Sspace i).space.subtypeL)) / 4 := by
    funext x
    rw [aux_lem_endpoints_support_3_polarization (GNc i N x) (hsym x) f g, hGNc i N x (f + g),
      hGNc i N x (f - g), aux_lem_endpoints_support_3_pairing_eq_inverseResponse,
      aux_lem_endpoints_support_3_pairing_eq_inverseResponse]
  rw [hfun]
  exact ((aux_lem_endpoints_support_3_inverseResponse_measurable model H HI.1 N (z i) (hr i) (Sspace i) _).sub
    (aux_lem_endpoints_support_3_inverseResponse_measurable model H HI.1 N (z i) (hr i) (Sspace i) _)).div_const 4

def aux_lem_endpoints_support_3_endpoint_invariance_resample {d : ℕ} (S : Finset ℤ)
    (om1 om2 : BilateralField d) : BilateralField d :=
  fun j => if j ∈ S then om2 j else om1 j

def aux_lem_endpoints_support_3_endpoint_invariance_N0 (S : Finset ℤ) : ℕ :=
  (S.filter (fun j => j ≤ 0)).sup (fun j => (-j).toNat)

def aux_lem_endpoints_support_3_endpoint_invariance_L0 (S : Finset ℤ) : ℕ :=
  (S.filter (fun j => 0 < j)).sup (fun j => j.toNat)

theorem aux_lem_endpoints_support_3_endpoint_invariance_coe_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ContinuousMap.add_apply, ih]

section Resample
variable {d : ℕ} (S : Finset ℤ) (om1 om2 : BilateralField d)

noncomputable def aux_lem_endpoints_support_3_endpoint_invariance_Dneg : C(SpatialCoordinates d, ℝ) :=
  ∑ j ∈ Finset.range (aux_lem_endpoints_support_3_endpoint_invariance_N0 S + 1),
    (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2 (-(j : ℤ)) - om1 (-(j : ℤ)))

noncomputable def aux_lem_endpoints_support_3_endpoint_invariance_Dpos : C(SpatialCoordinates d, ℝ) :=
  infraredPartialSum (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2)
      (aux_lem_endpoints_support_3_endpoint_invariance_L0 S) -
    infraredPartialSum om1 (aux_lem_endpoints_support_3_endpoint_invariance_L0 S)

theorem aux_lem_endpoints_support_3_endpoint_invariance_resample_of_not_mem {j : ℤ} (hj : j ∉ S) :
    aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2 j = om1 j := by
  simp only [aux_lem_endpoints_support_3_endpoint_invariance_resample, if_neg hj]

theorem aux_lem_endpoints_support_3_endpoint_invariance_not_mem_of_gt_N0 {j : ℕ}
    (hj : aux_lem_endpoints_support_3_endpoint_invariance_N0 S < j) : (-(j : ℤ)) ∉ S := by
  unfold aux_lem_endpoints_support_3_endpoint_invariance_N0 at hj
  intro hmem
  have hmem' : (-(j : ℤ)) ∈ S.filter (fun k => k ≤ 0) := by
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    simp
  have hle : (fun k : ℤ => (-k).toNat) (-(j : ℤ)) ≤
      (S.filter (fun k => k ≤ 0)).sup (fun k => (-k).toNat) :=
    Finset.le_sup (f := fun k : ℤ => (-k).toNat) hmem'
  simp only [neg_neg, Int.toNat_natCast] at hle
  omega

theorem aux_lem_endpoints_support_3_endpoint_invariance_not_mem_of_gt_L0 {n : ℕ}
    (hn : aux_lem_endpoints_support_3_endpoint_invariance_L0 S < n) : ((n : ℤ)) ∉ S := by
  unfold aux_lem_endpoints_support_3_endpoint_invariance_L0 at hn
  intro hmem
  have hpos : (0 : ℤ) < (n : ℤ) := by
    have hn1 : 0 < n := by omega
    exact_mod_cast hn1
  have hmem' : (n : ℤ) ∈ S.filter (fun k => 0 < k) := Finset.mem_filter.mpr ⟨hmem, hpos⟩
  have hle : (fun k : ℤ => k.toNat) (n : ℤ) ≤
      (S.filter (fun k => 0 < k)).sup (fun k => k.toNat) :=
    Finset.le_sup (f := fun k : ℤ => k.toNat) hmem'
  simp only [Int.toNat_natCast] at hle
  omega

theorem aux_lem_endpoints_support_3_endpoint_invariance_cutoffSum_stable {N : ℕ}
    (hN : aux_lem_endpoints_support_3_endpoint_invariance_N0 S ≤ N) :
    (∑ j ∈ Finset.range (N + 1),
        (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2 (-(j : ℤ)) - om1 (-(j : ℤ)))) =
      aux_lem_endpoints_support_3_endpoint_invariance_Dneg S om1 om2 := by
  unfold aux_lem_endpoints_support_3_endpoint_invariance_Dneg
  have hNsucc : aux_lem_endpoints_support_3_endpoint_invariance_N0 S + 1 ≤ N + 1 := by omega
  refine (Finset.sum_subset (Finset.range_subset_range.mpr hNsucc) ?_).symm
  intro j _ hjnot
  rw [Finset.mem_range, not_lt] at hjnot
  have hjgt : aux_lem_endpoints_support_3_endpoint_invariance_N0 S < j := by omega
  rw [aux_lem_endpoints_support_3_endpoint_invariance_resample_of_not_mem S om1 om2
    (aux_lem_endpoints_support_3_endpoint_invariance_not_mem_of_gt_N0 S hjgt), sub_self]

theorem lem_endpoints_support_3 {L : ℕ}
    (hL : aux_lem_endpoints_support_3_endpoint_invariance_L0 S ≤ L) :
    infraredPartialSum (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) L -
        infraredPartialSum om1 L =
      aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2 := by
  unfold aux_lem_endpoints_support_3_endpoint_invariance_Dpos infraredPartialSum
  simp only [Int.ofNat_eq_natCast]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.sum_subset (Finset.range_subset_range.mpr hL) ?_).symm
  intro n _ hnot
  rw [Finset.mem_range, not_lt] at hnot
  have hngt : aux_lem_endpoints_support_3_endpoint_invariance_L0 S < n + 1 := by omega
  have heq := aux_lem_endpoints_support_3_endpoint_invariance_resample_of_not_mem S om1 om2
    (aux_lem_endpoints_support_3_endpoint_invariance_not_mem_of_gt_L0 S (n := n + 1) hngt)
  show aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2 ((n + 1 : ℕ) : ℤ) -
        ContinuousMap.const (SpatialCoordinates d)
          ((aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2 ((n + 1 : ℕ) : ℤ)) 0) -
      (om1 ((n + 1 : ℕ) : ℤ) -
        ContinuousMap.const (SpatialCoordinates d) ((om1 ((n + 1 : ℕ) : ℤ)) 0)) = 0
  rw [heq]
  simp

end Resample
end Paper
