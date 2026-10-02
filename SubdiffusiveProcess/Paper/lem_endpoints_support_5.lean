import Mathlib.Tactic
import SubdiffusiveProcess.Paper.lem_endpoints_support_2
import SubdiffusiveProcess.Paper.lem_endpoints_support_3
import SubdiffusiveProcess.Paper.lem_endpoints_support_4

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

theorem aux_lem_endpoints_support_5_nonzero_seq {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω)
    (hsym : ∀ i (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y))
    (hpos : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))), 0 ≤ inner ℝ x (GE i omega x))
    (hnz : aux_lem_endpoints_nonzero z r hr GE omega) :
    ∃ i k : ℕ,
      0 < inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i omega (aux_lem_endpoints_support_4_seq z r hr i k)) := by
  obtain ⟨i, u, hu, hpos_u⟩ := hnz
  have hne : GE i omega ≠ 0 := by
    intro h0
    rw [h0] at hpos_u
    have hu' : limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i))) u < (⊤ : EReal) := by
      rw [← h0]
      exact hu
    have hterm : ∀ t : ℝ,
        ((2 * t * ‖u‖ ^ 2 : ℝ) : EReal) ≤
          limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i))) u := by
      intro t
      unfold limitFormEnergy
      have hle : ((2 * t * ‖u‖ ^ 2 : ℝ) : EReal) ≤
          ((2 * inner ℝ (t • u) u -
            inner ℝ (t • u) ((0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (r i) (hr i))) (t • u)) : ℝ) : EReal) := by
        apply EReal.coe_le_coe_iff.mpr
        simp only [ContinuousLinearMap.zero_apply, inner_zero_right, sub_zero,
          real_inner_smul_left, real_inner_self_eq_norm_sq]
        nlinarith
      exact le_trans hle (le_iSup (fun f : DomainL2 (centeredCube (z i) (r i) (hr i)) =>
        ((2 * inner ℝ f u - inner ℝ f ((0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i))) f) : ℝ) : EReal)) (t • u))
    have hEcoe : limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i))) u =
        ((limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i))) u).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hu')
        (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero
          (limitFormEnergy_nonneg (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i))) u)))).symm
    have hbound : ∀ t : ℝ, 2 * t * ‖u‖ ^ 2 ≤
        (limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i))) u).toReal := by
      intro t
      have h := hterm t
      rw [hEcoe] at h
      exact EReal.coe_le_coe_iff.mp h
    by_cases hu0 : u = 0
    · rw [hu0] at hpos_u
      have hzero : limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
          (0 : DomainL2 (centeredCube (z i) (r i) (hr i))) = 0 := by
        simp [limitFormEnergy]
      rw [hzero] at hpos_u
      norm_num at hpos_u
    · have hnorm : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
      have hn' : ‖u‖ ^ 2 ≠ 0 := ne_of_gt hnorm
      have ht := hbound (((limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i))) u).toReal + 1) / ‖u‖ ^ 2)
      have hmul : 2 * (((limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i))) u).toReal + 1) / ‖u‖ ^ 2) * ‖u‖ ^ 2 =
          2 * ((limitFormEnergy (0 : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i))) u).toReal + 1) := by
        rw [mul_assoc, div_mul_cancel₀ _ hn']
      rw [hmul] at ht
      linarith
  obtain ⟨f, hf⟩ := aux_lem_endpoints_support_3_response_of_ne_zero (GE i omega) (hsym i) (hpos i) hne
  have hopen : IsOpen {x : DomainL2 (centeredCube (z i) (r i) (hr i)) |
      0 < inner ℝ x (GE i omega x)} :=
    isOpen_lt continuous_const (continuous_id.inner (GE i omega).continuous)
  obtain ⟨k, hk⟩ := (aux_lem_endpoints_support_4_seq_dense z r hr i).exists_mem_open hopen ⟨f, hf⟩
  exact ⟨i, k, hk⟩

theorem aux_lem_endpoints_support_5_goodSeq_lower_mem_iff {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (hC0 : 1 ≤ C0) (omega : Ω) (hgood : aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 omega)
    (a : ℝ) (ha : 0 < a) :
    a ∈ aux_lem_endpoints_lowerSet z r hr GE GF omega ↔
      aux_lem_endpoints_support_4_upperTest z r hr GF GE a⁻¹ omega := by
  have hsp : ∀ i : ℕ,
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GE i omega x))) ∧
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GF i omega x))) :=
    fun i => aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF C0 omega hgood i
  have hC0' : (0 : ℝ) ≤ C0 := le_trans zero_le_one hC0
  have hUF : ∀ i : ℕ, ∀ u ∈ limitFormDomain (GE i omega),
      limitFormEnergy (GF i omega) u ≤ ↑(C0 * (limitFormEnergy (GE i omega) u).toReal) :=
    (aux_lem_endpoints_support_4_upperTest_iff z r hr GE GF omega (fun i => (hsp i).1.1)
      (fun i => (hsp i).1.2) C0 hC0').mp hgood.2.2.1
  have hUE : ∀ i : ℕ, ∀ u ∈ limitFormDomain (GF i omega),
      limitFormEnergy (GE i omega) u ≤ ↑(C0 * (limitFormEnergy (GF i omega) u).toReal) :=
    (aux_lem_endpoints_support_4_upperTest_iff z r hr GF GE omega (fun i => (hsp i).2.1)
      (fun i => (hsp i).2.2) C0 hC0').mp hgood.2.2.2.1
  rw [aux_lem_endpoints_support_4_upperTest_iff z r hr GF GE omega (fun i => (hsp i).2.1)
    (fun i => (hsp i).2.2) a⁻¹ (inv_nonneg.mpr ha.le)]
  unfold aux_lem_endpoints_lowerSet
  simp only [mem_setOf_eq]
  constructor
  · intro hlow i u huF
    have huE : u ∈ limitFormDomain (GE i omega) := by
      change limitFormEnergy (GE i omega) u < ⊤
      exact lt_of_le_of_lt (hUE i u huF) (EReal.coe_lt_top _)
    have htop : limitFormEnergy (GE i omega) u ≠ ⊤ :=
      ne_of_lt (show limitFormEnergy (GE i omega) u < ⊤ by
        change u ∈ limitFormDomain (GE i omega)
        exact huE)
    have hbot : limitFormEnergy (GE i omega) u ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg (GE i omega) u))
    rw [← EReal.coe_toReal htop hbot]
    exact EReal.coe_le_coe_iff.mpr ((le_inv_mul_iff₀ ha).mpr (hlow i u huE))
  · intro hUT i u huE
    have huF : u ∈ limitFormDomain (GF i omega) := by
      change limitFormEnergy (GF i omega) u < ⊤
      exact lt_of_le_of_lt (hUF i u huE) (EReal.coe_lt_top _)
    have htop : limitFormEnergy (GE i omega) u ≠ ⊤ :=
      ne_of_lt (show limitFormEnergy (GE i omega) u < ⊤ by
        change u ∈ limitFormDomain (GE i omega)
        exact huE)
    have hbot : limitFormEnergy (GE i omega) u ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg (GE i omega) u))
    have h1 := hUT i u huF
    rw [← EReal.coe_toReal htop hbot] at h1
    exact (le_inv_mul_iff₀ ha).mp (EReal.coe_le_coe_iff.mp h1)

theorem aux_lem_endpoints_support_5_goodSeq_upper_mem_iff {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (hC0 : 1 ≤ C0) (omega : Ω) (hgood : aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 omega)
    (a : ℝ) (ha : 0 ≤ a) :
    a ∈ aux_lem_endpoints_upperSet z r hr GE GF omega ↔
      aux_lem_endpoints_support_4_upperTest z r hr GE GF a omega := by
  have hsp := aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF C0 omega hgood
  rw [aux_lem_endpoints_support_4_upperTest_iff z r hr GE GF omega (fun i => (hsp i).1.1)
    (fun i => (hsp i).1.2) a ha]
  constructor
  · intro hmem i u hu
    have hF : limitFormEnergy (GF i omega) u ≤
        ((C0 * (limitFormEnergy (GE i omega) u).toReal : ℝ) : EReal) :=
      (aux_lem_endpoints_support_4_upperTest_iff z r hr GE GF omega (fun i => (hsp i).1.1)
        (fun i => (hsp i).1.2) C0 (le_trans zero_le_one hC0)).mp hgood.2.2.1 i u hu
    have hFbot : limitFormEnergy (GF i omega) u ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg (GF i omega) u))
    have hFtop : limitFormEnergy (GF i omega) u ≠ ⊤ :=
      ne_top_of_le_ne_top
        (EReal.coe_ne_top (C0 * (limitFormEnergy (GE i omega) u).toReal)) hF
    calc limitFormEnergy (GF i omega) u
        = ((limitFormEnergy (GF i omega) u).toReal : EReal) :=
          (EReal.coe_toReal hFtop hFbot).symm
      _ ≤ ((a * (limitFormEnergy (GE i omega) u).toReal : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (hmem i u hu)
  · intro htest i u hu
    have hFbot : limitFormEnergy (GF i omega) u ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg (GF i omega) u))
    have h := EReal.toReal_le_toReal (htest i u hu) hFbot
      (EReal.coe_ne_top (a * (limitFormEnergy (GE i omega) u).toReal))
    rw [EReal.toReal_coe] at h
    exact h

theorem aux_lem_endpoints_support_5_lowerSet_nonpos_mem {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) (a : ℝ) (ha : a ≤ 0) :
    a ∈ aux_lem_endpoints_lowerSet z r hr GE GF omega := by
  intro i u _
  exact le_trans (mul_nonpos_of_nonpos_of_nonneg ha
    (EReal.toReal_nonneg (limitFormEnergy_nonneg _ _)))
    (EReal.toReal_nonneg (limitFormEnergy_nonneg _ _))

theorem aux_lem_endpoints_support_5_goodSeq_upper_nonneg {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (omega : Ω) (hgood : aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 omega)
    (a : ℝ) (ha : a ∈ aux_lem_endpoints_upperSet z r hr GE GF omega) : 0 ≤ a := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i, k, hk⟩ := hgood.2.2.2.2
  set s := aux_lem_endpoints_support_4_seq z r hr i k with hs
  have hsym := (aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF C0 omega hgood i).1.1
  have hpos := (aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF C0 omega hgood i).1.2
  have hen := aux_lem_endpoints_support_3_energy_range (GE i omega) hsym hpos s
  have hu : GE i omega s ∈ limitFormDomain (GE i omega) := by
    change limitFormEnergy (GE i omega) (GE i omega s) < ⊤
    rw [hen]
    exact EReal.coe_lt_top _
  have hle := ha i (GE i omega s) hu
  have henr : (limitFormEnergy (GE i omega) (GE i omega s)).toReal =
      inner ℝ s (GE i omega s) := by
    rw [hen, EReal.toReal_coe]
  have hFnn : 0 ≤ (limitFormEnergy (GF i omega) (GE i omega s)).toReal :=
    EReal.toReal_nonneg (limitFormEnergy_nonneg (GF i omega) (GE i omega s))
  rw [henr] at hle
  have hmul : a * inner ℝ s (GE i omega s) < 0 := mul_neg_of_neg_of_pos hcon hk
  linarith

theorem aux_lem_endpoints_support_5_goodSeq_lower_le {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (hC0 : 1 ≤ C0) (omega : Ω) (hgood : aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 omega)
    (a : ℝ) (ha : a ∈ aux_lem_endpoints_lowerSet z r hr GE GF omega) : a ≤ C0 := by
  have htest : aux_lem_endpoints_support_4_upperTest z r hr GE GF C0 omega := hgood.2.2.1
  obtain ⟨i, k, hik⟩ := hgood.2.2.2.2
  set s : DomainL2 (centeredCube (z i) (r i) (hr i)) := aux_lem_endpoints_support_4_seq z r hr i k
  have hsym : ∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
      inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y) :=
    (aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF C0 omega hgood i).1.1
  have hpos : ∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
      0 ≤ inner ℝ x (GE i omega x) :=
    (aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF C0 omega hgood i).1.2
  have he : limitFormEnergy (GE i omega) (GE i omega s) =
      ((inner ℝ s (GE i omega s) : ℝ) : EReal) :=
    aux_lem_endpoints_support_3_energy_range (GE i omega) hsym hpos s
  have hE_toReal : (limitFormEnergy (GE i omega) (GE i omega s)).toReal =
      inner ℝ s (GE i omega s) := by
    rw [he, EReal.toReal_coe]
  have hu : GE i omega s ∈ limitFormDomain (GE i omega) := by
    change limitFormEnergy (GE i omega) (GE i omega s) < ⊤
    rw [he]
    exact EReal.coe_lt_top _
  have hlow := ha i (GE i omega s) hu
  have hlow' : a * inner ℝ s (GE i omega s) ≤
      (limitFormEnergy (GF i omega) (GE i omega s)).toReal := by
    rw [hE_toReal] at hlow
    exact hlow
  have hC0nn : 0 ≤ C0 := le_trans zero_le_one hC0
  have hup := (aux_lem_endpoints_support_4_upperTest_iff z r hr GE GF omega
    (fun j => (aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF C0 omega hgood j).1.1)
    (fun j => (aux_lem_endpoints_support_4_goodSeq_symm_pos z r hr GE GF C0 omega hgood j).1.2)
    C0 hC0nn).mp htest
  have hFle : limitFormEnergy (GF i omega) (GE i omega s) ≤
      ((C0 * inner ℝ s (GE i omega s) : ℝ) : EReal) := by
    have h := hup i (GE i omega s) hu
    rw [hE_toReal] at h
    exact h
  have hFnn : 0 ≤ limitFormEnergy (GF i omega) (GE i omega s) :=
    limitFormEnergy_nonneg _ _
  have hFne : limitFormEnergy (GF i omega) (GE i omega s) ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hFnn)
  have hFub : (limitFormEnergy (GF i omega) (GE i omega s)).toReal ≤
      C0 * inner ℝ s (GE i omega s) := by
    have h := EReal.toReal_le_toReal hFle hFne
      (ne_of_lt (EReal.coe_lt_top (C0 * inner ℝ s (GE i omega s))))
    rw [EReal.toReal_coe] at h
    exact h
  exact le_of_mul_le_mul_right (le_trans hlow' hFub) hik

theorem aux_lem_endpoints_support_5_lowerSet_down {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) (a : ℝ) (ha : a ∈ aux_lem_endpoints_lowerSet z r hr GE GF omega) (b : ℝ) (hb : b ≤ a) :
    b ∈ aux_lem_endpoints_lowerSet z r hr GE GF omega := by
  intro i u hu
  exact le_trans (mul_le_mul_of_nonneg_right hb
    (EReal.toReal_nonneg (limitFormEnergy_nonneg _ _))) (ha i u hu)

theorem aux_lem_endpoints_support_5_upperSet_up {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) (a : ℝ) (ha : a ∈ aux_lem_endpoints_upperSet z r hr GE GF omega) (b : ℝ) (hb : a ≤ b) :
    b ∈ aux_lem_endpoints_upperSet z r hr GE GF omega := by
  intro i u hu
  exact le_trans (ha i u hu) (mul_le_mul_of_nonneg_right hb
    (EReal.toReal_nonneg (limitFormEnergy_nonneg _ _)))

theorem aux_lem_endpoints_support_5_upperTest_measurableSet {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {X : Type} [MeasurableSpace X]
    (GE GF : (i : ℕ) → X →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hE : ∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))), StronglyMeasurable (fun x => GE i x f))
    (hF : ∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))), StronglyMeasurable (fun x => GF i x f))
    (a : ℝ) : MeasurableSet {x | aux_lem_endpoints_support_4_upperTest z r hr GE GF a x} := by
  have hmE : ∀ i (v w : DomainL2 (centeredCube (z i) (r i) (hr i))),
      Measurable (fun x => inner ℝ v (GE i x w)) := fun i v w =>
    (stronglyMeasurable_const.inner (hE i w)).measurable
  have hmF : ∀ i (v w : DomainL2 (centeredCube (z i) (r i) (hr i))),
      Measurable (fun x => inner ℝ v (GF i x w)) := fun i v w =>
    (stronglyMeasurable_const.inner (hF i w)).measurable
  unfold aux_lem_endpoints_support_4_upperTest
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => MeasurableSet.iInter fun l =>
    measurableSet_le ((measurable_const.mul (hmE i _ _)).sub (hmF i _ _))
      (measurable_const.mul (hmE i _ _))

theorem aux_lem_endpoints_support_5_goodSeq_measurableSet {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {X : Type} [MeasurableSpace X]
    (GE GF : (i : ℕ) → X →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hE : ∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))), StronglyMeasurable (fun x => GE i x f))
    (hF : ∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))), StronglyMeasurable (fun x => GF i x f))
    (C0 : ℝ) : MeasurableSet {x | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} := by
  have hmE : ∀ i (v w : DomainL2 (centeredCube (z i) (r i) (hr i))),
      Measurable (fun x => inner ℝ v (GE i x w)) := fun i v w =>
    (stronglyMeasurable_const.inner (hE i w)).measurable
  have hmF : ∀ i (v w : DomainL2 (centeredCube (z i) (r i) (hr i))),
      Measurable (fun x => inner ℝ v (GF i x w)) := fun i v w =>
    (stronglyMeasurable_const.inner (hF i w)).measurable
  have hmE' : ∀ i (v w : DomainL2 (centeredCube (z i) (r i) (hr i))),
      Measurable (fun x => inner ℝ (GE i x w) v) := fun i v w =>
    ((hE i w).inner stronglyMeasurable_const).measurable
  have hmF' : ∀ i (v w : DomainL2 (centeredCube (z i) (r i) (hr i))),
      Measurable (fun x => inner ℝ (GF i x w) v) := fun i v w =>
    ((hF i w).inner stronglyMeasurable_const).measurable
  have h1 : MeasurableSet {x | ∀ i k l : ℕ,
      inner ℝ (GE i x (aux_lem_endpoints_support_4_seq z r hr i k)) (aux_lem_endpoints_support_4_seq z r hr i l) =
          inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i x (aux_lem_endpoints_support_4_seq z r hr i l)) ∧
        inner ℝ (GF i x (aux_lem_endpoints_support_4_seq z r hr i k)) (aux_lem_endpoints_support_4_seq z r hr i l) =
          inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GF i x (aux_lem_endpoints_support_4_seq z r hr i l))} := by
    simp only [Set.setOf_forall, Set.setOf_and]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => MeasurableSet.iInter fun l =>
      (measurableSet_eq_fun (hmE' i _ _) (hmE i _ _)).inter
        (measurableSet_eq_fun (hmF' i _ _) (hmF i _ _))
  have h2 : MeasurableSet {x | ∀ i k : ℕ,
      0 ≤ inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i x (aux_lem_endpoints_support_4_seq z r hr i k)) ∧
        0 ≤ inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GF i x (aux_lem_endpoints_support_4_seq z r hr i k))} := by
    simp only [Set.setOf_forall, Set.setOf_and]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      (measurableSet_le measurable_const (hmE i _ _)).inter
        (measurableSet_le measurable_const (hmF i _ _))
  have h5 : MeasurableSet {x | ∃ i k : ℕ,
      0 < inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i x (aux_lem_endpoints_support_4_seq z r hr i k))} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun k =>
      measurableSet_lt measurable_const (hmE i _ _)
  have h3 := aux_lem_endpoints_support_5_upperTest_measurableSet z r hr GE GF hE hF C0
  have h4 := aux_lem_endpoints_support_5_upperTest_measurableSet z r hr GF GE hF hE C0
  have hEq : {x | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} =
      {x | ∀ i k l : ℕ,
        inner ℝ (GE i x (aux_lem_endpoints_support_4_seq z r hr i k)) (aux_lem_endpoints_support_4_seq z r hr i l) =
            inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i x (aux_lem_endpoints_support_4_seq z r hr i l)) ∧
          inner ℝ (GF i x (aux_lem_endpoints_support_4_seq z r hr i k)) (aux_lem_endpoints_support_4_seq z r hr i l) =
            inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GF i x (aux_lem_endpoints_support_4_seq z r hr i l))} ∩
      ({x | ∀ i k : ℕ,
        0 ≤ inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i x (aux_lem_endpoints_support_4_seq z r hr i k)) ∧
          0 ≤ inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GF i x (aux_lem_endpoints_support_4_seq z r hr i k))} ∩
      ({x | aux_lem_endpoints_support_4_upperTest z r hr GE GF C0 x} ∩
      ({x | aux_lem_endpoints_support_4_upperTest z r hr GF GE C0 x} ∩
      {x | ∃ i k : ℕ,
        0 < inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i x (aux_lem_endpoints_support_4_seq z r hr i k))}))) := by
    ext x
    rfl
  rw [hEq]
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

theorem aux_lem_endpoints_support_5_ct_lower_regular {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {X : Type} [MeasurableSpace X] (μ : Measure X)
    (GE GF : (i : ℕ) → X →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hE : ∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
      StronglyMeasurable (fun x => GE i x f))
    (hF : ∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
      StronglyMeasurable (fun x => GF i x f))
    (C0 : ℝ) (hC0 : 1 ≤ C0) (hgood : ∀ᵐ x ∂μ, aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x) :
    AEMeasurable (fun x => sSup (aux_lem_endpoints_lowerSet z r hr GE GF x)) μ ∧
      ∀ᵐ x ∂μ, |sSup (aux_lem_endpoints_lowerSet z r hr GE GF x)| ≤ C0 := by
  have hT : MeasurableSet {x | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} :=
    aux_lem_endpoints_support_5_goodSeq_measurableSet z r hr GE GF hE hF C0
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hmem : ∀ x, aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x →
      C0⁻¹ ∈ aux_lem_endpoints_lowerSet z r hr GE GF x := by
    intro x hx
    rw [aux_lem_endpoints_support_5_goodSeq_lower_mem_iff z r hr GE GF C0 hC0 x hx C0⁻¹ (inv_pos.mpr hC0pos)]
    simpa [inv_inv] using hx.2.2.2.1
  have hbdd : ∀ x, aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x →
      BddAbove (aux_lem_endpoints_lowerSet z r hr GE GF x) := by
    intro x hx
    exact ⟨C0, fun a ha => aux_lem_endpoints_support_5_goodSeq_lower_le z r hr GE GF C0 hC0 x hx a ha⟩
  refine ⟨?_, ?_⟩
  · refine aux_lem_endpoints_support_4_sSup_aemeasurable μ (fun x => aux_lem_endpoints_lowerSet z r hr GE GF x)
      {x | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} hT hgood ?_ ?_ ?_ ?_
    · intro x _ a ha b hb
      exact aux_lem_endpoints_support_5_lowerSet_down z r hr GE GF x a ha b hb
    · intro x hx
      exact ⟨C0⁻¹, hmem x hx⟩
    · intro x hx
      exact hbdd x hx
    · intro q
      by_cases hq0 : (q : ℝ) ≤ 0
      · have hset : {x | x ∈ {x | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} ∧
            (q : ℝ) ∈ aux_lem_endpoints_lowerSet z r hr GE GF x} =
            {x | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} := by
          ext x
          exact ⟨fun hx => hx.1, fun hx =>
            ⟨hx, aux_lem_endpoints_support_5_lowerSet_nonpos_mem z r hr GE GF x (q : ℝ) hq0⟩⟩
        rw [hset]
        exact hT
      · have hqpos : 0 < (q : ℝ) := not_le.mp hq0
        have hset : {x | x ∈ {x | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} ∧
            (q : ℝ) ∈ aux_lem_endpoints_lowerSet z r hr GE GF x} =
            {x | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} ∩
              {x | aux_lem_endpoints_support_4_upperTest z r hr GF GE (q : ℝ)⁻¹ x} := by
          ext x
          constructor
          · intro hx
            exact ⟨hx.1, (aux_lem_endpoints_support_5_goodSeq_lower_mem_iff z r hr GE GF C0 hC0 x hx.1
              (q : ℝ) hqpos).mp hx.2⟩
          · intro hx
            exact ⟨hx.1, (aux_lem_endpoints_support_5_goodSeq_lower_mem_iff z r hr GE GF C0 hC0 x hx.1
              (q : ℝ) hqpos).mpr hx.2⟩
        rw [hset]
        exact hT.inter (aux_lem_endpoints_support_5_upperTest_measurableSet z r hr GF GE hF hE ((q : ℝ)⁻¹))
  · filter_upwards [hgood] with x hx
    have h1 : C0⁻¹ ≤ sSup (aux_lem_endpoints_lowerSet z r hr GE GF x) :=
      le_csSup (hbdd x hx) (hmem x hx)
    have h2 : sSup (aux_lem_endpoints_lowerSet z r hr GE GF x) ≤ C0 :=
      csSup_le ⟨C0⁻¹, hmem x hx⟩
        (fun b hb => aux_lem_endpoints_support_5_goodSeq_lower_le z r hr GE GF C0 hC0 x hx b hb)
    rw [abs_le]
    refine ⟨?_, h2⟩
    have h3 : 0 < C0⁻¹ := inv_pos.mpr hC0pos
    linarith

theorem aux_lem_endpoints_support_5_ct_upper_regular {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {X : Type} [MeasurableSpace X] (μ : Measure X)
    (GE GF : (i : ℕ) → X →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hE : ∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
      StronglyMeasurable (fun x => GE i x f))
    (hF : ∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
      StronglyMeasurable (fun x => GF i x f))
    (C0 : ℝ) (hC0 : 1 ≤ C0) (hgood : ∀ᵐ x ∂μ, aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x) :
    AEMeasurable (fun x => sInf (aux_lem_endpoints_upperSet z r hr GE GF x)) μ ∧
      ∀ᵐ x ∂μ, |sInf (aux_lem_endpoints_upperSet z r hr GE GF x)| ≤ C0 := by
    have hT : MeasurableSet {x : X | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} :=
      aux_lem_endpoints_support_5_goodSeq_measurableSet z r hr GE GF hE hF C0
    have hC0nonneg : 0 ≤ C0 := le_trans zero_le_one hC0
    have hmem : ∀ x : X, aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x →
        C0 ∈ aux_lem_endpoints_upperSet z r hr GE GF x := fun x hx =>
      (aux_lem_endpoints_support_5_goodSeq_upper_mem_iff z r hr GE GF C0 hC0 x hx C0 hC0nonneg).mpr hx.2.2.1
    refine ⟨?_, ?_⟩
    · refine aux_lem_endpoints_support_4_sInf_aemeasurable μ
        (fun x => aux_lem_endpoints_upperSet z r hr GE GF x)
        {x : X | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} hT hgood ?_ ?_ ?_ ?_
      · intro x hx a ha b hb
        exact aux_lem_endpoints_support_5_upperSet_up z r hr GE GF x a ha b hb
      · intro x hx
        exact ⟨C0, hmem x hx⟩
      · intro x hx
        exact ⟨0, fun a ha => aux_lem_endpoints_support_5_goodSeq_upper_nonneg z r hr GE GF C0 x hx a ha⟩
      · intro q
        by_cases hq : (q : ℝ) < 0
        · have hempty : {x : X | x ∈ {y : X | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 y} ∧
              (q : ℝ) ∈ aux_lem_endpoints_upperSet z r hr GE GF x} = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro x hx
            exact absurd (aux_lem_endpoints_support_5_goodSeq_upper_nonneg z r hr GE GF C0 x hx.1 (q : ℝ) hx.2)
              (not_le.mpr hq)
          rw [hempty]
          exact MeasurableSet.empty
        · have hq0 : 0 ≤ (q : ℝ) := le_of_not_gt hq
          have hset : {x : X | x ∈ {y : X | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 y} ∧
                (q : ℝ) ∈ aux_lem_endpoints_upperSet z r hr GE GF x} =
              {x : X | aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 x} ∩
                {x : X | aux_lem_endpoints_support_4_upperTest z r hr GE GF (q : ℝ) x} := by
            ext x
            rw [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_setOf_eq]
            constructor
            · intro hx
              exact ⟨hx.1, (aux_lem_endpoints_support_5_goodSeq_upper_mem_iff z r hr GE GF C0 hC0 x hx.1
                (q : ℝ) hq0).mp hx.2⟩
            · intro hx
              exact ⟨hx.1, (aux_lem_endpoints_support_5_goodSeq_upper_mem_iff z r hr GE GF C0 hC0 x hx.1
                (q : ℝ) hq0).mpr hx.2⟩
          rw [hset]
          exact hT.inter (aux_lem_endpoints_support_5_upperTest_measurableSet z r hr GE GF hE hF (q : ℝ))
    · filter_upwards [hgood] with x hx
      have hne : (aux_lem_endpoints_upperSet z r hr GE GF x).Nonempty := ⟨C0, hmem x hx⟩
      have hbdd : BddBelow (aux_lem_endpoints_upperSet z r hr GE GF x) :=
        ⟨0, fun a ha => aux_lem_endpoints_support_5_goodSeq_upper_nonneg z r hr GE GF C0 x hx a ha⟩
      have hle : sInf (aux_lem_endpoints_upperSet z r hr GE GF x) ≤ C0 := csInf_le hbdd (hmem x hx)
      have hge : 0 ≤ sInf (aux_lem_endpoints_upperSet z r hr GE GF x) :=
        le_csInf hne fun a ha => aux_lem_endpoints_support_5_goodSeq_upper_nonneg z r hr GE GF C0 x hx a ha
      rw [abs_le]
      exact ⟨by linarith, hle⟩

theorem lem_endpoints_support_5 (d : ℕ)
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
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (GNc : (i : ℕ) → ℕ → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hGNc : ∀ i N x f, GNc i N x f =
      (responseSolution (Sspace i)
        (Lane4.cutoffPositiveCoefficient model H x N (z i) (hr i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
    (hGNcm : ∀ i N (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
      StronglyMeasurable (fun x : BilateralField d => GNc i N x f)) :
    ∃ GEc GFc : (i : ℕ) → BilateralField d →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)),
      in_joint_extracted_candidates d model H (BilateralField d)
        (chaosSampleLaw model).toMeasure (fun omega => omega) z r hr Sspace GNc GEc GFc NE NF ∧
      (∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
        StronglyMeasurable (fun x => GEc i x f)) ∧
      (∀ i (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
        StronglyMeasurable (fun x => GFc i x f)) ∧
      (∀ᵐ omega ∂P, ∀ i, GE i omega = GEc i (field omega) ∧ GF i omega = GFc i (field omega)) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨hP, hfield, hmap, hIR, hmono, hS, hGN, hconv⟩ := hJoint
  let A : Set (BilateralField d) := ⋂ i : ℕ,
    ({x : BilateralField d | CauchySeq (fun n => GNc i (NE n) x)} ∩
      {x : BilateralField d | CauchySeq (fun n => GNc i (NF n) x)})
  have hdist : ∀ i N M : ℕ,
      Measurable (fun x : BilateralField d => dist (GNc i N x) (GNc i M x)) := by
    intro i N M
    have hsm : ∀ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
        StronglyMeasurable (fun x : BilateralField d => (GNc i N x - GNc i M x) f) := by
      intro f
      have hsub := (hGNcm i N f).sub (hGNcm i M f)
      have hfun : (fun x : BilateralField d => (GNc i N x - GNc i M x) f) =
          (fun x : BilateralField d => GNc i N x f - GNc i M x f) :=
        funext fun x => ContinuousLinearMap.sub_apply _ _ f
      rw [hfun]
      exact hsub
    have h1 := aux_lem_endpoints_support_4_opNorm_measurable
      (fun x : BilateralField d => GNc i N x - GNc i M x) hsm
    simpa only [dist_eq_norm] using h1
  have hcE : ∀ i : ℕ,
      MeasurableSet {x : BilateralField d | CauchySeq (fun n => GNc i (NE n) x)} := fun i =>
    aux_lem_endpoints_support_4_cauchySeq_measurableSet (fun n => GNc i (NE n))
      (fun m n => hdist i (NE m) (NE n))
  have hcF : ∀ i : ℕ,
      MeasurableSet {x : BilateralField d | CauchySeq (fun n => GNc i (NF n) x)} := fun i =>
    aux_lem_endpoints_support_4_cauchySeq_measurableSet (fun n => GNc i (NF n))
      (fun m n => hdist i (NF m) (NF n))
  have hA : MeasurableSet A := MeasurableSet.iInter fun i => (hcE i).inter (hcF i)
  let GEc : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)) :=
    fun i x => A.indicator (fun y => limUnder atTop (fun n => GNc i (NE n) y)) x
  let GFc : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)) :=
    fun i x => A.indicator (fun y => limUnder atTop (fun n => GNc i (NF n) y)) x
  have hGN' : ∀ i N omega, GN i N omega = GNc i N (field omega) := fun i N omega =>
    ContinuousLinearMap.ext fun f => (hGN i N omega f).trans (hGNc i N (field omega) f).symm
  have hPA : ∀ᵐ omega ∂P, field omega ∈ A ∧
      (∀ i, GE i omega = GEc i (field omega) ∧ GF i omega = GFc i (field omega)) := by
    filter_upwards [hconv] with omega homega
    have hseqE : ∀ i, (fun n => GN i (NE n) omega) = fun n => GNc i (NE n) (field omega) :=
      fun i => funext fun n => hGN' i (NE n) omega
    have hseqF : ∀ i, (fun n => GN i (NF n) omega) = fun n => GNc i (NF n) (field omega) :=
      fun i => funext fun n => hGN' i (NF n) omega
    have hmemE : ∀ i, CauchySeq (fun n => GNc i (NE n) (field omega)) := fun i => by
      rw [← hseqE i]
      exact (homega i).1.cauchySeq
    have hmemF : ∀ i, CauchySeq (fun n => GNc i (NF n) (field omega)) := fun i => by
      rw [← hseqF i]
      exact (homega i).2.cauchySeq
    have hAomega : field omega ∈ A := mem_iInter.mpr fun i => ⟨hmemE i, hmemF i⟩
    refine ⟨hAomega, fun i => ⟨?_, ?_⟩⟩
    · have hlim : Tendsto (fun n => GNc i (NE n) (field omega)) atTop (𝓝 (GEc i (field omega))) :=
        aux_lem_endpoints_support_4_indicator_limit_tendsto (fun n => GNc i (NE n)) A (field omega) hAomega (hmemE i)
      have hlim' : Tendsto (fun n => GNc i (NE n) (field omega)) atTop (𝓝 (GE i omega)) := by
        rw [← hseqE i]
        exact (homega i).1
      exact tendsto_nhds_unique hlim' hlim
    · have hlim : Tendsto (fun n => GNc i (NF n) (field omega)) atTop (𝓝 (GFc i (field omega))) :=
        aux_lem_endpoints_support_4_indicator_limit_tendsto (fun n => GNc i (NF n)) A (field omega) hAomega (hmemF i)
      have hlim' : Tendsto (fun n => GNc i (NF n) (field omega)) atTop (𝓝 (GF i omega)) := by
        rw [← hseqF i]
        exact (homega i).2
      exact tendsto_nhds_unique hlim' hlim
  refine ⟨GEc, GFc, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, measurable_id, Measure.map_id, hIR, hmono, hS, hGNc, ?_⟩
    filter_upwards [aux_lem_endpoints_support_4_ae_mem_of_map P (chaosSampleLaw model).toMeasure field hfield hmap
      A hA (hPA.mono fun omega h => h.1)] with x hx i
    have hx' : CauchySeq (fun n => GNc i (NE n) x) ∧ CauchySeq (fun n => GNc i (NF n) x) :=
      mem_iInter.mp hx i
    exact ⟨aux_lem_endpoints_support_4_indicator_limit_tendsto (fun n => GNc i (NE n)) A x hx hx'.1,
      aux_lem_endpoints_support_4_indicator_limit_tendsto (fun n => GNc i (NF n)) A x hx hx'.2⟩
  · intro i f
    exact aux_lem_endpoints_support_4_limUnder_apply_stronglyMeasurable (fun n => GNc i (NE n))
      (fun n f => hGNcm i (NE n) f) A hA
      (fun x hx => cauchySeq_tendsto_of_complete (mem_iInter.mp hx i).1) f
  · intro i f
    exact aux_lem_endpoints_support_4_limUnder_apply_stronglyMeasurable (fun n => GNc i (NF n))
      (fun n f => hGNcm i (NF n) f) A hA
      (fun x hx => cauchySeq_tendsto_of_complete (mem_iInter.mp hx i).2) f
  · exact hPA.mono fun omega h => h.2

end Paper
