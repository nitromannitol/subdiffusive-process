module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_limit_transfer
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_uniqueness
public import SubdiffusiveProcess.Sobolev.CountableSmoothSources
public import SubdiffusiveProcess.Sobolev.LimitFormUniqueness
public import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The dual energy of a positive multiple of the killed inverse. -/
theorem aux_thm_prop_env_limitFormEnergy_smul {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (c : ℝ) (hc : 0 < c) (u : DomainL2 Q) :
    limitFormEnergy (c • G) u = ((c⁻¹ : ℝ) : EReal) * limitFormEnergy G u := by
  unfold limitFormEnergy
  apply le_antisymm
  · apply iSup_le
    intro f
    have hreal : (2 * inner ℝ f u - inner ℝ f ((c • G) f) : ℝ)
        = c⁻¹ * (2 * inner ℝ (c • f) u - inner ℝ (c • f) (G (c • f))) := by
      simp only [smul_apply, map_smul, real_inner_smul_left,
        real_inner_smul_right]
      field_simp
    rw [hreal, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left
      (le_iSup (fun f => ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) (c • f))
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr (le_of_lt hc)))
  · have hEG : (⨆ g : DomainL2 Q, ((2 * inner ℝ g u - inner ℝ g (G g) : ℝ) : EReal))
        ≤ (↑c : EReal) * (⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f ((c • G) f) : ℝ) : EReal)) := by
      apply iSup_le
      intro g
      have hreal : (2 * inner ℝ g u - inner ℝ g (G g) : ℝ)
          = c * (2 * inner ℝ (c⁻¹ • g) u - inner ℝ (c⁻¹ • g) ((c • G) (c⁻¹ • g))) := by
        simp only [smul_apply, map_smul, real_inner_smul_left,
          real_inner_smul_right]
        field_simp
      rw [hreal, EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left
        (le_iSup (fun f => ((2 * inner ℝ f u - inner ℝ f ((c • G) f) : ℝ) : EReal)) (c⁻¹ • g))
        (EReal.coe_nonneg.mpr (le_of_lt hc))
    calc (↑c⁻¹ : EReal) * (⨆ g : DomainL2 Q, ((2 * inner ℝ g u - inner ℝ g (G g) : ℝ) : EReal))
        ≤ (↑c⁻¹ : EReal) * ((↑c : EReal) * (⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f ((c • G) f) : ℝ) : EReal))) :=
          mul_le_mul_of_nonneg_left hEG (EReal.coe_nonneg.mpr (inv_nonneg.mpr (le_of_lt hc)))
      _ = ⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f ((c • G) f) : ℝ) : EReal) := by
          rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ (ne_of_gt hc), EReal.coe_one, one_mul]

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Operator proportionality `GE = c • GF` gives domain equality and proportional dual energies. -/
theorem aux_thm_prop_env_prop_of_smul {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q) (c : ℝ) (hc : 0 < c) (h : GE = c • GF)
    (hsmul : ∀ (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q),
      limitFormEnergy (c • G) u = ((c⁻¹ : ℝ) : EReal) * limitFormEnergy G u) :
    limitFormDomain GE = limitFormDomain GF ∧
      ∀ u : DomainL2 Q, u ∈ limitFormDomain GE →
        (limitFormEnergy GF u).toReal = c * (limitFormEnergy GE u).toReal := by
  have key : ∀ a : EReal, 0 ≤ a → ((((c⁻¹ : ℝ)) : EReal) * a < ⊤ ↔ a < ⊤) := by
    intro a ha
    induction a using EReal.rec with
    | bot => exact absurd ha (by simp)
    | coe x => rw [← EReal.coe_mul]; simp only [EReal.coe_lt_top]
    | top =>
      rw [EReal.mul_top_of_pos (EReal.coe_pos.mpr (inv_pos.mpr hc))]
  constructor
  · ext u
    simp only [limitFormDomain, mem_ofPred_eq, h, hsmul]
    exact key _ (limitFormEnergy_nonneg GF u)
  · intro u hu
    simp only [limitFormDomain, mem_ofPred_eq] at hu
    rw [h, hsmul GF u] at hu
    have hGF : limitFormEnergy GF u < ⊤ :=
      (key _ (limitFormEnergy_nonneg GF u)).mp hu
    have hcoe : (((limitFormEnergy GF u).toReal : ℝ) : EReal) = limitFormEnergy GF u :=
      EReal.coe_toReal (ne_of_lt hGF)
        (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg GF u)))
    have hGE : limitFormEnergy GE u = (((c⁻¹ * (limitFormEnergy GF u).toReal : ℝ)) : EReal) := by
      rw [h, hsmul GF u]
      conv_lhs => rw [← hcoe]
      rw [← EReal.coe_mul]
    rw [hGE, EReal.toReal_coe, mul_inv_cancel_left₀ (ne_of_gt hc)]

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

/-- Quadratic-form order reverses the dual energies. -/
theorem aux_env_energy_le_of_inner_le {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G1 G2 : DomainL2 Q →L[ℝ] DomainL2 Q)
    (h : ∀ x, inner ℝ x (G1 x) ≤ inner ℝ x (G2 x)) (u : DomainL2 Q) :
    limitFormEnergy G2 u ≤ limitFormEnergy G1 u := by
  unfold limitFormEnergy
  refine iSup_mono fun f => ?_
  refine EReal.coe_le_coe_iff.mpr ?_
  linarith [h f]

end Part2

section Part3
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

/-- Order of dual energies gives the reversed order of the quadratic forms, for a symmetric nonnegative first operator. -/
theorem aux_env_inner_le_of_energy_le {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G1 G2 : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs1 : ∀ x y, inner ℝ x (G1 y) = inner ℝ y (G1 x))
    (hp1 : ∀ x, 0 ≤ inner ℝ x (G1 x))
    (h : ∀ u, limitFormEnergy G2 u ≤ limitFormEnergy G1 u) :
    ∀ x, inner ℝ x (G1 x) ≤ inner ℝ x (G2 x) := by
  intro x
  have hA : limitFormEnergy G1 (G1 x) = ((inner ℝ x (G1 x) : ℝ) : EReal) := by
    apply le_antisymm
    · apply iSup_le
      intro f
      apply EReal.coe_le_coe_iff.mpr
      have h := hp1 (f - x)
      simp only [map_sub, inner_sub_left, inner_sub_right] at h
      rw [hs1 x f] at h
      linarith only [h]
    · apply le_iSup_of_le x
      apply EReal.coe_le_coe_iff.mpr
      linarith only []
  have hB : ((2 * inner ℝ x (G1 x) - inner ℝ x (G2 x) : ℝ) : EReal) ≤
      limitFormEnergy G2 (G1 x) := by
    have h := le_iSup (fun f : DomainL2 Q =>
      ((2 * inner ℝ f (G1 x) - inner ℝ f (G2 f) : ℝ) : EReal)) x
    change ((2 * inner ℝ x (G1 x) - inner ℝ x (G2 x) : ℝ) : EReal) ≤
      limitFormEnergy G2 (G1 x) at h
    exact h
  have hC : limitFormEnergy G2 (G1 x) ≤ limitFormEnergy G1 (G1 x) := h (G1 x)
  have hD : ((2 * inner ℝ x (G1 x) - inner ℝ x (G2 x) : ℝ) : EReal) ≤
      ((inner ℝ x (G1 x) : ℝ) : EReal) :=
    le_trans hB (le_trans hC (le_of_eq hA))
  have hreal := EReal.coe_le_coe_iff.mp hD
  linarith only [hreal]

end Part3

section Part4
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

/-- Energy comparison with a domain equality gives the two quadratic-form bounds. -/
theorem aux_thm_prop_env_compare_to_order {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsE : ∀ x y, inner ℝ x (GE y) = inner ℝ y (GE x)) (hpE : ∀ x, 0 ≤ inner ℝ x (GE x))
    (hsF : ∀ x y, inner ℝ x (GF y) = inner ℝ y (GF x)) (hpF : ∀ x, 0 ≤ inner ℝ x (GF x))
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (h : limitFormDomain GE = limitFormDomain GF ∧ ∀ u ∈ limitFormDomain GE,
      m * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal ∧
        (limitFormEnergy GF u).toReal ≤ M * (limitFormEnergy GE u).toReal) :
    ∀ x, M⁻¹ * inner ℝ x (GE x) ≤ inner ℝ x (GF x) ∧
      inner ℝ x (GF x) ≤ m⁻¹ * inner ℝ x (GE x) := by
  have hfinite : ∀ u, u ∈ limitFormDomain GE →
      ((m:ℝ):EReal) * limitFormEnergy GE u ≤ limitFormEnergy GF u ∧
        limitFormEnergy GF u ≤ ((M:ℝ):EReal) * limitFormEnergy GE u := by
    intro u hu
    have hF : u ∈ limitFormDomain GF := h.1 ▸ hu
    have hEm : limitFormEnergy GE u ≠ ⊤ := ne_of_lt hu
    have hFm : limitFormEnergy GF u ≠ ⊤ := ne_of_lt hF
    have hEb : limitFormEnergy GE u ≠ ⊥ := by
      rw [← bot_lt_iff_ne_bot]
      exact lt_of_lt_of_le (EReal.bot_lt_coe 0) (limitFormEnergy_nonneg GE u)
    have hFb : limitFormEnergy GF u ≠ ⊥ := by
      rw [← bot_lt_iff_ne_bot]
      exact lt_of_lt_of_le (EReal.bot_lt_coe 0) (limitFormEnergy_nonneg GF u)
    constructor
    · rw [← EReal.coe_toReal hEm hEb, ← EReal.coe_toReal hFm hFb, ← EReal.coe_mul,
        EReal.coe_le_coe_iff]
      exact (h.2 u hu).1
    · rw [← EReal.coe_toReal hFm hFb, ← EReal.coe_toReal hEm hEb, ← EReal.coe_mul,
        EReal.coe_le_coe_iff]
      exact (h.2 u hu).2
  have htop : ∀ u, u ∉ limitFormDomain GE →
      limitFormEnergy GE u = ⊤ ∧ limitFormEnergy GF u = ⊤ := by
    intro u hu
    have hEtop : limitFormEnergy GE u = ⊤ := le_antisymm le_top (not_lt.mp hu)
    have hFtop : limitFormEnergy GF u = ⊤ := by
      rw [h.1] at hu
      exact le_antisymm le_top (not_lt.mp hu)
    exact ⟨hEtop, hFtop⟩
  have hlow : ∀ u, ((m:ℝ):EReal) * limitFormEnergy GE u ≤ limitFormEnergy GF u := by
    intro u
    by_cases hu : u ∈ limitFormDomain GE
    · exact (hfinite u hu).1
    · obtain ⟨hEtop, hFtop⟩ := htop u hu
      rw [hEtop, hFtop, EReal.mul_top_of_pos (EReal.coe_pos.mpr hm)]
  have hup : ∀ u, limitFormEnergy GF u ≤ ((M:ℝ):EReal) * limitFormEnergy GE u := by
    intro u
    by_cases hu : u ∈ limitFormDomain GE
    · exact (hfinite u hu).2
    · obtain ⟨hEtop, hFtop⟩ := htop u hu
      rw [hFtop, hEtop, EReal.mul_top_of_pos (EReal.coe_pos.mpr hM)]
  have hsym1 : ∀ a b, inner ℝ a ((M⁻¹ • GE) b) = inner ℝ b ((M⁻¹ • GE) a) := by
    intro a b
    simp only [smul_apply, real_inner_smul_right, hsE a b]
  have hpos1 : ∀ a, 0 ≤ inner ℝ a ((M⁻¹ • GE) a) := by
    intro a
    rw [smul_apply, real_inner_smul_right]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hM)) (hpE a)
  have henergy1 : ∀ u, limitFormEnergy GF u ≤ limitFormEnergy (M⁻¹ • GE) u := by
    intro u
    rw [aux_thm_prop_env_limitFormEnergy_smul GE M⁻¹ (inv_pos.mpr hM) u, inv_inv]
    exact hup u
  have hsym2 : ∀ a b, inner ℝ a (GF b) = inner ℝ b (GF a) := hsF
  have hpos2 : ∀ a, 0 ≤ inner ℝ a (GF a) := hpF
  have henergy2 : ∀ u, limitFormEnergy (m⁻¹ • GE) u ≤ limitFormEnergy GF u := by
    intro u
    rw [aux_thm_prop_env_limitFormEnergy_smul GE m⁻¹ (inv_pos.mpr hm) u, inv_inv]
    exact hlow u
  have h2 : ∀ x, inner ℝ x (GF x) ≤ inner ℝ x ((m⁻¹ • GE) x) :=
    aux_env_inner_le_of_energy_le (G1 := GF) (G2 := m⁻¹ • GE) hsym2 hpos2 henergy2
  have h1 : ∀ x, inner ℝ x ((M⁻¹ • GE) x) ≤ inner ℝ x (GF x) :=
    aux_env_inner_le_of_energy_le (G1 := M⁻¹ • GE) (G2 := GF) hsym1 hpos1 henergy1
  intro x
  have ha : M⁻¹ * inner ℝ x (GE x) ≤ inner ℝ x (GF x) := by
    have := h1 x
    rwa [smul_apply, real_inner_smul_right] at this
  have hb : inner ℝ x (GF x) ≤ m⁻¹ * inner ℝ x (GE x) := by
    have := h2 x
    rwa [smul_apply, real_inner_smul_right] at this
  exact ⟨ha, hb⟩

end Part4

section Part5
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

/-- The two quadratic-form bounds give the energy comparison with a domain equality. -/
theorem thm_prop_env_energy {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (h : ∀ x, M⁻¹ * inner ℝ x (GE x) ≤ inner ℝ x (GF x) ∧
      inner ℝ x (GF x) ≤ m⁻¹ * inner ℝ x (GE x)) :
    limitFormDomain GE = limitFormDomain GF ∧ ∀ u ∈ limitFormDomain GE,
      m * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal ∧
        (limitFormEnergy GF u).toReal ≤ M * (limitFormEnergy GE u).toReal := by
  have h1 : ∀ x, inner ℝ x (GF x) ≤ inner ℝ x ((m⁻¹ • GE) x) := by
    intro x
    rw [smul_apply, inner_smul_right]
    exact (h x).2
  have h2 : ∀ x, inner ℝ x ((M⁻¹ • GE) x) ≤ inner ℝ x (GF x) := by
    intro x
    rw [smul_apply, inner_smul_right]
    exact (h x).1
  have hmGE_le : ∀ u, limitFormEnergy (m⁻¹ • GE) u ≤ limitFormEnergy GF u :=
    fun u => aux_env_energy_le_of_inner_le GF (m⁻¹ • GE) h1 u
  have hEF_le : ∀ u, limitFormEnergy GF u ≤ limitFormEnergy (M⁻¹ • GE) u :=
    fun u => aux_env_energy_le_of_inner_le (M⁻¹ • GE) GF h2 u
  have hm' : 0 < m⁻¹ := inv_pos.mpr hm
  have hM' : 0 < M⁻¹ := inv_pos.mpr hM
  have hmsmul : ∀ u, limitFormEnergy (m⁻¹ • GE) u = ((m:ℝ):EReal) * limitFormEnergy GE u := by
    intro u
    rw [aux_thm_prop_env_limitFormEnergy_smul GE m⁻¹ hm' u, inv_inv]
  have hMsmul : ∀ u, limitFormEnergy (M⁻¹ • GE) u = ((M:ℝ):EReal) * limitFormEnergy GE u := by
    intro u
    rw [aux_thm_prop_env_limitFormEnergy_smul GE M⁻¹ hM' u, inv_inv]
  have hb1 : ∀ u, ((m:ℝ):EReal) * limitFormEnergy GE u ≤ limitFormEnergy GF u := by
    intro u; rw [← hmsmul u]; exact hmGE_le u
  have hb2 : ∀ u, limitFormEnergy GF u ≤ ((M:ℝ):EReal) * limitFormEnergy GE u := by
    intro u; rw [← hMsmul u]; exact hEF_le u
  have hbotE : ∀ u, limitFormEnergy GE u ≠ ⊥ := by
    intro u
    exact ne_of_gt ((EReal.bot_lt_coe 0).trans_le (limitFormEnergy_nonneg GE u))
  have hbotF : ∀ u, limitFormEnergy GF u ≠ ⊥ := by
    intro u
    exact ne_of_gt ((EReal.bot_lt_coe 0).trans_le (limitFormEnergy_nonneg GF u))
  have htop_of_lt : ∀ u, limitFormEnergy GE u < ⊤ →
      ((M:ℝ):EReal) * limitFormEnergy GE u < ⊤ := by
    intro u hu
    rw [← EReal.coe_toReal hu.ne (hbotE u), ← EReal.coe_mul]
    exact EReal.coe_lt_top _
  constructor
  · ext u
    simp only [limitFormDomain, mem_ofPred_eq]
    constructor
    · intro hu
      exact lt_of_le_of_lt (hb2 u) (htop_of_lt u hu)
    · intro hu
      by_contra hcon
      have hEt : limitFormEnergy GE u = ⊤ := le_antisymm le_top (le_of_not_gt hcon)
      have hmul : ((m:ℝ):EReal) * limitFormEnergy GE u = ⊤ := by
        rw [hEt, EReal.mul_top_of_pos (EReal.coe_pos.mpr hm)]
      exact hu.ne (le_antisymm le_top (hmul ▸ hb1 u))
  · intro u hu
    have hul : limitFormEnergy GE u < ⊤ := hu
    have hEFtop : limitFormEnergy GF u ≠ ⊤ := (lt_of_le_of_lt (hb2 u) (htop_of_lt u hul)).ne
    constructor
    · have hne : ((m:ℝ):EReal) * limitFormEnergy GE u ≠ ⊥ :=
        ne_of_gt ((EReal.bot_lt_coe 0).trans_le
          (EReal.mul_nonneg (EReal.coe_pos.mpr hm).le (limitFormEnergy_nonneg GE u)))
      have key := EReal.toReal_le_toReal (hb1 u) hne hEFtop
      rwa [EReal.toReal_mul, EReal.toReal_coe] at key
    · have hne : ((M:ℝ):EReal) * limitFormEnergy GE u ≠ ⊤ := (htop_of_lt u hul).ne
      have key := EReal.toReal_le_toReal (hb2 u) (hbotF u) hne
      rwa [EReal.toReal_mul, EReal.toReal_coe] at key

end Part5

section Part6
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

/-- Proportional dual energies on a common domain give proportional killed inverses. -/
theorem aux_thm_prop_env_op_eq_of_prop {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsE : ∀ x y, inner ℝ x (GE y) = inner ℝ y (GE x)) (hpE : ∀ x, 0 ≤ inner ℝ x (GE x))
    (hsF : ∀ x y, inner ℝ x (GF y) = inner ℝ y (GF x)) (hpF : ∀ x, 0 ≤ inner ℝ x (GF x))
    (c : ℝ) (hc : 0 < c) (hdom : limitFormDomain GE = limitFormDomain GF)
    (hprop : ∀ u ∈ limitFormDomain GE,
      (limitFormEnergy GF u).toReal = c * (limitFormEnergy GE u).toReal) :
    GE = c • GF := by
  have hsGc : ∀ x y : DomainL2 Q, inner ℝ x ((c • GF) y) = inner ℝ y ((c • GF) x) := by
    intro x y
    rw [smul_apply, smul_apply,
      real_inner_smul_right, real_inner_smul_right, hsF x y]
  have hpGc : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x ((c • GF) x) := by
    intro x
    rw [smul_apply, real_inner_smul_right]
    exact mul_nonneg hc.le (hpF x)
  have hcpos : (0 : EReal) < ((c⁻¹ : ℝ) : EReal) := by
    rw [EReal.coe_pos]
    exact inv_pos.mpr hc
  have key : ∀ x : EReal, 0 ≤ x → (((c⁻¹ : ℝ) : EReal) * x < ⊤ ↔ x < ⊤) := by
    intro x hx
    constructor
    · intro h
      by_contra hcon
      rw [not_lt] at hcon
      have htop : x = ⊤ := le_antisymm le_top hcon
      rw [htop, EReal.mul_top_of_pos hcpos] at h
      exact absurd h (lt_irrefl _)
    · intro h
      rw [lt_top_iff_ne_top, EReal.mul_ne_top]
      exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (le_of_lt hcpos),
        Or.inl (EReal.coe_ne_top _), Or.inr h.ne⟩
  have hdomc : limitFormDomain GE = limitFormDomain (c • GF) := by
    rw [hdom]
    ext u
    simp only [limitFormDomain, mem_ofPred_eq,
      aux_thm_prop_env_limitFormEnergy_smul GF c hc u]
    exact (key _ (limitFormEnergy_nonneg GF u)).symm
  refine eq_of_limitFormEnergy_eq GE (c • GF) hsE hpE hsGc hpGc hdomc ?_
  intro u hu
  have hGE_fin : limitFormEnergy GE u < ⊤ := hu
  have hGF_mem : u ∈ limitFormDomain GF := hdom ▸ hu
  have hGF_fin : limitFormEnergy GF u < ⊤ := hGF_mem
  have hGE_top : limitFormEnergy GE u ≠ ⊤ := hGE_fin.ne
  have hGF_top : limitFormEnergy GF u ≠ ⊤ := hGF_fin.ne
  have hGE_bot : limitFormEnergy GE u ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp : (0 : EReal) ≠ ⊥) (limitFormEnergy_nonneg GE u)
  have hGF_bot : limitFormEnergy GF u ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp : (0 : EReal) ≠ ⊥) (limitFormEnergy_nonneg GF u)
  rw [aux_thm_prop_env_limitFormEnergy_smul GF c hc u,
    ← EReal.coe_toReal hGE_top hGE_bot, ← EReal.coe_toReal hGF_top hGF_bot,
    ← EReal.coe_mul]
  congr 1
  rw [hprop u hu, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

end Part6

section Part7
open Filter MeasureTheory Set Topology

/-- The pairing `x ↦ ⟨x, G x⟩` of an a.e. limit of measurable operator-valued maps is a.e. measurable. -/
theorem aux_env_inner_aemeasurable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {P : Measure Ω}
    (T : ℕ → Ω → E →L[ℝ] E) (G : Ω → E →L[ℝ] E) (x : E)
    (hT : ∀ n, Measurable (fun ω => inner ℝ x (T n ω x)))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => T n ω) atTop (𝓝 (G ω))) :
    AEMeasurable (fun ω => inner ℝ x (G ω x)) P := by
  have hΦ : Continuous (fun A : E →L[ℝ] E => inner ℝ x (A x)) :=
    continuous_const.inner ((ContinuousLinearMap.apply ℝ E x).continuous)
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun n => inner ℝ x (T n ω x)) atTop (𝓝 (inner ℝ x (G ω x))) := by
    filter_upwards [hlim] with ω hω
    exact (hΦ.tendsto (G ω)).comp hω
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hT n).aemeasurable) hlim'

end Part7

end SubdiffusiveProcess.Paper
end
