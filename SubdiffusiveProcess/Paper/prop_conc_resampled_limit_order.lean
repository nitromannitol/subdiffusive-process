module

public import SubdiffusiveProcess.Lane2.LimitForm
public import Mathlib.Tactic

@[expose] public section

/-! Legendre duality of limit forms.  For symmetric nonnegative bounded operators `GE, GF`, the form order
`m E ≤ F ≤ M E` of the limit forms `limitFormEnergy GE`, `limitFormEnergy GF` (with equal domains) is equivalent to the
reversed order `M⁻¹ ⟨f, GE f⟩ ≤ ⟨f, GF f⟩ ≤ m⁻¹ ⟨f, GE f⟩` of the quadratic forms of the operators.  The right side is a
closed condition, testable on a countable dense set. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace Paper
noncomputable section

section
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

theorem aux_prop_conc_resampled_limit_order_le_energy (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (f u : DomainL2 Q) :
    ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) ≤ limitFormEnergy G u :=
  le_iSup (fun f : DomainL2 Q => ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) f

theorem aux_prop_conc_resampled_limit_order_energy_le (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (u : DomainL2 Q) (c : ℝ) (h : ∀ f : DomainL2 Q, 2 * inner ℝ f u - inner ℝ f (G f) ≤ c) :
    limitFormEnergy G u ≤ (c : EReal) :=
  iSup_le fun f => EReal.coe_le_coe_iff.mpr (h f)

/-- The energy of the image of `f` is the quadratic form of `f`. -/
theorem aux_prop_conc_resampled_limit_order_energy_apply (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y)) (hp : ∀ x, 0 ≤ inner ℝ x (G x))
    (f : DomainL2 Q) : limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) := by
  apply le_antisymm
  · refine aux_prop_conc_resampled_limit_order_energy_le G (G f) _ fun h => ?_
    have h1 := hp (h - f)
    have hsym : inner ℝ f (G h) = inner ℝ h (G f) := by
      rw [← real_inner_comm f (G h)]; exact hs h f
    have h2 : inner ℝ (h - f) (G (h - f)) =
        inner ℝ h (G h) - 2 * inner ℝ h (G f) + inner ℝ f (G f) := by
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym]
      ring
    linarith [h1, h2]
  · have := aux_prop_conc_resampled_limit_order_le_energy G f (G f)
    have h : 2 * inner ℝ f (G f) - inner ℝ f (G f) = inner ℝ f (G f) := by ring
    rwa [h] at this

variable (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)

/-- The form order of the limit forms gives the reversed order of the quadratic forms of the operators. -/
theorem aux_prop_conc_resampled_limit_order_op_of_form
    (hEs : ∀ x y, inner ℝ (GE x) y = inner ℝ x (GE y)) (hEp : ∀ x, 0 ≤ inner ℝ x (GE x))
    (hFs : ∀ x y, inner ℝ (GF x) y = inner ℝ x (GF y)) (hFp : ∀ x, 0 ≤ inner ℝ x (GF x))
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hdom : limitFormDomain GE = limitFormDomain GF)
    (hord : ∀ u ∈ limitFormDomain GE, m * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal ∧
      (limitFormEnergy GF u).toReal ≤ M * (limitFormEnergy GE u).toReal) (f : DomainL2 Q) :
    inner ℝ f (GF f) ≤ m⁻¹ * inner ℝ f (GE f) ∧ M⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f) := by
  have hfin : ∀ (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q), u ∈ limitFormDomain G →
      limitFormEnergy G u = ((limitFormEnergy G u).toReal : EReal) := by
    intro G u hu
    have h0 := limitFormEnergy_nonneg G u
    have h1 : limitFormEnergy G u < ⊤ := hu
    exact (EReal.coe_toReal h1.ne (by intro hb; rw [hb] at h0; exact absurd h0 (by simp))).symm
  constructor
  · -- `q_F(f) ≤ m⁻¹ q_E(f)`, testing at `u = GF f`
    set u := GF f with hu
    have hEu : limitFormEnergy GF u = ((inner ℝ f (GF f) : ℝ) : EReal) :=
      aux_prop_conc_resampled_limit_order_energy_apply GF hFs hFp f
    have huF : u ∈ limitFormDomain GF := by
      show limitFormEnergy GF u < ⊤
      rw [hEu]; exact EReal.coe_lt_top _
    have huE : u ∈ limitFormDomain GE := hdom ▸ huF
    have hb := (hord u huE).1
    rw [hEu, EReal.toReal_coe] at hb
    have hla := aux_prop_conc_resampled_limit_order_le_energy GE (m⁻¹ • f) u
    rw [hfin GE u huE] at hla
    have hla' := EReal.coe_le_coe_iff.mp hla
    have e1 : inner ℝ (m⁻¹ • f) u = m⁻¹ * inner ℝ f (GF f) := by
      rw [real_inner_smul_left]
    have e2 : inner ℝ (m⁻¹ • f) (GE (m⁻¹ • f)) = m⁻¹ * m⁻¹ * inner ℝ f (GE f) := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    rw [e1, e2] at hla'
    have hmm : m * m⁻¹ = 1 := mul_inv_cancel₀ hm.ne'
    have key : 2 * inner ℝ f (GF f) - m⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f) := by
      have := mul_le_mul_of_nonneg_left hla' hm.le
      have hL : m * (2 * (m⁻¹ * inner ℝ f (GF f)) - m⁻¹ * m⁻¹ * inner ℝ f (GE f)) =
          2 * inner ℝ f (GF f) - m⁻¹ * inner ℝ f (GE f) := by field_simp
      linarith [this, hb, hL]
    have : inner ℝ f (GF f) ≤ m⁻¹ * inner ℝ f (GE f) := by linarith
    exact this
  · -- `M⁻¹ q_E(f) ≤ q_F(f)`, testing at `u = GE f`
    set u := GE f with hu
    have hEu : limitFormEnergy GE u = ((inner ℝ f (GE f) : ℝ) : EReal) :=
      aux_prop_conc_resampled_limit_order_energy_apply GE hEs hEp f
    have huE : u ∈ limitFormDomain GE := by
      show limitFormEnergy GE u < ⊤
      rw [hEu]; exact EReal.coe_lt_top _
    have huF : u ∈ limitFormDomain GF := hdom ▸ huE
    have hb := (hord u huE).2
    rw [hEu, EReal.toReal_coe] at hb
    have hla := aux_prop_conc_resampled_limit_order_le_energy GF (M • f) u
    rw [hfin GF u huF] at hla
    have hla' := EReal.coe_le_coe_iff.mp hla
    have e1 : inner ℝ (M • f) u = M * inner ℝ f (GE f) := by
      rw [real_inner_smul_left]
    have e2 : inner ℝ (M • f) (GF (M • f)) = M * M * inner ℝ f (GF f) := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    rw [e1, e2] at hla'
    have hmm : M * M⁻¹ = 1 := mul_inv_cancel₀ hM.ne'
    have key : M * inner ℝ f (GE f) ≤ M * M * inner ℝ f (GF f) := by
      linarith [hla', hb]
    have : M⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f) := by
      have h1 : M⁻¹ * (M * inner ℝ f (GE f)) ≤ M⁻¹ * (M * M * inner ℝ f (GF f)) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hM.le)
      have h2 : M⁻¹ * (M * inner ℝ f (GE f)) = inner ℝ f (GE f) := by
        rw [← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul]
      have h3 : M⁻¹ * (M * M * inner ℝ f (GF f)) = M * inner ℝ f (GF f) := by
        rw [show M * M * inner ℝ f (GF f) = M * (M * inner ℝ f (GF f)) by ring, ← mul_assoc,
          inv_mul_cancel₀ hM.ne', one_mul]
      rw [h2, h3] at h1
      have h4 : M⁻¹ * inner ℝ f (GE f) ≤ M⁻¹ * (M * inner ℝ f (GF f)) := by
        exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hM.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul] at h4
    exact this


/-- The reversed operator order gives the form order of the limit forms, with equal domains. -/
theorem aux_prop_conc_resampled_limit_order_form_of_op
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (h : ∀ f : DomainL2 Q, inner ℝ f (GF f) ≤ m⁻¹ * inner ℝ f (GE f) ∧
      M⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f)) :
    limitFormDomain GE = limitFormDomain GF ∧
    ∀ u ∈ limitFormDomain GE, m * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal ∧
      (limitFormEnergy GF u).toReal ≤ M * (limitFormEnergy GE u).toReal := by
  have hfin : ∀ (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q), u ∈ limitFormDomain G →
      limitFormEnergy G u = ((limitFormEnergy G u).toReal : EReal) := by
    intro G u hu
    have h0 := limitFormEnergy_nonneg G u
    have h1 : limitFormEnergy G u < ⊤ := hu
    exact (EReal.coe_toReal h1.ne (by intro hb; rw [hb] at h0; exact absurd h0 (by simp))).symm
  -- Claim A: `E_F u ≤ c → E_E u ≤ m⁻¹ c`
  have hA : ∀ (u : DomainL2 Q) (c : ℝ), limitFormEnergy GF u ≤ (c : EReal) →
      limitFormEnergy GE u ≤ ((m⁻¹ * c : ℝ) : EReal) := by
    intro u c hc
    refine aux_prop_conc_resampled_limit_order_energy_le GE u _ fun f => ?_
    have h1 := (aux_prop_conc_resampled_limit_order_le_energy GF (m • f) u).trans hc
    have h1' := EReal.coe_le_coe_iff.mp h1
    have e1 : inner ℝ (m • f) u = m * inner ℝ f u := by rw [real_inner_smul_left]
    have e2 : inner ℝ (m • f) (GF (m • f)) = m * m * inner ℝ f (GF f) := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    rw [e1, e2] at h1'
    have hq := (h f).1
    have hq' : m * m * inner ℝ f (GF f) ≤ m * inner ℝ f (GE f) := by
      have := mul_le_mul_of_nonneg_left hq (mul_nonneg hm.le hm.le)
      have e3 : m * m * (m⁻¹ * inner ℝ f (GE f)) = m * inner ℝ f (GE f) := by field_simp
      linarith [this, e3]
    have h2 : m * (2 * inner ℝ f u - inner ℝ f (GE f)) ≤ c := by nlinarith [h1', hq']
    have h3 : 2 * inner ℝ f u - inner ℝ f (GE f) ≤ m⁻¹ * c := by
      have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hm.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul] at this
    exact h3
  -- Claim B: `E_E u ≤ c → E_F u ≤ M c`
  have hB : ∀ (u : DomainL2 Q) (c : ℝ), limitFormEnergy GE u ≤ (c : EReal) →
      limitFormEnergy GF u ≤ ((M * c : ℝ) : EReal) := by
    intro u c hc
    refine aux_prop_conc_resampled_limit_order_energy_le GF u _ fun f => ?_
    have h1 := (aux_prop_conc_resampled_limit_order_le_energy GE (M⁻¹ • f) u).trans hc
    have h1' := EReal.coe_le_coe_iff.mp h1
    have e1 : inner ℝ (M⁻¹ • f) u = M⁻¹ * inner ℝ f u := by rw [real_inner_smul_left]
    have e2 : inner ℝ (M⁻¹ • f) (GE (M⁻¹ • f)) = M⁻¹ * M⁻¹ * inner ℝ f (GE f) := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    rw [e1, e2] at h1'
    have hq := (h f).2
    have h2 : M * (2 * (M⁻¹ * inner ℝ f u) - M⁻¹ * M⁻¹ * inner ℝ f (GE f)) ≤ M * c :=
      mul_le_mul_of_nonneg_left h1' hM.le
    have e3 : M * (2 * (M⁻¹ * inner ℝ f u) - M⁻¹ * M⁻¹ * inner ℝ f (GE f)) =
        2 * inner ℝ f u - M⁻¹ * inner ℝ f (GE f) := by field_simp
    rw [e3] at h2
    linarith [h2, hq]
  have hdomEF : ∀ u, u ∈ limitFormDomain GE → u ∈ limitFormDomain GF := by
    intro u hu
    have h1 := hB u _ (le_of_eq (hfin GE u hu))
    exact lt_of_le_of_lt h1 (EReal.coe_lt_top _)
  have hdomFE : ∀ u, u ∈ limitFormDomain GF → u ∈ limitFormDomain GE := by
    intro u hu
    have h1 := hA u _ (le_of_eq (hfin GF u hu))
    exact lt_of_le_of_lt h1 (EReal.coe_lt_top _)
  refine ⟨Set.ext fun u => ⟨hdomEF u, hdomFE u⟩, fun u hu => ?_⟩
  have huF := hdomEF u hu
  have hB' := EReal.coe_le_coe_iff.mp
    ((hfin GF u huF).symm.le.trans (hB u _ (le_of_eq (hfin GE u hu))))
  have hA' := EReal.coe_le_coe_iff.mp
    ((hfin GE u hu).symm.le.trans (hA u _ (le_of_eq (hfin GF u huF))))
  refine ⟨?_, hB'⟩
  have := mul_le_mul_of_nonneg_left hA' hm.le
  rwa [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul] at this


end

/-- **Legendre duality of limit forms**: the form order of the limit forms (with equal domains) is equivalent to the
reversed order of the quadratic forms of the symmetric nonnegative operators. -/
theorem prop_conc_resampled_limit_order {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEs : ∀ x y, inner ℝ (GE x) y = inner ℝ x (GE y)) (hEp : ∀ x, 0 ≤ inner ℝ x (GE x))
    (hFs : ∀ x y, inner ℝ (GF x) y = inner ℝ x (GF y)) (hFp : ∀ x, 0 ≤ inner ℝ x (GF x))
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M) :
    (limitFormDomain GE = limitFormDomain GF ∧
      ∀ u ∈ limitFormDomain GE, m * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal ∧
        (limitFormEnergy GF u).toReal ≤ M * (limitFormEnergy GE u).toReal) ↔
    ∀ f : DomainL2 Q, inner ℝ f (GF f) ≤ m⁻¹ * inner ℝ f (GE f) ∧
      M⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f) :=
  ⟨fun h f => aux_prop_conc_resampled_limit_order_op_of_form GE GF hEs hEp hFs hFp m M hm hM h.1 h.2 f,
    aux_prop_conc_resampled_limit_order_form_of_op GE GF m M hm hM⟩

end
end Paper
