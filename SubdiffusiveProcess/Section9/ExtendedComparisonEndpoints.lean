import SubdiffusiveProcess.Section9.RepresentedComparisonDraft
import Mathlib

/-! The extended-valued endpoint order for proportional limit forms.
A positive finite energy excludes degeneracy; no infinite energy is converted to a real. -/

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section9

/-- The real part recovers an energy only on its finite-energy domain. -/
theorem finite_limit_energy_coe {d : ℕ} {Q : TopologicalSpace.Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q)
    (hu : u ∈ limitFormDomain G) :
    ((limitFormEnergy G u).toReal : EReal) = limitFormEnergy G u :=
  EReal.coe_toReal (ne_of_lt hu)
    (ne_bot_of_le_ne_bot (by simp) (limitFormEnergy_nonneg G u))

/-- Positive proportionality coefficients agree with their real EReal embedding. -/
theorem positive_proportional_coefficient (c : ℝ) (hc : 0 < c) :
    (ENNReal.ofReal c : EReal) = (c : EReal) := by
  rw [EReal.coe_ennreal_ofReal, max_eq_left hc.le]

/-- A positive finite-energy test identifies the proportionality scalar. -/
theorem proportional_scalar_eq
    {d : ℕ} {Ω : Type} (GE GF : KilledInverseFamily d Ω) (ω : Ω)
    (c b : ℝ) (hc : 0 < c) (hb : 0 < b)
    (hpc : ProportionalLimitForms d Ω GE GF c ω)
    (hpb : ProportionalLimitForms d Ω GE GF b ω)
    (hnonzero : ∃ i, ∃ u : DomainL2 (determiningCube d i),
      u ∈ limitFormDomain (GE i ω) ∧ 0 < (limitFormEnergy (GE i ω) u).toReal) : c = b := by
  obtain ⟨i, u, hu, hpos⟩ := hnonzero
  have h := ((hpc i).2 u).symm.trans ((hpb i).2 u)
  rw [positive_proportional_coefficient c hc, positive_proportional_coefficient b hb,
    ← finite_limit_energy_coe (GE i ω) u hu, ← EReal.coe_mul, ← EReal.coe_mul] at h
  exact (mul_right_cancel₀ hpos.ne' (EReal.coe_injective h))

/-- The lower and upper extended-valued endpoint sets have the exact scalar endpoints. -/
theorem endpoints_eq_of_proportional
    {d : ℕ} {Ω : Type} (GE GF : KilledInverseFamily d Ω) (ω : Ω)
    (c : ℝ) (hc : 0 < c) (hprop : ProportionalLimitForms d Ω GE GF c ω)
    (hnonzero : ∃ i, ∃ u : DomainL2 (determiningCube d i),
      u ∈ limitFormDomain (GE i ω) ∧ 0 < (limitFormEnergy (GE i ω) u).toReal) :
    lowerEndpoint d Ω GE GF ω = c ∧ upperEndpoint d Ω GE GF ω = c := by
  obtain ⟨i, u, hu, hpos⟩ := hnonzero
  have hE := finite_limit_energy_coe (GE i ω) u hu
  have hlo : ∀ a : ℝ, (0 < a ∧ ∀ j, ∀ v : DomainL2 (determiningCube d j),
      (a : EReal) * limitFormEnergy (GE j ω) v ≤ limitFormEnergy (GF j ω) v) ↔
      0 < a ∧ a ≤ c := by
    intro a
    constructor
    · rintro ⟨ha, h⟩
      have htest := h i u
      rw [(hprop i).2 u, positive_proportional_coefficient c hc, ← hE,
        ← EReal.coe_mul, ← EReal.coe_mul] at htest
      exact ⟨ha, (mul_le_mul_iff_left₀ hpos).mp (EReal.coe_le_coe_iff.mp htest)⟩
    · rintro ⟨ha, hac⟩
      refine ⟨ha, fun j v => ?_⟩
      rw [(hprop j).2 v, positive_proportional_coefficient c hc]
      exact mul_le_mul_of_nonneg_right (EReal.coe_le_coe_iff.mpr hac)
        (limitFormEnergy_nonneg (GE j ω) v)
  have hhi : ∀ a : ℝ, (0 < a ∧ ∀ j, ∀ v : DomainL2 (determiningCube d j),
      limitFormEnergy (GF j ω) v ≤ (a : EReal) * limitFormEnergy (GE j ω) v) ↔ c ≤ a := by
    intro a
    constructor
    · rintro ⟨ha, h⟩
      have htest := h i u
      rw [(hprop i).2 u, positive_proportional_coefficient c hc, ← hE,
        ← EReal.coe_mul, ← EReal.coe_mul] at htest
      exact (mul_le_mul_iff_left₀ hpos).mp (EReal.coe_le_coe_iff.mp htest)
    · intro hca
      refine ⟨hc.trans_le hca, fun j v => ?_⟩
      rw [(hprop j).2 v, positive_proportional_coefficient c hc]
      exact mul_le_mul_of_nonneg_right (EReal.coe_le_coe_iff.mpr hca)
        (limitFormEnergy_nonneg (GE j ω) v)
  have hloset : {a : ℝ | 0 < a ∧ ∀ j, ∀ v : DomainL2 (determiningCube d j),
      (a : EReal) * limitFormEnergy (GE j ω) v ≤ limitFormEnergy (GF j ω) v} = Set.Ioc 0 c :=
    Set.ext fun a => hlo a
  have hhiset : {a : ℝ | 0 < a ∧ ∀ j, ∀ v : DomainL2 (determiningCube d j),
      limitFormEnergy (GF j ω) v ≤ (a : EReal) * limitFormEnergy (GE j ω) v} = Set.Ici c :=
    Set.ext fun a => hhi a
  constructor
  · change sSup _ = c
    rw [hloset, csSup_Ioc hc]
  · change sInf _ = c
    rw [hhiset, csInf_Ici]

/-- Equality of inverse operators gives equality of full extended energies and domains. -/
theorem proportional_one_of_inverse_eq
    {d : ℕ} {Ω : Type} (GE GF : KilledInverseFamily d Ω) (ω : Ω)
    (h : ∀ i, GE i ω = GF i ω) : ProportionalLimitForms d Ω GE GF 1 ω := by
  intro i
  rw [h i]
  exact ⟨rfl, fun u => by simp⟩

end SubdiffusiveProcess.Section9
