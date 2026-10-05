module

public import SubdiffusiveProcess.Sobolev.LimitFormUniqueness
public import SubdiffusiveProcess.Variational.DualEnergy

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology

noncomputable section
namespace SubdiffusiveProcess.Section9

/-- A finite strictly positive dual energy excludes the zero inverse. -/
theorem limitInverse_ne_zero_of_positive_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (henergy : ∃ u : DomainL2 Q, u ∈ limitFormDomain G ∧
      0 < (limitFormEnergy G u).toReal) : G ≠ 0 := by
  rintro rfl
  obtain ⟨u, hu, hpos⟩ := henergy
  have hbot : limitFormEnergy (0 : DomainL2 Q →L[ℝ] DomainL2 Q) u ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (limitFormEnergy_nonneg _ u)
  have hreal := EReal.coe_toReal hu.ne hbot
  have hnorm := norm_sq_le_operatorNorm_mul_quadraticDual
    (0 : DomainL2 Q →L[ℝ] DomainL2 Q) u _ hreal.symm
  have hu0 : u = 0 := by
    apply norm_eq_zero.mp
    have hn : ‖u‖ ^ 2 ≤ 0 := by simpa using hnorm
    nlinarith [norm_nonneg u]
  subst u
  simp [limitFormEnergy] at hpos

/-- Real polarization gives a positive quadratic test for a nonzero positive symmetric map. -/
theorem exists_positive_quadratic_of_symmetric_positive_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hp : ∀ x, 0 ≤ inner ℝ x (G x)) (hne : G ≠ 0) :
    ∃ x : E, 0 < inner ℝ x (G x) := by
  by_contra h
  push Not at h
  have hzero : ∀ x : E, inner ℝ x (G x) = 0 :=
    fun x => le_antisymm (h x) (hp x)
  apply hne
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [symmetric_operator_pairing_eq G hs y x, hzero (y + x), hzero y, hzero x]
  simp

/-- The image of a positive quadratic test has finite strictly positive dual energy. -/
theorem exists_positive_energy_of_symmetric_positive_ne_zero
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hp : ∀ x, 0 ≤ inner ℝ x (G x)) (hne : G ≠ 0) :
    ∃ u : DomainL2 Q, u ∈ limitFormDomain G ∧
      0 < (limitFormEnergy G u).toReal := by
  obtain ⟨x, hx⟩ := exists_positive_quadratic_of_symmetric_positive_ne_zero G hs hp hne
  refine ⟨G x, apply_mem_limitFormDomain G hs hp x, ?_⟩
  rwa [limitFormEnergy_apply_eq G hs hp x, EReal.toReal_coe]

end SubdiffusiveProcess.Section9
