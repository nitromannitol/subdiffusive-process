import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Probability.SymmetricPairingMeasurability
import Mathlib.Tactic.Linarith

/-! A positive symmetric killed inverse is determined by its dual energy and
finite-energy domain. No existence or convergence of an inverse is asserted. -/

open MeasureTheory Set TopologicalSpace

namespace SubdiffusiveProcess
noncomputable section
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- The dual energy at an image vector equals its original quadratic pairing. -/
theorem limitFormEnergy_apply_eq
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hp : ∀ x, 0 ≤ inner ℝ x (G x)) (x : DomainL2 Q) :
    limitFormEnergy G (G x) = ((inner ℝ x (G x) : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro f
    apply EReal.coe_le_coe_iff.mpr
    have h := hp (f - x)
    simp only [map_sub, inner_sub_left, inner_sub_right] at h
    rw [hs x f] at h
    linarith only [h]
  · apply le_iSup_of_le x
    apply EReal.coe_le_coe_iff.mpr
    linarith only []

/-- Every image vector of a positive symmetric inverse belongs to its finite-energy domain. -/
theorem apply_mem_limitFormDomain
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hp : ∀ x, 0 ≤ inner ℝ x (G x)) (x : DomainL2 Q) :
    G x ∈ limitFormDomain G := by
  change limitFormEnergy G (G x) < ⊤
  rw [limitFormEnergy_apply_eq G hs hp x]
  exact EReal.coe_lt_top _

/-- Energy comparison on the first inverse's range reverses its quadratic pairing comparison. -/
theorem inner_le_of_limitFormEnergy_eq
    (G F : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hp : ∀ x, 0 ≤ inner ℝ x (G x))
    (he : ∀ u ∈ limitFormDomain G, limitFormEnergy G u = limitFormEnergy F u)
    (x : DomainL2 Q) : inner ℝ x (G x) ≤ inner ℝ x (F x) := by
  have h := le_iSup (fun f : DomainL2 Q =>
    ((2 * inner ℝ f (G x) - inner ℝ f (F f) : ℝ) : EReal)) x
  change ((2 * inner ℝ x (G x) - inner ℝ x (F x) : ℝ) : EReal) ≤
    limitFormEnergy F (G x) at h
  rw [← he (G x) (apply_mem_limitFormDomain G hs hp x),
    limitFormEnergy_apply_eq G hs hp x] at h
  have hreal := EReal.coe_le_coe_iff.mp h
  linarith only [hreal]

/-- Common finite-energy domains and equal dual energies identify positive symmetric inverses. -/
theorem eq_of_limitFormEnergy_eq
    (G F : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hGp : ∀ x, 0 ≤ inner ℝ x (G x))
    (hFs : ∀ x y, inner ℝ x (F y) = inner ℝ y (F x))
    (hFp : ∀ x, 0 ≤ inner ℝ x (F x))
    (hd : limitFormDomain G = limitFormDomain F)
    (he : ∀ u ∈ limitFormDomain G, limitFormEnergy G u = limitFormEnergy F u) : G = F := by
  have hq (x : DomainL2 Q) : inner ℝ x (G x) = inner ℝ x (F x) := by
    apply le_antisymm (inner_le_of_limitFormEnergy_eq G F hGs hGp he x)
    apply inner_le_of_limitFormEnergy_eq F G hFs hFp
    intro u hu
    exact (he u (hd.symm ▸ hu)).symm
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [symmetric_operator_pairing_eq G hGs y x,
    symmetric_operator_pairing_eq F hFs y x, hq (y + x), hq y, hq x]

end
end SubdiffusiveProcess
