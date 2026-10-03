module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAnalyticLocality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCube7a
@[expose] public section

/-! A local analytic predicate inherits an ambient failure bound through the exact coefficient observation and at every translated lattice site. -/

set_option autoImplicit false
open Homogenization MeasureTheory Set Filter SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem goodCube_exists_raw_local_test_event
    {d : ℕ} (M : GMCModel d) (n : ℕ) (P : (Vec d → ℝ) → Prop)
    (hlocal : ∀ a b : Vec d → ℝ,
      Set.EqOn a b (nativeBox n 1 (0 : Lattice d)) → (P a ↔ P b))
    {B : ℝ≥0∞} (Bad : Set (PotentialSample d))
    (hbound : M.P.toMeasure Bad ≤ B)
    (hgood : ∀ᵐ omega ∂M.P.toMeasure, omega ∉ Bad → P (aCutoff M n omega)) :
    ∃ bad : Set (nativeBox n 1 (0 : Lattice d) → ℝ),
      (∀ z : Lattice d, M.P.toMeasure (coefficientLocalBadEvent M n 1 bad z) ≤ B) ∧
      ∀ (z : Lattice d) (omega : PotentialSample d),
        omega ∉ coefficientLocalBadEvent M n 1 bad z →
        P (fun x => aCutoff M n omega (x + goodCubeCentre n z)) := by
  have hobsEq : ∀ omega omega' : PotentialSample d,
      restrictedCoefficientObservation (aCutoff M n)
        (nativeBox n 1 (0 : Lattice d)) omega =
      restrictedCoefficientObservation (aCutoff M n)
        (nativeBox n 1 (0 : Lattice d)) omega' →
      Set.EqOn (aCutoff M n omega) (aCutoff M n omega')
        (nativeBox n 1 (0 : Lattice d)) := by
    intro omega omega' heq x hx
    have h := congrFun heq (Subtype.mk x hx)
    exact h
  obtain ⟨bad, hraw, hmu0⟩ :=
    goodCube_exists_restricted_failure_le_ambient (mu := M.P.toMeasure)
      (restrictedCoefficientObservation (aCutoff M n)
        (nativeBox n 1 (0 : Lattice d)))
      (fun omega => P (aCutoff M n omega))
      (fun omega omega' heq => hlocal _ _ (hobsEq omega omega' heq))
      Bad hbound hgood
  refine ⟨bad, ?_, ?_⟩
  · intro z
    unfold coefficientLocalBadEvent
    rw [measure_preimage_translatePotentialSequence]
    exact hmu0
  · intro z omega homega
    unfold coefficientLocalBadEvent at homega
    have hmem : translatePotentialSequence (goodCubeCentre n z) omega ∉
        (restrictedCoefficientObservation (aCutoff M n)
          (nativeBox n 1 (0 : Lattice d)) ⁻¹' bad) := fun h => homega h
    rw [hraw] at hmem
    have hP : P (aCutoff M n
        (translatePotentialSequence (goodCubeCentre n z) omega)) := by
      simpa only [Set.mem_setOf_eq, not_not] using hmem
    have heqf : (fun x : Vec d => aCutoff M n omega (x + goodCubeCentre n z))
        = aCutoff M n (translatePotentialSequence (goodCubeCentre n z) omega) := by
      funext x
      exact (aCutoff_translatePotentialSequence M n (goodCubeCentre n z) omega x).symm
    rw [heqf]
    exact hP
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
