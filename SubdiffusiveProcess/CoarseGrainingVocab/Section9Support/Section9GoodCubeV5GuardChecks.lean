module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5Assembly

@[expose] public section

/-! The exact logical cost of recovering unconditional tests from a law guard.
These checks concern the actual `LocalDiffusionData` carrier.  They do not
assert that this carrier is empty, or refute the original transfer theorem. -/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A law-independent conclusion under this guard has exactly an existence
premise.  Omitting a law witness does not make the conclusion unconditional. -/
theorem goodCubeV5_lawIndependent_guard_iff {d : ℕ} (a : Vec d → ℝ) (P : Prop) :
    (∀ law : Kernel (Vec d) (Path d), LocalDiffusionData a a law → P) ↔
      ((∃ law : Kernel (Vec d) (Path d), LocalDiffusionData a a law) → P) := by
  constructor
  · rintro h ⟨law, hlaw⟩
    exact h law hlaw
  · exact fun h law hlaw => h ⟨law, hlaw⟩

/-- Unconditional extraction of arbitrary tests is equivalent to supplying the
missing witness on precisely this coefficient's law class. -/
theorem goodCubeV5_unconditional_extraction_iff {d : ℕ} (a : Vec d → ℝ) :
    (∀ P : Prop,
      (∀ law : Kernel (Vec d) (Path d), LocalDiffusionData a a law → P) → P) ↔
      ∃ law : Kernel (Vec d) (Path d), LocalDiffusionData a a law := by
  constructor
  · intro h
    exact h _ (fun law hlaw => ⟨law, hlaw⟩)
  · rintro ⟨law, hlaw⟩ P h
    exact h law hlaw

/-- If the cutoff law class is empty, every cutoff package in O's premise
holds.  This is a conditional vacuity check, not a nonexistence theorem. -/
theorem goodCubeV5_guard_of_no_law {d : ℕ} (a : Vec d → ℝ)
    (h : ¬ ∃ law : Kernel (Vec d) (Path d), LocalDiffusionData a a law)
    (P : Kernel (Vec d) (Path d) → Prop) :
    ∀ law : Kernel (Vec d) (Path d), LocalDiffusionData a a law → P law := by
  intro law hlaw
  exact (h ⟨law, hlaw⟩).elim

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
