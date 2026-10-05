module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.Paper.inputs_Cp_holder

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_Cp_witness (d : ℕ) : Nonempty (CampanatoInput d) := by
  let C : ℝ → ℝ := fun alpha =>
    if h : 0 < alpha ∧ alpha < 1 then
      Classical.choose (inputs_Cp_holder d alpha h.1 h.2)
    else
      Classical.choose (inputs_Cp_holder d (1 / 2) (by norm_num) (by norm_num))
  have hC_pos : ∀ alpha, 0 < alpha → alpha < 1 → 0 < C alpha := by
    intro alpha hα₀ hα₁
    dsimp only [C]
    split_ifs with h
    · have heq : inputs_Cp_holder d alpha h.1 h.2 =
          inputs_Cp_holder d alpha hα₀ hα₁ := Subsingleton.elim _ _
      rw [congrArg (fun h' => Classical.choose h') heq]
      exact (Classical.choose_spec (inputs_Cp_holder d alpha hα₀ hα₁)).1
    · exact (False.elim (h ⟨hα₀, hα₁⟩))
  refine ⟨{
    C := C
    C_pos := hC_pos
    holder_of_campanato := ?_
  }⟩
  intro alpha hα₀ hα₁ z r hr hr_le u K hK hcamp
  dsimp only [C]
  split_ifs with h
  · have heq : inputs_Cp_holder d alpha h.1 h.2 =
        inputs_Cp_holder d alpha hα₀ hα₁ := Subsingleton.elim _ _
    rw [congrArg (fun h' => Classical.choose h') heq]
    exact (Classical.choose_spec (inputs_Cp_holder d alpha hα₀ hα₁)).2
      z r hr hr_le u K hK hcamp
  · exact (False.elim (h ⟨hα₀, hα₁⟩))

end SubdiffusiveProcess.Paper
