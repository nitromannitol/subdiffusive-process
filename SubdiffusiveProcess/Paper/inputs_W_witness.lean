module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.Paper.inputs_W_gradient
public import SubdiffusiveProcess.Paper.inputs_W_morrey

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_W_witness (d : ℕ) : Nonempty (SmallPerturbationInput d) := by
  classical
  have htwo : (2 : ℝ) ≤ 2 := le_rfl
  let C : ℝ → ℝ := fun p =>
    if hp : 2 ≤ p then Classical.choose (inputs_W_gradient d p hp)
    else Classical.choose (inputs_W_gradient d 2 htwo)
  let osc : ℝ → ℝ := fun p =>
    if hp : 2 ≤ p then
      Classical.choose (Classical.choose_spec (inputs_W_gradient d p hp))
    else
      Classical.choose (Classical.choose_spec (inputs_W_gradient d 2 htwo))
  let CMorrey : ℝ → ℝ → ℝ := fun p alpha =>
    if hp : 2 ≤ p then
      if ha : 0 < alpha then
        if hgap : alpha < 1 - (d : ℝ) / p then
          Classical.choose (inputs_W_morrey d p hp alpha ha hgap)
        else 1
      else 1
    else 1
  refine ⟨{
    C := C
    C_pos := ?_
    osc := osc
    osc_pos := ?_
    interior_gradient := ?_
    CMorrey := CMorrey
    CMorrey_pos := ?_
    morrey := ?_
  }⟩
  · intro p
    by_cases hp : 2 ≤ p
    · simpa only [C, dite_eq_left hp] using
        (Classical.choose_spec (Classical.choose_spec (inputs_W_gradient d p hp))).1
    · simpa only [C, dite_eq_right hp] using
        (Classical.choose_spec (Classical.choose_spec (inputs_W_gradient d 2 htwo))).1
  · intro p
    by_cases hp : 2 ≤ p
    · simpa only [osc, dite_eq_left hp] using
        (Classical.choose_spec (Classical.choose_spec (inputs_W_gradient d p hp))).2.1
    · simpa only [osc, dite_eq_right hp] using
        (Classical.choose_spec (Classical.choose_spec (inputs_W_gradient d 2 htwo))).2.1
  · intro p hp x0 l hl a a0 ha0 hosc F Kf hF hKf hFbound u hu
    have hosc' :
        (∀ᵐ y ∂volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)),
          |Real.log (a.val y) - Real.log a0| ≤
            Classical.choose (Classical.choose_spec (inputs_W_gradient d p hp))) := by
      simpa only [osc, dite_eq_left hp] using hosc
    simpa only [C, osc, dite_eq_left hp] using
      (Classical.choose_spec (Classical.choose_spec (inputs_W_gradient d p hp))).2.2
        x0 l hl a a0 ha0 hosc' F Kf hF hKf hFbound u hu
  · intro p alpha
    by_cases hp : 2 ≤ p
    · by_cases ha : 0 < alpha
      · by_cases hgap : alpha < 1 - (d : ℝ) / p
        · have hspec := Classical.choose_spec (inputs_W_morrey d p hp alpha ha hgap)
          unfold CMorrey
          rw [dite_eq_left hp, dite_eq_left ha, dite_eq_left hgap]
          exact hspec.1
        · unfold CMorrey
          rw [dite_eq_left hp, dite_eq_left ha, dite_eq_right hgap]
          norm_num
      · unfold CMorrey
        rw [dite_eq_left hp, dite_eq_right ha]
        norm_num
    · unfold CMorrey
      rw [dite_eq_right hp]
      norm_num
  · intro p hp alpha ha hgap x0 l hl u hmem
    have hspec := Classical.choose_spec (inputs_W_morrey d p hp alpha ha hgap)
    unfold CMorrey
    rw [dite_eq_left hp, dite_eq_left ha, dite_eq_left hgap]
    exact hspec.2 x0 l hl u hmem

end SubdiffusiveProcess.Paper
