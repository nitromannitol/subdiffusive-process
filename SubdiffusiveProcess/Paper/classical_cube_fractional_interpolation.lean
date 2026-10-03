module

public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Paper.inputs_classical_e4_interpolation

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

namespace Paper

/-- Classical fractional Sobolev interpolation on a fixed cube, in the
project's volume-normalized carriers.  PROVED (paper `\label{mfd:lem-19}`, last display of its proof) from the unit-cube
interpolation leaf `classical_unit_cube_fractional_interpolation` by the dilation of the cube: in the norms
`Sem_σ + r^{-σ}a` the factor `r^{-1/2}` cancels, so the constant is that of the unit cube. -/
theorem classical_cube_fractional_interpolation
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1)
    (hthreeQuarters : (threeQuarters : ℝ) = 3 / 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (wHalf : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
        (wThree : CubeFractionalL2 (k := 1) hd z r hr threeQuarters),
        wThree.val 0 = wHalf.val 0 →
        cubeFractionalL2Norm hd z r hr halfFractionalOrder wHalf ≤
          C * (‖wHalf.val 0‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
              (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd z r hr threeQuarters wThree ^ (2 / 3 : ℝ) := by
  have hhalf : ((halfFractionalOrder : Set.Ioo (0 : ℝ) 1) : ℝ) = 1 / 2 := rfl
  have hts : ((halfFractionalOrder : Set.Ioo (0 : ℝ) 1) : ℝ) < threeQuarters := by
    rw [hthreeQuarters, hhalf]; norm_num
  obtain ⟨C, hC, hall⟩ := aux_inputs_classical_e4_interpolation_all_sum hd threeQuarters halfFractionalOrder hts
  refine ⟨C, hC, ?_⟩
  intro wHalf wThree hEq
  set v := wHalf.val 0 with hv
  have hw1 : wHalf.val = fun _ : Fin 1 => v := funext fun i => by fin_cases i; rfl
  have hw3 : wThree.val = fun _ : Fin 1 => v := funext fun i => by fin_cases i; exact hEq
  have hfin : cubeFractionalL2Seminorm hd z r hr threeQuarters (fun _ : Fin 1 => v) < ⊤ := by
    rw [← hw3]; exact wThree.property
  obtain ⟨-, hmain⟩ := hall z r hr v hfin
  have hexp1 : 1 - ((halfFractionalOrder : Set.Ioo (0 : ℝ) 1) : ℝ) / threeQuarters = 1 / 3 := by
    rw [hthreeQuarters, hhalf]; norm_num
  have hexp2 : ((halfFractionalOrder : Set.Ioo (0 : ℝ) 1) : ℝ) / threeQuarters = 2 / 3 := by
    rw [hthreeQuarters, hhalf]; norm_num
  rw [hexp1, hexp2] at hmain
  unfold cubeFractionalL2Norm
  simp only [Finset.univ_unique, Finset.sum_singleton, hw1, hw3]
  rw [Real.sqrt_sq (norm_nonneg v)]
  exact hmain

end Paper

