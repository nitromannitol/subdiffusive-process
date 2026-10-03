module

public import SubdiffusiveProcess.Sobolev.SmoothCubeLipschitz
public import SubdiffusiveProcess.Sobolev.ContinuousCubeL2
public import SubdiffusiveProcess.Sobolev.FractionalRepresentatives
public import SubdiffusiveProcess.Sobolev.FractionalLipschitzFinite
@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal ContDiff
namespace SubdiffusiveProcess

/-- Smooth fields near a closed cube define actual coordinate L2 classes with finite volume-normalized fractional seminorm. The proof consumes the Lipschitz integral estimate and representative invariance; M, lines 988–1036. -/
theorem contDiffOn_cube_fractional_L2
    {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (O : Opens (SpatialCoordinates d))
    (hO : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ O)
    (f : SpatialCoordinates d → Fin k → ℝ)
    (hf : ContDiffOn ℝ ∞ f (O : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ hmem : ∀ i : Fin k, MemLp (fun x => f x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      ((ENNReal.ofReal s / volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal (∑ i : Fin k,
              ((hmem i).toLp (fun w => f w i) x - (hmem i).toLp (fun w => f w i) y) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * s)) ^ (1 / 2 : ℝ) < ⊤ := by
  obtain ⟨hmem, _⟩ := continuousOn_cube_memLp_and_nonzero z r hr f
    (hf.continuousOn.mono hO)
  obtain ⟨K, hK⟩ :=
    exists_lipschitzOnWith_cube_of_contDiffOn_neighborhood z r hr O hO f hf
  have hraw := fractional_square_integral_lt_top_of_lipschitzOnWith
    hd z r hr s hs hs1 f K hK
  refine ⟨hmem, ?_⟩
  have hrep :
      (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (∑ i : Fin k,
            ((hmem i).toLp (fun w => f w i) x - (hmem i).toLp (fun w => f w i) y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * s)) =
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * s) := by
    exact fractional_square_integral_congr_ae
      (fun i x => (hmem i).toLp (fun w => f w i) x)
      (fun i x => f x i)
      (fun i => MemLp.coeFn_toLp (hmem i)) s
  rw [hrep]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  exact (ENNReal.mul_lt_top
    (ENNReal.div_lt_top ENNReal.ofReal_ne_top (by
      rw [centeredCube_volume z hr]
      exact (ENNReal.ofReal_pos.mpr (pow_pos hr d)).ne'))
    hraw).ne

end SubdiffusiveProcess
