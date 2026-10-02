import SubdiffusiveProcess.FractionalEmbedding.DomainEmbedding

/-! Fractional Sobolev embedding on a cube: `W^{s,2}(Q) ⊂ L^{2d/(d-2s)}(Q)`, in the project's
volume-normalized inhomogeneous fractional norm.  Di Nezza--Palatucci--Valdinoci, Hitchhiker's
guide to the fractional Sobolev spaces, Bull. Sci. Math. 136 (2012), Theorem 6.7 (with
`p = 2`, `q = p* = 2d/(d-2s)`, `sp < d`), for the extension domain `Q` (Theorem 5.4: bounded
Lipschitz open sets are `W^{s,p}`-extension domains).  No coefficient, form or PDE is involved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

noncomputable section
namespace Paper

/-- Fractional Sobolev embedding on a fixed cube, with the critical exponent
`p = 2d/(d-2s)`; the constant depends on `d`, `s` and the cube only. -/
theorem inputs_classical_fractional_sobolev_embedding
    (d : ℕ) (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
      MemLp (v : SpatialCoordinates d → ℝ) (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 2 * (s : ℝ))))
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            |v x| ^ (2 * (d : ℝ) / ((d : ℝ) - 2 * (s : ℝ)))) ^
              (((d : ℝ) - 2 * (s : ℝ)) / (d : ℝ)) ≤
          C * cubeFractionalSqNorm hd z r hr s v := by
  simpa only [SubdiffusiveProcess.FractionalEmbedding.criticalPower,
    SubdiffusiveProcess.FractionalEmbedding.criticalRoot] using
    SubdiffusiveProcess.FractionalEmbedding.cube_sobolev_embedding d hd s z r hr

end Paper
