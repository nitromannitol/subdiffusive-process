import SubdiffusiveProcess.MeyersRegularity.Final
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.NativeBridge

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The open Euclidean ball `B_R(x0) = {x : |x - x0|₂ < R}` as a subset of `Vec d`
(`Vec d` itself carries the sup norm, so `Metric.ball` is a cube). -/
def aux_classical_meyers_gradient_ball {d : ℕ} (x0 : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | ∑ i : Fin d, (x i - x0 i) ^ 2 < R ^ 2}

/-- Meyers (1963), Ann. Scuola Norm. Sup. Pisa 17, 189--206, Theorem 2, estimate (49), in the special
case `A = a I` (scalar coefficient with `|a - 1| ≤ ε`, i.e. ellipticity ratio `θλ` close to `1`),
`f = 0`, source `h ∈ L^r` with `r = p ≥ 2 ≥ 2n/(n+2)` (so `r* ≥ p`), on the concentric Euclidean balls
`B_R ⊂ B_{2R} ⊂ Ω = B_{3R}` (so `2R < d_y = 3R`, as Meyers' proof requires): a weak solution
`u ∈ H¹(Ω)` of `div (a ∇u) = h` on `Ω` satisfies
`|∇u|_{p;R} ≤ C (R^{n(1/p-1/2)-1} |u|_{2;2R} + R^{n(1/p-1/r)+1} |h|_{r;2R})`,
where `|·|_{q;ρ}` is the (unnormalised) `L^q(B_ρ)` norm and `ε, C` depend only on `(n, p)`. -/
theorem classical_meyers_gradient (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ 0 < C ∧
      ∀ (x0 : Vec d) (R : ℝ), 0 < R →
      ∀ (a h : Vec d → ℝ),
        AEMeasurable a (volume.restrict (aux_classical_meyers_gradient_ball x0 (3 * R))) →
        (∀ᵐ x ∂volume.restrict (aux_classical_meyers_gradient_ball x0 (3 * R)),
          |a x - 1| ≤ epsilon) →
        MemLp h (ENNReal.ofReal p) (volume.restrict (aux_classical_meyers_gradient_ball x0 (3 * R))) →
      ∀ u : H1Function (aux_classical_meyers_gradient_ball x0 (3 * R)),
        (∀ phi : H10Function (aux_classical_meyers_gradient_ball x0 (3 * R)),
          (∫ x in aux_classical_meyers_gradient_ball x0 (3 * R),
              a x * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) =
            -∫ x in aux_classical_meyers_gradient_ball x0 (3 * R),
              h x * phi.toH1Function.toFun x) →
        MemLp (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p)
            (volume.restrict (aux_classical_meyers_gradient_ball x0 R)) ∧
          (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p)
              (volume.restrict (aux_classical_meyers_gradient_ball x0 R))).toReal ≤
            C * (R ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) *
                (eLpNorm u.toFun 2
                  (volume.restrict (aux_classical_meyers_gradient_ball x0 (2 * R)))).toReal +
              R * (eLpNorm h (ENNReal.ofReal p)
                (volume.restrict (aux_classical_meyers_gradient_ball x0 (2 * R)))).toReal) := by
  exact SubdiffusiveProcess.MeyersRegularity.exists_meyers_estimate d hd p hp

end Paper
