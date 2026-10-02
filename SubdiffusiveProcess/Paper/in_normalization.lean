import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Main.CutoffPotential
import SubdiffusiveProcess.Paper.in_common_scale_coupling

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal BigOperators

noncomputable section
namespace Paper




def in_normalization (d : Nat) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : BilateralField d)
    (H : C(SpatialCoordinates d, Real))
    (h : Nat → SpatialCoordinates d → Real)
    (kappa : Nat → Real) (A : Nat → SpatialCoordinates d → Real)
    (mu : Nat → Measure (SpatialCoordinates d))
    (T : Nat → Real) (Tr : Real → Real)
    (g : Nat → Nat → SpatialCoordinates d → Real)
    (a : Nat → SpatialCoordinates d → Real) : Prop :=
  (∀ x, H x = ∑' j : Nat, (omega ((j : Int) + 1) x - omega ((j : Int) + 1) 0)) ∧
  (∀ N x, h N x = H x + ∑ j ∈ Finset.range (N + 1), omega (-(j : Int)) x) ∧
  (∀ N, kappa N = Real.exp (((N : Real) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) ∧
  (∀ N x, A N x = (kappa N)⁻¹ * Real.exp (h N x)) ∧
  (∀ N, mu N = volume.withDensity (fun x => ENNReal.ofReal
    (Real.exp (h N x - ((N : Real) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))) ∧
  (∀ N, T N = (3 : Real) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) ∧
  (∀ N, Tr ((3 : Real) ^ N) = T N) ∧
  (∀ N i y, g N i y = omega ((i : Int) - (N : Int)) (((3 : Real) ^ N)⁻¹ • y)) ∧
  (∀ N y, a N y = Real.exp
    (∑ i ∈ Finset.range (N + 1), (g N i y - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))

end Paper
