module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffPotential
public import SubdiffusiveProcess.Paper.in_common_scale_coupling

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Normalization display.
- One realization of the common scale coupling is fixed; supplier: in_common_scale_coupling.
- All nine defining clauses pin H, h_N, kappa_N, A_N, mu_N, T_N, the triadic clock, and relabelled layers and coefficients.
- The H series is a defining convention here; its convergence is a separate result.
- Kappa and the clock depend only on the deterministic model and cutoff.
- T_N is the literal paper clock, with no additional ahom_0 factor.
- The clock outside triadic radii is specified separately.
-/

def in_normalization (d : Nat) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
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
  (∀ N, kappa N = Real.exp (((N : Real) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) ∧
  (∀ N x, A N x = (kappa N)⁻¹ * Real.exp (h N x)) ∧
  (∀ N, mu N = volume.withDensity (fun x => ENNReal.ofReal
    (Real.exp (h N x - ((N : Real) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)))) ∧
  (∀ N, T N = (3 : Real) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) ∧
  (∀ N, Tr ((3 : Real) ^ N) = T N) ∧
  (∀ N i y, g N i y = omega ((i : Int) - (N : Int)) (((3 : Real) ^ N)⁻¹ • y)) ∧
  (∀ N y, a N y = Real.exp
    (∑ i ∈ Finset.range (N + 1), (g N i y - _root_.SubdiffusiveProcess.Model.tauSq M.P)))

end SubdiffusiveProcess.Paper
