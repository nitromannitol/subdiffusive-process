module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductFlatComparator
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedComponentAssembly

@[expose] public section

/-!
# Theta-perturbed ladder: local energy readout

At exponent two the weighted local-energy premise of the sharp comparator is
only a deterministic geometric factor times the square root of the root cube
energy.  This module records that reduction for the localized product family,
leaving the interior Caccioppoli estimate as the sole PDE-side residue.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Root coefficient energy implies the exact weighted local-energy slot of
the sharp product comparator. -/
theorem weightedLocalSymmetricEnergyLp_localizedTheta_le_of_rootEnergy
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (s1 s : FractionalOrder) (hgap : 0 < s.1 - s1.1)
    {H : ℝ}
    (hroot : cubeAverage Q (coefficientEnergyDensity
      ((localizedThetaCoeffFamily M L omega hB theta htheta hepsilon0
        hepsilon1 hnear).coeffOn Q).toCoeffField u.grad) ≤ H) :
    weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
        ((localizedThetaCoeffFamily M L omega hB theta htheta hepsilon0
          hepsilon1 hnear).coeffOn Q) u s1 s FiniteLpExponent.two ≤
      ENNReal.ofReal
        (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 s.1 *
          Real.sqrt H) := by
  have hraw := weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout
    Q ((localizedThetaCoeffFamily M L omega hB theta htheta hepsilon0
      hepsilon1 hnear).coeffOn Q) u s1 s hgap
  have hsqrt : Real.sqrt (cubeAverage Q (coefficientEnergyDensity
      ((localizedThetaCoeffFamily M L omega hB theta htheta hepsilon0
        hepsilon1 hnear).coeffOn Q).toCoeffField u.grad)) ≤ Real.sqrt H :=
    Real.sqrt_le_sqrt hroot
  exact hraw.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hsqrt
      (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg s1.1 s.1)))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
