module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.EquationLocalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationTranslation

@[expose] public section

/-!
# Theta-perturbed ladder: product equation on the family carrier

The response error is indexed by `localizedThetaCoeffFamily`, while the
physical equation is written with its scalar coefficient field.  This file
records the exact conversion to Chapter 3's matrix-valued forced-equation
carrier.  The force is zero; no base-cutoff equation is used.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- A weakly harmonic function for the localized product coefficient is a
zero-forcing solution for the same coefficient on the triadic-family carrier.
-/
theorem isForcedEquation_localizedThetaCoeffFamily
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (hu : IsWeaklyHarmonicOn
      (localizedThetaCutoff M L omega B b theta) (openCubeSet Q) u) :
    Ch03.ABK26.IsForcedEquation Q
      ((localizedThetaCoeffFamily M L omega hB theta htheta hepsilon0
        hepsilon1 hnear).coeffOn Q) u (fun _ ↦ 0) := by
  intro phi
  have hphi := hu phi
  simp only [localizedThetaCoeffFamily, localizedThetaTriadicCoeffData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
    matVecMul_scalarMatrix]
  calc
    (∫ x in openCubeSet Q,
        vecDot (localizedThetaCutoff M L omega B b theta x • u.grad x)
          (phi.toH1Function.grad x) ∂volume) = 0 := hphi
    _ = -(∫ x in openCubeSet Q,
        vecDot 0 (phi.toH1Function.grad x) ∂volume) := by
          simp only [vecDot_zero_left, integral_zero, neg_zero]

/-- The preceding conversion after first replacing the physical normalized
coefficient by its collar-localized extension. -/
theorem isForcedEquation_localizedThetaCoeffFamily_of_physical
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon : ℝ} (hb : 0 < b)
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (Q : TriadicCube d) (hQB : openCubeSet Q ⊆ B)
    (u : H1Function (openCubeSet Q))
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (openCubeSet Q) u) :
    Ch03.ABK26.IsForcedEquation Q
      ((localizedThetaCoeffFamily M L omega hB theta htheta hepsilon0
        hepsilon1 hnear).coeffOn Q) u (fun _ ↦ 0) := by
  apply isForcedEquation_localizedThetaCoeffFamily M L omega hB theta htheta
    hepsilon0 hepsilon1 hnear Q u
  exact isWeaklyHarmonicOn_localizedThetaCutoff_of_physical M L omega
    (isOpen_openCubeSet Q).measurableSet hQB hb theta hu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
