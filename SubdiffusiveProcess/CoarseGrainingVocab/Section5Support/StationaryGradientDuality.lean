import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryWeakHodge

/-!
# Duality for strong stationary horizontal gradients

This file records the infinitesimal integration-by-parts identity for the
stationary translation action.  It is the generator-level algebra used in
the mollified curl-free half of the stationary Hodge calculation.

The route mirrors the Koopman duality calculation in
`Algsuperdiff/Section3/Provider/Corrector/MollifiedDecorrelation.lean`: move a
translation through the Hilbert pairing, differentiate the inverse orbit,
and use uniqueness of the derivative.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

/-- Pairing a strong horizontal orbit with a fixed scalar `L²` test
commutes with taking its coordinate derivative. -/
theorem HasHorizontalGradient.hasDerivAt_inner_koopman_left
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    (i : Fin d) (psi : ScalarL2 mu) :
    HasDerivAt
      (fun t : ℝ => inner ℝ
        (koopman (mu := mu) (t • (Pi.single i 1 : Vec d)) phi) psi)
      (inner ℝ (vectorL2Coord (mu := mu) i F) psi) 0 := by
  simpa only [real_inner_comm] using
    (innerSL ℝ psi).hasFDerivAt.comp_hasDerivAt 0 (hphi i)

/-- The same orbit derivative after moving the Koopman translation to the
right side of the pairing.  The inverse translation contributes the minus
sign. -/
theorem HasHorizontalGradient.hasDerivAt_inner_koopman_right
    (phi : ScalarL2 mu) {psi : ScalarL2 mu} {G : VectorL2 d mu}
    (hpsi : HasHorizontalGradient (mu := mu) psi G)
    (i : Fin d) :
    HasDerivAt
      (fun t : ℝ => inner ℝ phi
        (koopman (mu := mu) ((-t) • (Pi.single i 1 : Vec d)) psi))
      (-inner ℝ phi (vectorL2Coord (mu := mu) i G)) 0 := by
  have horbit : HasDerivAt
      (fun t : ℝ =>
        koopman (mu := mu) (t • (Pi.single i 1 : Vec d)) psi)
      (vectorL2Coord (mu := mu) i G) 0 := hpsi i
  have hneg : HasDerivAt
      (fun t : ℝ =>
        koopman (mu := mu) ((-t) • (Pi.single i 1 : Vec d)) psi)
      (-(vectorL2Coord (mu := mu) i G)) 0 := by
    have horbit' : HasDerivAt
        (fun t : ℝ =>
          koopman (mu := mu) (t • (Pi.single i 1 : Vec d)) psi)
        (vectorL2Coord (mu := mu) i G) (-(0 : ℝ)) := by
      simpa using horbit
    simpa [Function.comp_def] using
      horbit'.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_neg (0 : ℝ))
  simpa only [map_neg] using
    (innerSL ℝ phi).hasFDerivAt.comp_hasDerivAt 0 hneg

/-- Stationary integration by parts for two fields in the domain of the
strong horizontal gradient:

`<D_i phi, psi> = - <phi, D_i psi>`.
-/
theorem HasHorizontalGradient.inner_coord_eq_neg_inner_coord
    {phi psi : ScalarL2 mu} {F G : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    (hpsi : HasHorizontalGradient (mu := mu) psi G)
    (i : Fin d) :
    inner ℝ (vectorL2Coord (mu := mu) i F) psi =
      -inner ℝ phi (vectorL2Coord (mu := mu) i G) := by
  have hleft := hphi.hasDerivAt_inner_koopman_left i psi
  have hright := hpsi.hasDerivAt_inner_koopman_right phi i
  have horbit : (fun t : ℝ => inner ℝ
      (koopman (mu := mu) (t • (Pi.single i 1 : Vec d)) phi) psi) =
      fun t : ℝ => inner ℝ phi
        (koopman (mu := mu) ((-t) • (Pi.single i 1 : Vec d)) psi) := by
    funext t
    rw [inner_koopman_left]
    congr 2
    simp
  rw [horbit] at hleft
  exact hleft.unique hright

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary
