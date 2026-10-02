import SubdiffusiveProcess.Besov.FinitePairing

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- Bounded data allow passage from the finite-depth pairing to the integral pairing. -/
theorem bounded_pairing_le {d : ℕ} (m : ℤ) (s : ℝ) (hs : 0 < s) (hsOne : s ≤ 1)
    (q r : ℝ≥0∞) (hq : 1 ≤ q) (hr : 1 ≤ r) (f g : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet (originCube d m)))
    (hg : IntegrableOn g (cubeSet (originCube d m))) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ cubeSet (originCube d m), |g x| ≤ M) :
    ENNReal.ofReal |cubeBesovPairing (originCube d m) f g| ≤
      ENNReal.ofReal (pairingConstant d * s⁻¹) *
        (besovNorm d m s 1 (ENNReal.conjExponent q) (ENNReal.conjExponent r) g *
          negativeBesovNorm d m s r q f) := by
  have hlim := tendsto_cubeBesovPairing_projection_right_of_integrableOn_of_bounded
    (originCube d m) f g M hf hg hM hbound
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim.abs)
  exact Filter.Eventually.of_forall fun n => pairing_projection_le m (n + 1) s hs hsOne q r hq hr f g hf hg

end SubdiffusiveProcess.Besov
