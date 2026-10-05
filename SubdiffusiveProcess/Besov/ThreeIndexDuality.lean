module

public import SubdiffusiveProcess.Besov.TruncationNorm
public import SubdiffusiveProcess.Besov.TruncationLimit

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- Full three-index Besov duality for integrable data and an integrable product. -/
theorem threeIndex_pairing_le {d : ℕ} (m : ℤ) (s : ℝ) (hs : 0 < s) (hsOne : s ≤ 1)
    (q r : ℝ≥0∞) (hq : 1 ≤ q) (hr : 1 ≤ r) (f g : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet (originCube d m)))
    (hg : IntegrableOn g (cubeSet (originCube d m)))
    (hfg : IntegrableOn (fun x => f x * g x) (cubeSet (originCube d m))) :
    ENNReal.ofReal |cubeBesovPairing (originCube d m) f g| ≤
      ENNReal.ofReal ((2 * pairingConstant d) * s⁻¹) *
        (besovNorm d m s 1 (ENNReal.conjExponent q) (ENNReal.conjExponent r) g *
          negativeBesovNorm d m s r q f) := by
  let : ENNReal.HolderConjugate q (ENNReal.conjExponent q) :=
    ENNReal.HolderConjugate.conjExponent hq
  let : ENNReal.HolderConjugate r (ENNReal.conjExponent r) :=
    ENNReal.HolderConjugate.conjExponent hr
  have hq' : 1 ≤ ENNReal.conjExponent q := ENNReal.HolderConjugate.one_le _ q
  have hr' : 1 ≤ ENNReal.conjExponent r := ENNReal.HolderConjugate.one_le _ r
  have hbound : ∀ n, ENNReal.ofReal |cubeBesovPairing (originCube d m) f
      (centeredTruncation (originCube d m) n g)| ≤
      ENNReal.ofReal ((2 * pairingConstant d) * s⁻¹) *
        (besovNorm d m s 1 (ENNReal.conjExponent q) (ENNReal.conjExponent r) g *
          negativeBesovNorm d m s r q f) := by
    intro n
    have hgtr := centeredTruncation_integrable (originCube d m) n g hg
    have hbounded := bounded_pairing_le m s hs hsOne q r hq hr f
      (centeredTruncation (originCube d m) n g) hf hgtr
      ((n : ℝ) + 1 + |cubeAverage (originCube d m) g -
        cubeAverage (originCube d m) (clippedPart (originCube d m) n g)|)
      (by positivity) (fun x _ => centeredTruncation_bound _ n g x)
    have hn := centeredTruncation_besovNorm_le m n s
      (ENNReal.conjExponent q) (ENNReal.conjExponent r) hq' hr' g hg
    have he : ENNReal.ofReal ((2 * pairingConstant d) * s⁻¹) =
        2 * ENNReal.ofReal (pairingConstant d * s⁻¹) := by
      rw [show (2 * pairingConstant d) * s⁻¹ = 2 * (pairingConstant d * s⁻¹) by ring,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    exact hbounded.trans ((mul_le_mul_right (mul_le_mul' hn le_rfl) _).trans_eq (by
      rw [he]
      ac_rfl))
  have hlim := tendsto_pairing_centeredTruncation (originCube d m) f g hf hg hfg
  exact le_of_tendsto (ENNReal.tendsto_ofReal hlim.abs) (Filter.Eventually.of_forall hbound)

end SubdiffusiveProcess.Besov
