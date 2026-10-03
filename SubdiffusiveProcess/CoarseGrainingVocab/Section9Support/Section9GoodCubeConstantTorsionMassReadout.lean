module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteLocalTests
@[expose] public section

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
attribute [local instance] Classical.propDecidable

theorem goodCube_finiteLocalTests_sobolev_mass_readout
    {d : ℕ} (a : Vec d → ℝ) (p A sigma eps epsH massFraction c : ℝ)
    (clock : ℝ → ℝ) (G : Finset (ℤ × Vec d)) (Pairs : Set (Cube d × Cube d))
    (Qfam : Set (Cube d)) (U : Cube d)
    (htest : GoodCubeFiniteLocalTests a p A sigma eps epsH massFraction clock G Pairs)
    (hfamily : ∀ Q ∈ Qfam, ∃ q ∈ G, ((q.2, (3 : ℝ)^q.1) : Cube d) = Q)
    (hparent : ∃ q ∈ G, ((q.2, (3 : ℝ)^q.1) : Cube d) = U)
    (hquarter : ∃ q ∈ G, cubeSet (q.2, (3 : ℝ)^q.1) ⊆ middleQuarter U)
    (hc : c ≤ massFraction) :
    (∀ Q ∈ Qfam, GoodCubeSobolevDisplay a p A clock Q) ∧
      ENNReal.ofReal c * weightedMeasure a (cubeSet U) ≤
        weightedMeasure a (middleQuarter U) ∧
      ∀ Q ∈ Qfam, ∀ R ∈ Qfam,
        ENNReal.ofReal c * weightedMeasure a (cubeSet R) ≤
          weightedMeasure a (cubeSet Q) := by
  obtain ⟨qU, qUin, hqU⟩ := hparent
  obtain ⟨qQ, qQin, hqQ⟩ := hquarter
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨q, hqin, hq⟩ := hfamily Q hQ
    rw [← hq]
    exact htest.sobolev q hqin
  · calc ENNReal.ofReal c * weightedMeasure a (cubeSet U)
        ≤ ENNReal.ofReal massFraction * weightedMeasure a (cubeSet U) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hc) _
      _ ≤ weightedMeasure a (cubeSet (qQ.2, (3 : ℝ)^qQ.1)) :=
          by simpa only [hqU] using htest.mass qQ qQin qU qUin
      _ ≤ weightedMeasure a (middleQuarter U) := measure_mono hqQ
  · intro Q hQ R hR
    obtain ⟨q, hqin, hq⟩ := hfamily Q hQ
    obtain ⟨r, hrin, hr⟩ := hfamily R hR
    calc ENNReal.ofReal c * weightedMeasure a (cubeSet R)
          ≤ ENNReal.ofReal massFraction * weightedMeasure a (cubeSet R) :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal hc) _
        _ ≤ weightedMeasure a (cubeSet (q.2, (3 : ℝ)^q.1)) :=
            by simpa only [hr] using htest.mass q hqin r hrin
        _ = weightedMeasure a (cubeSet Q) := by rw [hq]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
