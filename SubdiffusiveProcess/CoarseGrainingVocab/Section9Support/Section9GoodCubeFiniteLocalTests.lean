import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeLocalTestEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionTest
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicContraction
/-! The finite Sobolev, torsion, mass and strict harmonic tests are local to the coefficient observation that contains their physical cubes. -/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
structure GoodCubeFiniteLocalTests {d : ℕ} (a : Vec d → ℝ)
    (p A sigma eps epsH massFraction : ℝ) (clock : ℝ → ℝ)
    (G : Finset (ℤ × Vec d)) (Pairs : Set (Cube d × Cube d)) : Prop where
  sobolev : ∀ q ∈ G,
    GoodCubeSobolevDisplay a p A clock (q.2, (3 : ℝ)^q.1)
  torsion : ∀ q ∈ G,
    GoodCubeTorsionComparisonTest (originCube d q.1) (fun x => a (x + q.2)) sigma eps
  mass : ∀ q ∈ G, ∀ r ∈ G,
    ENNReal.ofReal massFraction * weightedMeasure a (cubeSet (r.2, (3 : ℝ)^r.1)) ≤
      weightedMeasure a (cubeSet (q.2, (3 : ℝ)^q.1))
  harmonic : LocalHarmonicOscillation a epsH Pairs

private theorem goodCube_finiteLocalTests_congr_coeff_aux
    {d : ℕ} {a b : Vec d → ℝ} {S : Set (Vec d)}
    (hab : Set.EqOn a b S) (p A sigma eps epsH massFraction : ℝ) (clock : ℝ → ℝ)
    (G : Finset (ℤ × Vec d)) (Pairs : Set (Cube d × Cube d))
    (hinside : ∀ q ∈ G, cubeSet (q.2, (3 : ℝ)^q.1) ⊆ S)
    (hpairs : ∀ q ∈ Pairs, cubeSet q.2 ⊆ S)
    (h : GoodCubeFiniteLocalTests a p A sigma eps epsH massFraction clock G Pairs) :
    GoodCubeFiniteLocalTests b p A sigma eps epsH massFraction clock G Pairs := by
  obtain ⟨hsob, htor, hmass, hhar⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    have hae : a =ᵐ[volume.restrict (cubeSet (q.2, (3 : ℝ)^q.1))] b := by
      filter_upwards [ae_restrict_mem (measurableSet_cubeSet (q.2, (3 : ℝ)^q.1))] with x hx
      exact hab (hinside q hq hx)
    exact (goodCube_sobolevDisplay_congr_coeff (q.2, (3 : ℝ)^q.1) hae p A clock).mp (hsob q hq)
  · intro q hq
    refine (goodCube_torsionComparisonTest_translated_congr_coeff
      (originCube d q.1) q.2 hab ?_ sigma eps).mp (htor q hq)
    intro x hx
    have h1 : q.2 + x ∈ translatedCube d q.1 q.2 := by
      show q.2 + x ∈ (fun y => q.2 + y) '' openCubeSet (originCube d q.1)
      exact ⟨x, hx, rfl⟩
    rw [translatedCube_eq_cubeSet] at h1
    have h2 := hinside q hq h1
    rwa [add_comm] at h2
  · intro q hq r hr
    have hae : a =ᵐ[volume.restrict (cubeSet (r.2, (3 : ℝ)^r.1))] b := by
      filter_upwards [ae_restrict_mem (measurableSet_cubeSet (r.2, (3 : ℝ)^r.1))] with x hx
      exact hab (hinside r hr hx)
    have hmeas := goodCube_weightedMeasure_restrict_congr hae
    have hmassEq : weightedMeasure a (cubeSet (r.2, (3 : ℝ)^r.1))
        = weightedMeasure b (cubeSet (r.2, (3 : ℝ)^r.1)) := by
      have h := congrArg (fun mu : Measure (Vec d) => mu Set.univ) hmeas
      simpa only [Measure.restrict_apply_univ] using h
    have haeQ : a =ᵐ[volume.restrict (cubeSet (q.2, (3 : ℝ)^q.1))] b := by
      filter_upwards [ae_restrict_mem (measurableSet_cubeSet (q.2, (3 : ℝ)^q.1))] with x hx
      exact hab (hinside q hq hx)
    have hmassEqQ : weightedMeasure a (cubeSet (q.2, (3 : ℝ)^q.1))
        = weightedMeasure b (cubeSet (q.2, (3 : ℝ)^q.1)) := by
      have h := congrArg (fun mu : Measure (Vec d) => mu Set.univ)
        (goodCube_weightedMeasure_restrict_congr haeQ)
      simpa only [Measure.restrict_apply_univ] using h
    rw [← hmassEq, ← hmassEqQ]
    exact hmass q hq r hr
  · exact (goodCube_localHarmonicOscillation_congr_coeff hab hpairs).mp hhar

theorem goodCube_finiteLocalTests_congr_coeff
    {d : ℕ} {a b : Vec d → ℝ} {S : Set (Vec d)}
    (hab : Set.EqOn a b S) (p A sigma eps epsH massFraction : ℝ) (clock : ℝ → ℝ)
    (G : Finset (ℤ × Vec d)) (Pairs : Set (Cube d × Cube d))
    (hinside : ∀ q ∈ G, cubeSet (q.2, (3 : ℝ)^q.1) ⊆ S)
    (hpairs : ∀ q ∈ Pairs, cubeSet q.2 ⊆ S) :
    GoodCubeFiniteLocalTests a p A sigma eps epsH massFraction clock G Pairs ↔
      GoodCubeFiniteLocalTests b p A sigma eps epsH massFraction clock G Pairs := by
  constructor
  · exact goodCube_finiteLocalTests_congr_coeff_aux hab p A sigma eps epsH massFraction
      clock G Pairs hinside hpairs
  · exact goodCube_finiteLocalTests_congr_coeff_aux hab.symm p A sigma eps epsH massFraction
      clock G Pairs hinside hpairs
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
