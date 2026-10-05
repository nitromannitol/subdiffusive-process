module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteLocalTests
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevTestTranslation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicTestTranslation
@[expose] public section

/-! The full finite coefficient-test package transports to actual spatial sites, including both weighted masses and strict harmonic contraction. -/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem goodCube_finiteLocalTests_translate
    {d : ℕ} (z : Vec d) (a : Vec d → ℝ) (ha : Measurable a)
    (p A sigma eps epsH massFraction : ℝ) (hp : 0 < p) (clock : ℝ → ℝ)
    (G : Finset (ℤ × Vec d)) (Pairs : Set (Cube d × Cube d))
    (h : GoodCubeFiniteLocalTests (fun x => a (x + z))
      p A sigma eps epsH massFraction clock G Pairs) :
    GoodCubeFiniteLocalTests a p A sigma eps epsH massFraction clock
      (G.image (fun q => (q.1, q.2 + z)))
      ((fun q => ((q.1.1 + z, q.1.2), (q.2.1 + z, q.2.2))) '' Pairs) := by
  obtain ⟨hsob, htor, hmass, hhar⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    exact goodCube_sobolevDisplay_translate z (q'.2, (3 : ℝ)^q'.1) a ha p A hp clock
      (hsob q' hq')
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    simpa only [add_assoc] using! htor q' hq'
  · intro q hq r hr
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hr
    have hQ : MeasurableSet (cubeSet (r'.2, (3 : ℝ)^r'.1)) := measurableSet_cubeSet _
    have hQq : MeasurableSet (cubeSet (q'.2, (3 : ℝ)^q'.1)) := measurableSet_cubeSet _
    have hrEq : cubeSet (r'.2 + z, (3 : ℝ)^r'.1)
        = translateSet z (cubeSet (r'.2, (3 : ℝ)^r'.1)) :=
      goodCube_cubeSet_add_eq_translateSet (r'.2, (3 : ℝ)^r'.1) z
    have hqEq : cubeSet (q'.2 + z, (3 : ℝ)^q'.1)
        = translateSet z (cubeSet (q'.2, (3 : ℝ)^q'.1)) :=
      goodCube_cubeSet_add_eq_translateSet (q'.2, (3 : ℝ)^q'.1) z
    rw [hrEq, hqEq, goodCube_weightedMeasure_translateSet z _ hQ a,
      goodCube_weightedMeasure_translateSet z _ hQq a]
    exact hmass q' hq' r' hr'
  · refine ⟨?_⟩
    intro pair hpair h hh
    obtain ⟨c, hc, rfl⟩ := hpair
    rw [goodCube_cubeSet_add_eq_translateSet c.2 z] at hh
    have h1 := goodCube_harmonicContraction_translate z (cubeSet c.1) (cubeSet c.2) a epsH
      (hhar.contraction c hc) h hh
    rw [goodCube_cubeSet_add_eq_translateSet c.1 z, goodCube_cubeSet_add_eq_translateSet c.2 z]
    exact h1
/-- Native test images agree exactly with affine transport of the reference catalogue. -/
theorem goodCube_finiteLocalTests_native_translate
    {d : ℕ} (y : Vec d) (n : ℕ) (a : Vec d → ℝ) (ha : Measurable a)
    (p A sigma eps epsH massFraction : ℝ) (hp : 0 < p) (clock : ℝ → ℝ)
    (G : Finset (ℕ × Vec d)) (Pairs : Set (Cube d × Cube d))
    (h : GoodCubeFiniteLocalTests (fun x => a (x + y))
      p A sigma eps epsH massFraction clock
      (G.image (fun q => ((n : ℤ) - q.1, (3 : ℝ)^n • q.2)))
      (affinePairTransport (0 : Vec d) ((3 : ℝ)^n) '' Pairs)) :
    GoodCubeFiniteLocalTests a p A sigma eps epsH massFraction clock
      (G.image (fun q => ((n : ℤ) - q.1, y + (3 : ℝ)^n • q.2)))
      (affinePairTransport y ((3 : ℝ)^n) '' Pairs) := by
  have ht := goodCube_finiteLocalTests_translate y a ha p A sigma eps epsH massFraction
    hp clock _ _ h
  simpa only [Finset.image_image, Set.image_image, affinePairTransport, affineCubeTransport,
    zero_add, add_zero, Function.comp_def, add_comm] using! ht
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
