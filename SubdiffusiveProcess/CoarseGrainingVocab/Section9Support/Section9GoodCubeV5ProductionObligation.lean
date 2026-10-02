import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5TestTransfer
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceTemplate




set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- One selected catalogue's unconditional robust tests and the layer-zero tail.
`J` and all analytic tolerances belong to the selected finite template. -/
def GoodCubeV5RobustLocalEvent (d : ℕ)
    (c C epsilon p A epsL2 epsH massFraction eps0 : ℝ) (J : ℕ)
    (G : Finset (ℕ × Vec d)) (Pairs Pfam0 : Set (Cube d × Cube d))
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ)) :
    Prop :=
  ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
    M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤ ENNReal.ofReal
      (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2))))) ∧
    ∀ omega : PotentialSample d,
      omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z →
      GoodCubeV5RobustFiniteLocalTests (aCutoff M n omega) (nativeBox n 1 z)
        epsilon p A (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction
        (Section7Process.timeScale (ahom M))
        (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2)))
        (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) '' Pairs) ∧
      GoodCubeV5RobustHarmonicOscillation (aCutoff M n omega) (nativeBox n 1 z)
        epsilon eps0 (goodCubeReferencePairs Pfam0 n z)

/-- The corrected splice uses the raw local event before a diffusion-law guard.
The existing measurable enlargement is handled by passing `homraw` to this
theorem.  The cutoff-law package is not an argument. -/
theorem goodCubeV5_anchored_tests_of_local_event {d : ℕ}
    {c C eps1 epsilon p A epsL2 epsH massFraction eps0 : ℝ} {J : ℕ}
    {G : Finset (ℕ × Vec d)} {Pairs Pfam0 : Set (Cube d × Cube d)}
    {bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ)}
    (hlocal : GoodCubeV5RobustLocalEvent d c C epsilon p A epsL2 epsH massFraction
      eps0 J G Pairs Pfam0 bad)
    (heps1 : 0 < eps1) (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (hbudget : goodCubeV5TailBudget eps1 ≤ Real.log (1 + epsilon))
    (M : GMCModel d) (hdelta : M.delta ≤ c) (n : ℕ) (z : Lattice d)
    (omega : AnchoredC11Sample d)
    (homraw : omega.1 ∈ goodCubeEvent
      (goodCubeEventField n 1 eps1 (coefficientLocalBadEvent M n 1 (bad M n))) z)
    (hinside : ∀ q ∈ G.image
        (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2)),
      cubeSet (q.2, (3 : ℝ)^q.1) ⊆ nativeBox n 1 z)
    (hpairs : ∀ q ∈ affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) '' Pairs,
      cubeSet q.2 ⊆ nativeBox n 1 z)
    (hpfam : ∀ q ∈ goodCubeReferencePairs Pfam0 n z, cubeSet q.2 ⊆ nativeBox n 1 z) :
    GoodCubeFiniteLocalTests (aAnchored M omega) p A
        (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction
        (Section7Process.timeScale (ahom M))
        (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2)))
        (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) '' Pairs) ∧
      LocalHarmonicOscillation (aAnchored M omega) eps0
        (goodCubeReferencePairs Pfam0 n z) := by
  obtain ⟨htests, hosc⟩ := (hlocal M hdelta n z).2 omega.1
    (not_mem_layerZero_of_goodCubeEvent homraw)
  exact goodCubeAnchoredTestTransferAll d eps1 epsilon heps1 hepsilon hhalf hbudget
    M n z omega (coefficientLocalBadEvent M n 1 (bad M n)) homraw p A
    (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction eps0
    (Section7Process.timeScale (ahom M)) _ _ _ hinside hpairs hpfam htests hosc

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
