module

public import SubdiffusiveProcess.GoodCube.RobustAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Providers.Section9.WeightedGoodCubeEventsV4
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.EventIndependence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.Frozen.Assumptions.ACutoff
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab (restrictedCoefficientSigma)
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section





theorem SubdiffusiveProcess.Frozen.Section9.weighted_good_cube_events
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∃ (c C eps0 p0 : ℝ) (Cdep j1 j2 : ℕ),
      0 < c ∧ 0 < C ∧ 0 < eps0 ∧ eps0 ≤ eta / 2 ∧ 2 < p0 ∧
      C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
      ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        let transportCube : ℕ → Lattice d → Cube d → Cube d := fun n z Q =>
          (goodCubeCentre n z + (3 : ℝ) ^ n • Q.1, (3 : ℝ) ^ n * Q.2)
        let Pfam : ℕ → Lattice d → Set (Cube d × Cube d) := fun n z =>
          (fun p => (transportCube n z p.1, transportCube n z p.2)) '' Pfam0
        let Qfam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Qfam0
        let Afam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Afam0
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
            (Pfam n z) (Qfam n z) (Afam n z)) ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
        ∀ n : ℕ,
        ∃ E : ℕ → Lattice d → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ z : Lattice d,
            MeasurableSet[restrictedCoefficientSigma
              (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n))] (E 0 z)) ∧
          (∀ j : ℕ, 1 ≤ j → ∀ z : Lattice d,
            MeasurableSet[shellLocalSigma (n + j)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)))] (E j z)) ∧
          (∀ (j : ℕ) (z : Lattice d),
            M.P.toMeasure (E j z) ≤
              ENNReal.ofReal (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
                (3 : ℝ) ^ (3 * (j : ℝ) / 2))))) ∧
          IndependentEventScales M.P.toMeasure E ∧
          MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep * 3 ^ j) E ∧
          TranslationInvariantEventLaw M.P.toMeasure E ∧
          (∀ z : Lattice d,
            ∀ omega ∈ goodCubeEvent E z,
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) law →
                LocalTorsionEstimates (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega)
                    eps0 (Pfam n z)) ∧
          (∀ z : Lattice d,
            ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
              (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ∈ goodCubeEvent E z →
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega)
                  (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega) law →
                LocalTorsionEstimates (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega)
                    eps0 (Pfam n z))

 := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Opus55.weighted_good_cube_events_v5_robust
    d hd eta heta0 heta1
