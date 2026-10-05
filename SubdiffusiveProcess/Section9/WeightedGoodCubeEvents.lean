module

public import SubdiffusiveProcess.GoodCube.RobustAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Providers.Section9.WeightedGoodCubeEventsV4
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.EventIndependence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.Model.ACutoff
public import SubdiffusiveProcess.Vocab.Ahom
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

/-!
# Good cubes: the coupled local estimates

The local analytic conclusions cannot hold, with one positive mass constant `c`,
for every admissible family on an arbitrary finite grid: `IsLocalCubeGeometry`
permits arbitrarily small concentric triadic cubes. This obstruction is proved
in `Section9GoodCubeMassObstruction` and `Section9GoodCubeMassProviderObstruction`.

The coupled local estimates deliver `LocalTorsionEstimates` together with
`LocalHarmonicOscillation` in one existential. They also supply
`TranslationInvariantEventLaw`, consumed by
`SubdiffusiveProcess.Section9.weighted_multiscale_percolation`, the smallness choice
`C·3^{-3j₁/2} ≤ η/2`, and existence of admissible local geometry for the
produced `j₁, j₂`. One reference template `grid0, Pfam0, Qfam0, Afam0` is
chosen before the model, and every native cube receives its literal translated
and triadically dilated image. The diffusion carrier is `LocalDiffusionData`.

Grid offsets must be distinguished from points. Transporting offsets by

```lean
let grid : ℕ → Lattice d → Finset (Vec d) := fun n z =>
  Finset.image (fun x => goodCubeCentre n z + (3 : ℝ) ^ n • x) grid0
```

and asking for `IsLocalCubeGeometry (grid n z) …` treats offsets as points.
An offset of `IsGridCube` is dimensionless: grid-cube centres are
`3 ^ m * (g + k)`, so `g` is measured in units of the side. The fixed family
of translated triadic grids therefore does not depend on `(n, z)`, and the
geometry clause is `IsLocalCubeGeometry grid0 …`.

The point transport sends an offset `g` to `3 ^ n * (z + g)`, whose class
modulo `1` is `3 ^ n · g`. Thus that transport works only for reference offsets
closed under multiplication by `3` modulo `1`. Offsets with a denominator
divisible by `3` make that geometry unsatisfiable
(`goodCube_isGridCube_pointTransport_refutation`); imposing outer pair cubes
on the `(B·a)/8` lattice avoids this obstruction but unnecessarily restricts
the reference geometry. The offset transport requires no arithmetic condition
on the offsets: `goodCube_isGridCube_affine`.

The full coupled conclusion retains the native geometry, all event
distributions and independence clauses, and the cutoff analytic estimates.
It additionally requires the tolerance bound and the anchored coupled
conclusion, including the special case `theta = 1`.
The strengthened coupled conclusion is supplied by
`weighted_good_cube_events_v5_robust`.
-/

theorem SubdiffusiveProcess.Section9.weighted_good_cube_events
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
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
        ∀ n : ℕ,
        ∃ E : ℕ → Lattice d → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
          (∀ z : Lattice d,
            MeasurableSet[restrictedCoefficientSigma
              (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
                _root_.SubdiffusiveProcess.Model.aCutoff M n omega)
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
                LocalDiffusionData (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
                  (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) law →
                LocalTorsionEstimates (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
                    eps0 (Pfam n z)) ∧
          (∀ z : Lattice d,
            ∀ omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d,
              (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) ∈ goodCubeEvent E z →
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (_root_.SubdiffusiveProcess.Model.aAnchored M omega)
                  (_root_.SubdiffusiveProcess.Model.aAnchored M omega) law →
                LocalTorsionEstimates (_root_.SubdiffusiveProcess.Model.aAnchored M omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (_root_.SubdiffusiveProcess.Model.aAnchored M omega)
                    eps0 (Pfam n z))
 := _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.RobustGoodCube.weighted_good_cube_events_v5_robust
    d hd eta heta0 heta1
