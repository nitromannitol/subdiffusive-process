module

public import SubdiffusiveProcess.Analysis.RawLp

public import Mathlib
public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import MarkovProcess.Lifetime.ExitTimeStopping
public import SubdiffusiveProcess.Section9.ShapeCubeGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.Lattice
public import SubdiffusiveProcess.Frozen.Assumptions.PotentialSample
public import SubdiffusiveProcess.Frozen.Assumptions.LocalSigma
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

def CoefficientOn {d : ℕ} (U : Set (Vec d)) (a : Vec d → ℝ) : Prop :=
  AEStronglyMeasurable a (volume.restrict U) ∧
    ∃ lo hi : ℝ, 0 < lo ∧ ∀ᵐ x ∂(volume.restrict U), lo ≤ a x ∧ a x ≤ hi



def CoefficientC11On {d : ℕ} (U : Set (Vec d)) (a : Vec d → ℝ) : Prop :=
  ∃ Da : Vec d → (Vec d →L[ℝ] ℝ),
    (∀ x ∈ U, HasFDerivAt a (Da x) x) ∧
      ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
        ∃ C : NNReal, LipschitzOnWith C Da K

abbrev Path (d : ℕ) := LifetimePath (Vec d)

def position {d : ℕ} (t : NNReal) (w : Path d) : Vec d :=
  (LifetimePath.coordinate t w).elim id (fun _ => 0)

def weightedMeasure {d : ℕ} (rho : Vec d → ℝ) : Measure (Vec d) :=
  volume.withDensity (fun x => ENNReal.ofReal (rho x))

def meanExit {d : ℕ} (law : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (x : Vec d) : ENNReal :=
  ∫⁻ w, LifetimePath.exitTime U w ∂law x

def lpSq {d : ℕ} (rho : Vec d → ℝ) (U : Set (Vec d)) (p : ℝ)
    (f : Vec d → ℝ) : ENNReal :=
  (SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal p)
    ((volume.withDensity (fun x => ENNReal.ofReal (rho x))).restrict U)) ^ (2 : ℕ)

def energy {d : ℕ} (c : Vec d → ℝ) (U : Set (Vec d)) (f : H1Function U) : ℝ :=
  ∫ x in U, c x * vecDot (f.grad x) (f.grad x)

def IsKilledDensity {d : ℕ} (law : Kernel (Vec d) (LifetimePath (Vec d)))
    (rho : Vec d → ℝ) (U : Set (Vec d)) (p : ℝ → Vec d → Vec d → ℝ) : Prop :=
  (∀ t > 0, Measurable (Function.uncurry (p t))) ∧
    (∀ t > 0, ∀ x ∈ U, ∀ y ∈ U, 0 ≤ p t x y) ∧
    (∀ t > 0, ∀ x ∈ U, ∀ B : Set (Vec d), MeasurableSet B →
      law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
        LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B}
        = ∫⁻ y in B ∩ U, ENNReal.ofReal (p t x y)
          ∂(volume.withDensity (fun y => ENNReal.ofReal (rho y))))

def StrongMarkov {d : ℕ} (law : Kernel (Vec d) (Path d)) : Prop :=
  (∀ x, law x univ = 1) ∧
  (∀ x, ∀ᵐ w ∂law x, LifetimePath.coordinate 0 w = Cemetery.alive x) ∧
  ∀ x, ∀ T : Path d → ENNReal, ∀ hT : IsStoppingTime LifetimePath.canonicalFiltration T,
    ∀ B : Set (Path d), MeasurableSet[hT.measurableSpace] B →
      ∀ g : Path d → ENNReal, Measurable g →
        (∫⁻ w in B ∩ {w | T w < w.lifetime},
            g (LifetimePath.shift (T w).toNNReal w) ∂law x) =
        ∫⁻ w in B ∩ {w | T w < w.lifetime},
            (∫⁻ v, g v ∂law (position (T w).toNNReal w)) ∂law x

noncomputable def killedResolvent {d : ℕ} (law : Kernel (Vec d) (Path d)) (U : Set (Vec d))
    (s : ℝ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  s⁻¹ * ∫ t in Set.Ioi (0:ℝ),
      Real.exp (-t/s) *
        ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w},
          f (position (Real.toNNReal t) w) ∂law x

noncomputable def LocalDiffusion {d : ℕ} (c rho : Vec d → ℝ)
    (law : Kernel (Vec d) (Path d)) : Prop :=
  StrongMarkov law ∧
    (∀ K : Set (Vec d), IsCompact K →
      CoefficientOn K c ∧ CoefficientOn K rho) ∧
    ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
      ∀ s : ℝ, 0 < s → ∀ f : Vec d → ℝ,
        MemLp f 2 ((weightedMeasure rho).restrict U) →
        ∃ u : H10Function U,
          (∀ᵐ x ∂(weightedMeasure rho).restrict U,
              u.toH1Function.toFun x = killedResolvent law U s f x) ∧
          SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
            c rho s⁻¹ U u.toH1Function (fun x => s⁻¹ * f x)



def HasContinuousKilledDensityOn {d : ℕ} (rho : Vec d → ℝ) (law : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) : Prop :=
  ∃ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p ∧
    ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ U ×ˢ U)

/-- `LocalDiffusion` together with a continuous killed density on every bounded
open set: the companion predicate of freeze package 17 §3.1 route (i-b).

`LocalDiffusion`'s resolvent clause is only `a.e.` in the starting point, so a
law altered at a single starting point still satisfies `LocalDiffusion` while
having an infinite mean exit time there; the Section 9 anchors whose
conclusions are pointwise in the starting point therefore take this predicate
instead (freeze package 17 §2.2, freeze package 16 decision E4). -/
def LocalDiffusionData {d : ℕ} (c rho : Vec d → ℝ) (law : Kernel (Vec d) (Path d)) : Prop :=
  LocalDiffusion c rho law ∧
    ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
      HasContinuousKilledDensityOn rho law U

def oscillation {d : ℕ} (U : Set (Vec d)) (h : Vec d → ℝ) : ENNReal :=
  ⨆ x ∈ U, ⨆ y ∈ U, ENNReal.ofReal |h x - h y|

def SobolevAssumption {d : ℕ} (c rho : Vec d → ℝ) (U : Set (Vec d)) (p A F : ℝ) : Prop :=
  ∀ f : H10Function U,
    lpSq rho U p f.toH1Function.toFun ≤
      ENNReal.ofReal (A * ((weightedMeasure rho U).toReal) ^ (-(1 - 2 / p))) *
        (lpSq rho U 2 f.toH1Function.toFun + ENNReal.ofReal (F * energy c U f.toH1Function))

def PoincareAssumption {d : ℕ} (c rho : Vec d → ℝ) (U : Set (Vec d)) (A F : ℝ) : Prop :=
  ∀ f : H10Function U,
    lpSq rho U 2 f.toH1Function.toFun ≤
      ENNReal.ofReal (A * F * energy c U f.toH1Function)

def Crossing {d : ℕ} (mu : Measure (Path d)) (c0 F0 t : ℝ) (n : ℕ)
    (event : Set (Path d)) : Prop :=
  ∃ T S : ℕ → Path d → ENNReal,
    (∀ i < n, IsStoppingTime LifetimePath.canonicalFiltration (T i) ∧
      IsStoppingTime LifetimePath.canonicalFiltration (S i)) ∧
    (∀ i < n, ∀ w, T i w ≤ S i w) ∧
    (∀ i, i + 1 < n → ∀ w, S i w ≤ T (i + 1) w) ∧
    (event ⊆ {w | n = 0 ∨ S (n - 1) w ≤ ENNReal.ofReal t}) ∧
    ∀ i < n, ∀ hT : IsStoppingTime LifetimePath.canonicalFiltration (T i),
      ∀ B : Set (Path d), MeasurableSet[hT.measurableSpace] B →
        B ⊆ {w | T i w < ∞} →
        ENNReal.ofReal c0 * mu B ≤
          mu (B ∩ {w | ENNReal.ofReal (c0 * F0) ≤ S i w - T i w})

noncomputable def WeakHarmonic {d : ℕ} (c : Vec d → ℝ) (U : Set (Vec d))
    (h : Vec d → ℝ) : Prop :=
  ContinuousOn h U ∧
    ∀ W : Set (Vec d), IsOpen W → IsCompact (closure W) → closure W ⊆ U →
      ∃ u : H1Function W,
        (∀ᵐ x ∂(volume.restrict W), u.toFun x = h x) ∧
        ∀ phi : H10Function W,
          (∫ x in W, c x * vecDot (u.grad x) (phi.toH1Function.grad x)) = 0

/-- A cube of the fixed finite family of translated triadic grids with offsets
`grid`: centre `y`, side `side`.  The translation of the scale-`3 ^ m` grid
scales with the grid, so the centres are `3 ^ m * (g + k)`; with an absolute
translation `g + k * 3 ^ m` the middle-sixteenth covering property below is
unsatisfiable at large scales (P-370). -/
def IsGridCube {d : ℕ} (grid : Finset (Vec d)) (y : Vec d) (side : ℝ) : Prop :=
  ∃ g ∈ grid, ∃ m : ℤ, ∃ k : Fin d → ℤ,
    side = (3 : ℝ) ^ m ∧ y = fun i => (3 : ℝ) ^ m * (g i + (k i : ℝ))

/-- The middle sixteenths of the family cover every smaller cube with Lebesgue
number `lam`. -/
def HasMiddleSixteenthCover {d : ℕ} (grid : Finset (Vec d)) (lam : ℝ) : Prop :=
  1 ≤ lam ∧ ∀ (x : Vec d) (rho : ℝ), 0 < rho →
    ∃ y side : _, IsGridCube grid y side ∧ rho ≤ side ∧ side ≤ lam * rho ∧
      SubdiffusiveProcess.Section9.centeredAxisCube x rho ⊆ SubdiffusiveProcess.Section9.centeredAxisCube y (side / 16)



def section9CrossingSteps (_d : ℕ) : ℕ := 1

/-- The pinned value of the shared Section 9 step count (`D-137`). -/
theorem section9CrossingSteps_eq_one (d : ℕ) : section9CrossingSteps d = 1 := rfl

/-- The step count is at least one (`D-132(C)`; the pin that keeps clauses (i)
and (ii) of the version 2.1 percolation anchor from being vacuous).  Since
`D-137` it is an immediate consequence of `section9CrossingSteps_eq_one`. -/
theorem one_le_section9CrossingSteps (d : ℕ) : 1 ≤ section9CrossingSteps d :=
  le_rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)

/-- A cube of the local families, recorded as `(centre, side length)`. -/
abbrev Cube (d : ℕ) := Vec d × ℝ

/-- The point set of a family cube. -/
def cubeSet {d : ℕ} (Q : Cube d) : Set (Vec d) := centeredAxisCube Q.1 Q.2

/-- The middle quarter `V` of a family cube. -/
def middleQuarter {d : ℕ} (U : Cube d) : Set (Vec d) := centeredAxisCube U.1 (U.2 / 4)

/-- Compact inclusion `B' ⋐ B` between family cubes. -/
def CompactlyInside {d : ℕ} (Q R : Cube d) : Prop := closure (cubeSet Q) ⊆ cubeSet R

/-- The physical centre of the scale-`n` cube attached to a lattice site. -/
def goodCubeCentre {d : ℕ} (n : ℕ) (z : Lattice d) : Vec d :=
  fun i => (z i : ℝ) * (3 : ℝ) ^ n

/-- The sigma-field generated by the shell field `g_k` on a box. -/
def shellLocalSigma {d : ℕ} (k : ℕ) (B : Set (Vec d)) :
    MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  MeasurableSpace.comap (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k)
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma B)

/-- The good-cube event attached to a site: none of the layer events occurs. -/
def goodCubeEvent {d : ℕ} {Omega : Type}
    (E : ℕ → Lattice d → Set Omega) (z : Lattice d) : Set Omega :=
  ⋂ j : ℕ, (E j z)ᶜ



structure IsLocalCubeGeometry {d : ℕ} (grid : Finset (Vec d)) (j1 j2 : ℕ)
    (U : Cube d) (Pfam : Set (Cube d × Cube d)) (Qfam Afam : Set (Cube d)) : Prop where
  finite_Q : Qfam.Finite
  finite_P : Pfam.Finite
  self_mem : U ∈ Qfam
  side_pos : ∀ Q ∈ Qfam, 0 < Q.2
  gridded : ∀ Q ∈ Qfam, IsGridCube grid Q.1 Q.2
  pair_mem : ∀ p ∈ Pfam, p.1 ∈ Qfam ∧ p.2 ∈ Qfam
  pair_nested : ∀ p ∈ Pfam, CompactlyInside p.1 p.2
  pair_middle_half : ∀ p ∈ Pfam, cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2)
  pair_in_half : ∀ p ∈ Pfam, cubeSet p.2 ⊆ centeredAxisCube U.1 (U.2 / 2)
  pair_outer_side : ∀ p ∈ Pfam, p.2.2 = (3 : ℝ) ^ (-(j1 : ℤ)) * U.2
  pair_inner_side : ∀ p ∈ Pfam, p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2
  cover : middleQuarter U ⊆ ⋃ p ∈ Pfam, cubeSet p.1
  A_subset : Afam ⊆ Qfam
  A_in_quarter : ∀ A ∈ Afam, cubeSet A ⊆ middleQuarter U
  chain : ∀ x ∈ middleQuarter U, ∀ y ∈ middleQuarter U,
    ∃ (k : ℕ) (ch : ℕ → Cube d),
      (∀ i ≤ k, ∃ p ∈ Pfam, ch i = p.1) ∧
      x ∈ cubeSet (ch 0) ∧ y ∈ cubeSet (ch k) ∧
      ∀ i < k, ∃ A ∈ Afam,
        cubeSet A ⊆ cubeSet (ch i) ∩ cubeSet (ch (i + 1)) ∩ middleQuarter U



structure LocalTorsionEstimates {d : ℕ} (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d))
    (clock : ℝ → ℝ) (p0 cc CC : ℝ) (U : Cube d) (Qfam Afam : Set (Cube d)) : Prop where
  exit_lower : ∀ x ∈ middleQuarter U,
    ENNReal.ofReal (cc * clock U.2) ≤ meanExit law (cubeSet U) x
  exit_upper : ∀ x ∈ cubeSet U,
    meanExit law (cubeSet U) x ≤ ENNReal.ofReal (CC * clock U.2)
  descendant : ∀ B' ∈ Qfam, ∀ B ∈ Qfam, CompactlyInside B' B →
    (∀ x ∈ cubeSet B', ENNReal.ofReal (cc * clock B.2) ≤ meanExit law (cubeSet B) x) ∧
    (∀ x ∈ cubeSet B, meanExit law (cubeSet B) x ≤ ENNReal.ofReal (CC * clock B.2))
  mass_quarter :
    ENNReal.ofReal cc * weightedMeasure a (cubeSet U) ≤ weightedMeasure a (middleQuarter U)
  mass_descendant : ∀ B' ∈ Qfam, ∀ B ∈ Qfam, CompactlyInside B' B →
    ENNReal.ofReal cc * weightedMeasure a (cubeSet B) ≤ weightedMeasure a (cubeSet B')
  mass_overlap : ∀ A ∈ Afam,
    ENNReal.ofReal cc * weightedMeasure a (cubeSet U) ≤ weightedMeasure a (cubeSet A)
  sobolev : ∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
    lpSq a (cubeSet Q) p0 f.toH1Function.toFun ≤
      ENNReal.ofReal CC * weightedMeasure a (cubeSet Q) ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)



structure LocalHarmonicOscillation {d : ℕ} (a : Vec d → ℝ) (eps0 : ℝ)
    (Pfam : Set (Cube d × Cube d)) : Prop where
  contraction : ∀ p ∈ Pfam, ∀ h : Vec d → ℝ, WeakHarmonic a (cubeSet p.2) h →
    oscillation (cubeSet p.1) h ≤ ENNReal.ofReal eps0 * oscillation (cubeSet p.2) h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
