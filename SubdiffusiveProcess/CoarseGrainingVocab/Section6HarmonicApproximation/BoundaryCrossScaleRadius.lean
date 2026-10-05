module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScaleCutoff
public import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalPatchCutoff
public import Homogenization.Deterministic.CoarseCaccioppoli.RadiusIteration
public import Homogenization.Deterministic.CoarseCaccioppoli.TriadicScale

@[expose] public section

/-!
# Radius-sequence form of the cross-scale boundary test

The weak equation lives on an ambient cube `Q`, while the deterministic
radius sequence is based on the projected boundary cube `R`.  This module
supplies the nonnegativity, boundedness, support, and one-step coercive-test
facts on that exact pair of carriers.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The ambient-normalized cross-scale energy profile is nonnegative. -/
theorem boundaryCrossScaleEnergyProfile_nonneg
    {Q R : TriadicCube d} {center : Vec d} {energy : Vec d → ℝ}
    (henergy : ∀ x ∈ openCubeSet Q, 0 ≤ energy x) (rho : ℝ) :
    0 ≤ boundaryCrossScaleEnergyProfile Q R center rho energy := by
  apply volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet Q)
  intro x hxQ
  by_cases hx : x ∈ coarseCaccioppoliLocalClosedCube R center rho
  · simpa [Set.indicator_of_mem hx] using henergy x hxQ
  · simp [Set.indicator_of_notMem hx]

/-- The full ambient energy is a uniform upper bound for the cross-scale
radius profile. -/
theorem boundaryCrossScaleEnergyProfile_boundedAbove
    {Q R : TriadicCube d} {center : Vec d} {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x)
    (henergy_int : IntegrableOn energy (openCubeSet Q)) :
    CoarseCaccioppoliRadiusBoundedAbove
      (fun rho ↦ boundaryCrossScaleEnergyProfile Q R center rho energy) := by
  refine ⟨volumeAverage (openCubeSet Q) energy, ?_⟩
  intro rho _ _
  apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
    (henergy_int.indicator
      (measurableSet_coarseCaccioppoliLocalClosedCube R center rho))
    henergy_int
  intro x hxQ
  by_cases hx : x ∈ coarseCaccioppoliLocalClosedCube R center rho
  · simp [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    exact henergy_nonneg x hxQ

/-- On every consecutive pair of deterministic radii, the canonical cutoff
is supported inside the local trace window and the localized direct test gives
the exact `4/14/8` inequality. -/
theorem boundaryCrossScaleEnergyProfile_radiusSequence_le_aCutoff_coerciveTerms
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube R center 1)
      (fun y ↦ u.toFun y - h.toFun y)) (j : ℕ) :
    let rhoInner := coarseCaccioppoliRadiusSequence j
    let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
    boundaryCrossScaleEnergyProfile Q R center rhoInner
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      4 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) +
        14 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveCutoffDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y ↦ u.toFun y - h.toFun y)) +
        8 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) := by
  dsimp only
  have hinner : 0 < coarseCaccioppoliRadiusSequence j :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3)
      (coarseCaccioppoliRadiusSequence_mem_Icc j).1
  have hlt : coarseCaccioppoliRadiusSequence j <
      coarseCaccioppoliRadiusSequence (j + 1) :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
  have houter : coarseCaccioppoliLocalClosedCube R center
      (coarseCaccioppoliRadiusSequence (j + 1)) ⊆
        coarseCaccioppoliLocalOpenCube R center 1 :=
    coarseCaccioppoliLocalClosedCube_subset_localOpenCube_one_of_lt_one
      (coarseCaccioppoliRadiusSequence_lt_one (j + 1))
  exact boundaryCrossScaleEnergyProfile_le_aCutoff_coerciveTerms
    M L omega hweak hg hzero hinner hlt houter

/-- Radius iteration for the cross-scale nonzero-datum test.  The only
remaining premise is the scale-by-scale price of the three explicit coercive
densities.  In particular, cutoff support, localized trace, integrability,
profile boundedness, and the infinite radius summation are all discharged. -/
theorem boundaryCrossScaleEnergyProfile_oneThird_le_of_sequenceDensityPrices
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube R center 1)
      (fun y ↦ u.toFun y - h.toFun y))
    {A beta : ℝ} (hA : 0 ≤ A) (hbeta : 0 ≤ beta)
    (hprices : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      4 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) +
        14 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveCutoffDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y ↦ u.toFun y - h.toFun y)) +
        8 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) ≤
        (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
        A * Real.rpow (rhoOuter - rhoInner) (-beta)) :
    boundaryCrossScaleEnergyProfile Q R center (1 / 3 : ℝ)
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      A * coarseCaccioppoliRadiusIterationConst beta := by
  let energy : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)
  let F : ℝ → ℝ := fun rho ↦
    boundaryCrossScaleEnergyProfile Q R center rho energy
  have henergy_nonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x := by
    intro x hx
    exact mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg _)
  have henergy_int : IntegrableOn energy (openCubeSet Q) := by
    simpa only [energy] using integrableOn_aCutoff_energy M L omega Q u
  have hbounded : CoarseCaccioppoliRadiusBoundedAbove F := by
    simpa only [F] using
      boundaryCrossScaleEnergyProfile_boundedAbove henergy_nonneg henergy_int
  have hrec : CoarseCaccioppoliRadiusSequenceRecurrence F A beta := by
    intro j
    have htest :=
      boundaryCrossScaleEnergyProfile_radiusSequence_le_aCutoff_coerciveTerms
        M L omega hweak hg hzero j
    have hprice := hprices j
    dsimp only at htest hprice
    exact htest.trans hprice
  simpa only [F, energy] using
    coarseCaccioppoli_radius_iteration_of_sequenceRecurrence
      hbeta hA hbounded hrec

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
