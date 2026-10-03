module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineResidual

@[expose] public section

/-!
# Coupled affine/residual half absorption

The two affine-correction bulks must not be estimated separately: either
estimate introduces the uncontrolled energy of the affine competitor.  The
correct cancellation is performed at the energy level.  Split both the inner
and outer physical energies against the same canonical affine harmonic lift,
and spend only one eighth of the residual outer energy.  The two splits then
leave one half of the physical outer energy and a single multiple of the
canonical lift energy.

PROVENANCE: this is the coupled affine-energy cancellation implicit in
`Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitHarmonic.lean` and
`BoundaryAssemblyEnergy.lean`.  Here the canonical lift is coefficient
harmonic, so its energy is subsequently read through the GMC coarse matrix.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Scalar core of the coupled absorption.  The coefficient `5 / 2` is the
literal cost of using the same affine lift in the inner and outer energy
splits. -/
theorem affineResidual_eighth_to_physical_half
    {Einner Eouter EinnerRes EouterRes Ev B : ℝ}
    (hinner : Einner ≤ 2 * EinnerRes + 2 * Ev)
    (hres : EinnerRes ≤ (1 / 8 : ℝ) * EouterRes + B)
    (houter : EouterRes ≤ 2 * Eouter + 2 * Ev) :
    Einner ≤ (1 / 2 : ℝ) * Eouter + (5 / 2 : ℝ) * Ev + 2 * B := by
  linarith only [hinner, hres, houter]

/-- A one-eighth consecutive-radius estimate for the affine residual becomes
a one-half estimate for the physical solution.  Crucially, the affine
competitor itself never occurs: only the energy of its canonical harmonic
extension survives. -/
theorem boundaryCrossScaleEnergyProfile_physical_half_of_affineResidual_eighth
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter B : ℝ}
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = uRes.grad x + v.grad x)
    (hres :
      boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 8 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B) :
    boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) +
        (5 / 2 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v + 2 * B := by
  have hinner := boundaryCrossScaleEnergyProfile_aCutoff_le_residual_add_affine
    M L omega Q R center rhoInner u uRes v hgrad
  have hgradReverse : ∀ x, uRes.grad x = u.grad x + (-v).grad x := by
    intro x
    rw [H1Function.neg_grad, hgrad x]
    simp
  have houterNeg := boundaryCrossScaleEnergyProfile_aCutoff_le_residual_add_affine
    M L omega Q R center rhoOuter uRes u (-v) hgradReverse
  have henergyNeg : localizedCoeffEnergyValue (openCubeSet Q)
      ((aCutoffFamily M L omega).coeffOn Q) (-v) =
      localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) v := by
    unfold localizedCoeffEnergyValue
    simp [H1Function.neg_grad, matVecMul_neg, vecDot_neg_left,
      vecDot_neg_right]
  rw [henergyNeg] at houterNeg
  exact affineResidual_eighth_to_physical_half hinner hres houterNeg

/-- Radius-iteration endpoint of the coupled cancellation.  A residual
one-eighth recurrence is enough: after the two physical/residual energy
splits it is a physical one-half recurrence.  The canonical lift is charged
once per radius step and is absorbed into the same nonnegative gap weight,
so it remains an additive dimensional energy rather than acquiring an
inverse power of the fractional order. -/
theorem boundaryCrossScaleEnergyProfile_oneThird_le_of_affineResidual_eighth
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d)
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = uRes.grad x + v.grad x)
    {A beta : ℝ} (hA : 0 ≤ A) (hbeta : 0 ≤ beta)
    (hres : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 8 : ℝ) *
            boundaryCrossScaleEnergyProfile Q R center rhoOuter (fun x ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (uRes.grad x)) +
          A * Real.rpow (rhoOuter - rhoInner) (-beta)) :
    boundaryCrossScaleEnergyProfile Q R center (1 / 3 : ℝ) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      ((5 / 2 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v + 2 * A) *
        coarseCaccioppoliRadiusIterationConst beta := by
  let energy : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  let F : ℝ → ℝ := fun rho ↦
    boundaryCrossScaleEnergyProfile Q R center rho energy
  let Ev := localizedCoeffEnergyValue (openCubeSet Q)
    ((aCutoffFamily M L omega).coeffOn Q) v
  let B := (5 / 2 : ℝ) * Ev + 2 * A
  have hEv : 0 ≤ Ev := by
    dsimp only [Ev]
    exact localizedCoeffEnergyValue_openCubeSet_nonneg Q
      (aCutoffFamily M L omega) v
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have henergyNonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x := by
    intro x _
    exact mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg _)
  have henergyInt : MeasureTheory.IntegrableOn energy (openCubeSet Q) := by
    simpa only [energy] using integrableOn_aCutoff_energy M L omega Q u
  have hbounded : CoarseCaccioppoliRadiusBoundedAbove F := by
    simpa only [F] using
      boundaryCrossScaleEnergyProfile_boundedAbove henergyNonneg henergyInt
  have hrec : CoarseCaccioppoliRadiusSequenceRecurrence F B beta := by
    intro j
    let rhoInner := coarseCaccioppoliRadiusSequence j
    let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
    have hresj := hres j
    dsimp only at hresj
    have hphysical :=
      boundaryCrossScaleEnergyProfile_physical_half_of_affineResidual_eighth
        M L omega Q R center u uRes v hgrad hresj
    have hgapPos : 0 < rhoOuter - rhoInner := by
      dsimp only [rhoInner, rhoOuter]
      exact sub_pos.mpr
        (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j))
    have hgapOne : rhoOuter - rhoInner ≤ 1 := by
      have hinner0 : 0 ≤ rhoInner := by
        dsimp only [rhoInner]
        exact (by norm_num : (0 : ℝ) ≤ 1 / 3).trans
          (coarseCaccioppoliRadiusSequence_mem_Icc j).1
      have houter1 : rhoOuter ≤ 1 := by
        dsimp only [rhoOuter]
        exact (coarseCaccioppoliRadiusSequence_mem_Icc (j + 1)).2
      linarith
    have hweight : 1 ≤ Real.rpow (rhoOuter - rhoInner) (-beta) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hgapPos hgapOne
        (neg_nonpos.mpr hbeta)
    have hEvWeight : (5 / 2 : ℝ) * Ev ≤
        (5 / 2 : ℝ) * Ev *
          Real.rpow (rhoOuter - rhoInner) (-beta) := by
      exact le_mul_of_one_le_right (mul_nonneg (by norm_num) hEv) hweight
    dsimp only [F, energy, B, Ev, rhoInner, rhoOuter]
    calc
      _ ≤ (1 / 2 : ℝ) *
            boundaryCrossScaleEnergyProfile Q R center
              (coarseCaccioppoliRadiusSequence (j + 1)) (fun x ↦
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.grad x)) +
          (5 / 2 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
              ((aCutoffFamily M L omega).coeffOn Q) v +
            2 * (A * Real.rpow
              (coarseCaccioppoliRadiusSequence (j + 1) -
                coarseCaccioppoliRadiusSequence j) (-beta)) := hphysical
      _ ≤ (1 / 2 : ℝ) *
            boundaryCrossScaleEnergyProfile Q R center
              (coarseCaccioppoliRadiusSequence (j + 1)) (fun x ↦
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.grad x)) +
          ((5 / 2 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
              ((aCutoffFamily M L omega).coeffOn Q) v + 2 * A) *
            Real.rpow
              (coarseCaccioppoliRadiusSequence (j + 1) -
                coarseCaccioppoliRadiusSequence j) (-beta) := by
        dsimp only [Ev, rhoInner, rhoOuter] at hEvWeight
        nlinarith only [hEvWeight]
  simpa only [F, energy, B, Ev] using
    coarseCaccioppoli_radius_iteration_of_sequenceRecurrence
      hbeta hB hbounded hrec

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
