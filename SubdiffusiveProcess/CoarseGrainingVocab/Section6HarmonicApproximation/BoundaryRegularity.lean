module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS
public import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingForcing

@[expose] public section

/-!
# Fractional regularity of the projected boundary datum

This file adds the quantitative regularity fields to the projected rough
Dirichlet construction.  It is deliberately separate from the trace module:
the latter is purely `H¹`, while this layer is the v5 inhomogeneous datum.

PROVENANCE: mirrors the split between
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryDatumTransport.lean` and
`CoarseIndexBridges.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

private noncomputable def wspFieldOfFull {Q : TriadicCube d}
    {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := f
  euclideanMemLp := hf.1
  euclideanMemWsp := hf.2

omit [NeZero d] in
@[simp] private theorem wspFieldOfFull_toField {Q : TriadicCube d}
    {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    (wspFieldOfFull hf).toField = f := rfl

private theorem forceBesovRegularity_of_full {Q : TriadicCube d}
    {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    ForceBesovRegularity Q s.1 f := by
  have hsob := cubeEuclideanWspField_forceSobolevRegularity s (wspFieldOfFull hf)
  simpa using hsob.toForceBesovRegularity s.2.1 s.2.2.le

private theorem forceBesovRegularity_neg_of_full {Q : TriadicCube d}
    {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    ForceBesovRegularity Q s.1 (fun x => -f x) := by
  let F := negCubeEuclideanWspField (wspFieldOfFull hf)
  have hsob := cubeEuclideanWspField_forceSobolevRegularity s F
  simpa [F] using hsob.toForceBesovRegularity s.2.1 s.2.2.le

/-- The projected rough Dirichlet datum, now carrying the exact positive-Besov
regularity hypotheses consumed by `exists_boundaryCaccioppoliEnergy_withBoundaryDatum`.
-/
theorem exists_projectedBoundaryDatum_regular
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d)
    (hdir : IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (originCube d (m : ℤ)) u h g)
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g)
    (hh : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad)
    (hkm : k ≤ (m : ℤ)) :
    let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
    let Q := originCube d k
    let A := aCutoffFamily M L (translatePotentialSample c omega)
    ∃ g0 : Vec d → Vec d,
      ∃ u0 h0 : H1Function (openCubeSet Q),
      ∃ v : DirichletForcedCubeSolution Q A (fun x => -g0 x),
        (∀ x, g0 x = g (x + c)) ∧
        (∀ x, u0.toFun x = u.toFun (x + c)) ∧
        Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
          FiniteLpExponent.two (fun x => g (x + c)) ∧
        (∀ x, u0.grad x = u.grad (x + c)) ∧
        IsForcedEquation Q A u0 (fun x => -g0 x) ∧
        v.boundaryData = h0 ∧
        (∀ x, h0.toFun x = h.toFun (x + c)) ∧
        (∀ x, h0.grad x = h.grad (x + c)) ∧
        Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
          FiniteLpExponent.two (fun x => h.grad (x + c)) ∧
        Ch01.LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (openCubeAtScale (q - c) (k - 1))
          (fun y => u0.toFun y - v.toH1.toFun y) ∧
        ForceBesovRegularity Q sOrder.1 (fun x => -g0 x) ∧
        ForceBesovRegularity Q sOrder.1 (dirichletBoundaryGradientField v) := by
  dsimp only
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  have hP : translateSet c (openCubeSet Q) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    have heq : translateSet c (openCubeSet Q) = translatedCube d k c := by
      rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
    rw [heq]
    exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm
  have hg0 : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q sOrder FiniteLpExponent.two (fun x => g (x + c)) :=
    memCubeEuclideanFullWsp_translate_of_subset Q (originCube d (m : ℤ)) c
      sOrder FiniteLpExponent.two g hP hg
  have hh0 : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q sOrder FiniteLpExponent.two (fun x => h.grad (x + c)) :=
    memCubeEuclideanFullWsp_translate_of_subset Q (originCube d (m : ℤ)) c
      sOrder FiniteLpExponent.two h.grad hP hh
  have hgL2 : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) g :=
    by
      have hgNorm : MemLp g 2 (normalizedCubeMeasure (originCube d (m : ℤ))) :=
        Ch03.ABK26.MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hg
      have hgCube := memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure
        (originCube d (m : ℤ)) hgNorm
      simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet
          (originCube d (m : ℤ))] using hgCube
  obtain ⟨g0, u0, h0, v, hg0point, hu0val, hu0grad, hu0, hvh0, hh0val,
      hh0grad, htrace⟩ :=
    exists_projectedBoundaryDatum M L omega m k q u h g hdir hgL2 hkm
  have hg0eq : g0 = fun x => g (x + c) := funext hg0point
  have hgreg : ForceBesovRegularity Q sOrder.1 (fun x => -g0 x) := by
    rw [hg0eq]
    exact forceBesovRegularity_neg_of_full hg0
  have hhreg : ForceBesovRegularity Q sOrder.1
      (dirichletBoundaryGradientField v) := by
    rw [dirichletBoundaryGradientField, hvh0]
    have heq : h0.grad = fun x => h.grad (x + c) := funext hh0grad
    rw [heq]
    exact forceBesovRegularity_of_full hh0
  exact ⟨g0, u0, h0, v, hg0point, hu0val, hg0, hu0grad, hu0, hvh0, hh0val,
    hh0grad, hh0, htrace, hgreg, hhreg⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
