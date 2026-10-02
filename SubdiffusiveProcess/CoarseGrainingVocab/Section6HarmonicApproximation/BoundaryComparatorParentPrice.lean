import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryParentPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalMeanControl

/-!
# The projected physical carrier at the comparator-residue interface

This module inserts the Superdiffusion-style flat-comparator mean estimate
into the already landed projected parent decomposition.  The only unpriced
solution-dependent quantity left by this interface is the flat-comparator
residue itself; no boundary-window gradient estimate is used.

PROVENANCE: mirrors the interface of
`Algsuperdiff/Section4/Provider/ExcessDecay/ResidueInterface.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- The physical projected norm with its boundary scalar replaced by the
priced flat-comparator mean decomposition. -/
theorem exists_cubeLpNorm_projected_sub_dirichletSolution_le_comparatorPrices
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m k : ℤ} {q : Vec d} {U : Set (Vec d)} {s D : ℝ}
        {A : CoeffFamily d} {g0 : Vec d → Vec d}
        (v : DirichletForcedCubeSolution (originCube d k) A g0)
        (u h : H1Function (openCubeSet (originCube d m)))
        (u₀ h₀ : H1Function (openCubeSet (originCube d k)))
        (i : Fin d) (sg : ℝ),
        k < m → (sg = 1 ∨ sg = -1) →
        wellPlacedHalfGap m k < sg * q i →
        MemH10 (openCubeSet (originCube d m))
          (fun y => u.toFun y - h.toFun y) →
        v.boundaryData = h₀ →
        (∀ x, u₀.toFun x =
          u.toFun (x + Section6ExcessDecay.wellPlacedCentre q m k)) →
        (∀ x, h₀.toFun x =
          h.toFun (x + Section6ExcessDecay.wellPlacedCentre q m k)) →
        (∀ x, h₀.grad x =
          h.grad (x + Section6ExcessDecay.wellPlacedCentre q m k)) →
        translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k) ⊆ U →
        U ⊆ openCubeSet (originCube d m) →
        MeasurableSet U → 0 < volume U → volume U ≠ ⊤ →
        0 < (volume (translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q m k))).toReal →
        0 < s →
        (∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D) →
        fractionalSeminormOn U s h.grad ≠ ⊤ →
        let P := translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q m k)
        ∃ ubar hbar : H1Function
            (truncatedWindow
              (Section6ExcessDecay.wellPlacedCentre q m k) m k),
          IsUnitWeaklyHarmonicOn
              (truncatedWindow
                (Section6ExcessDecay.wellPlacedCentre q m k) m k) ubar ∧
          IsUnitWeaklyHarmonicOn
              (truncatedWindow
                (Section6ExcessDecay.wellPlacedCentre q m k) m k) hbar ∧
          MemH10
              (truncatedWindow
                (Section6ExcessDecay.wellPlacedCentre q m k) m k)
              (fun y => ubar.toFun y - u.toFun y) ∧
          MemH10
              (truncatedWindow
                (Section6ExcessDecay.wellPlacedCentre q m k) m k)
              (fun y => hbar.toFun y - h.toFun y) ∧
          normalizedL2On P (fun y => u.toFun y - ubar.toFun y) ≤
            flatComparatorPriceConst d * (3 : ℝ) ^ k *
              ∑ j : Fin d, normalizedL2On P (fun y => u.grad y j) ∧
          normalizedL2On P (fun y => h.toFun y - hbar.toFun y) ≤
            flatComparatorPriceConst d * (3 : ℝ) ^ k *
              ∑ j : Fin d, normalizedL2On P (fun y => h.grad y j) ∧
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
              (fun y => u₀.toFun y - v.toH1.toFun y) ≤
            2 * Real.sqrt ((volume U).toReal / (volume P).toReal) *
                normalizedL2On U
                  (fun y => u.toFun y - averageOn U u.toFun) +
              unitMeanZeroPoincareConst d * (3 : ℝ) ^ k * (d : ℝ) *
                Real.sqrt ((volume U).toReal / (volume P).toReal) *
                (D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
                    (volume U).toReal ^ (-(1 / 2 : ℝ)) *
                      (fractionalSeminormOn U s h.grad).toReal +
                  euclideanNorm (averageVecOn U h.grad)) +
              (1 + 2 * C) *
                (normalizedL2On P (fun y => u.toFun y - ubar.toFun y) +
                  normalizedL2On P (fun y => h.toFun y - hbar.toFun y)) +
              C * (normalizedL2On P
                    (fun y => u.toFun y - volumeAverage P u.toFun) +
                  normalizedL2On P
                    (fun y => h.toFun y - volumeAverage P h.toFun)) +
              cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
                (fun y => v.toH1.toFun y - h₀.toFun y) := by
  obtain ⟨C, hC0, hmean⟩ :=
    exists_physicalBoundaryMean_le_flatComparatorPrices d
  refine ⟨C, hC0, ?_⟩
  intro m k q U s D A g0 v u h u₀ h₀ i hsgn hkm hsg hover hdat hv
    hu₀ hh₀ hh₀grad hPsub hUsub hUmeas hU0 hUtop hPpos hs hdiam hfrac
  let P := translatedCube d k
    (Section6ExcessDecay.wellPlacedCentre q m k)
  obtain ⟨ubar, hbar, hubarHarm, hhbarHarm, hubarTrace, hhbarTrace,
      hubarPrice, hhbarPrice, hmeanPrice⟩ :=
    hmean m k q i hsgn u h hkm hsg hover hdat
  have hparent :=
    sqrt_projected_sub_dirichletSolution_le_windowPrices_add_meanDefect
      v u h u₀ h₀ hv hu₀ hh₀ hh₀grad hPsub hUsub hUmeas hU0 hUtop hPpos
        hs hdiam hfrac
  have hnorm :
      cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
          (fun y => u₀.toFun y - v.toH1.toFun y) =
        Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d k))
          (fun y => u₀.toFun y - v.toH1.toFun y)) := by
    have hmem : MemLp (fun y => u₀.toFun y - v.toH1.toFun y) 2
        (normalizedCubeMeasure (originCube d k)) := by
      simpa only [Pi.sub_apply] using
        u₀.memL2_normalizedCubeMeasure.sub
          v.toH1.memL2_normalizedCubeMeasure
    rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq
      (originCube d k) _ hmem]
    exact (Real.sqrt_sq (cubeLpNorm_nonneg _ _ _)).symm
  refine ⟨ubar, hbar, hubarHarm, hhbarHarm, hubarTrace, hhbarTrace,
    hubarPrice, hhbarPrice, ?_⟩
  rw [hnorm]
  linarith only [hparent, hmeanPrice]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
