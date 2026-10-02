import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergyReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryRegularity
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli

/-!
# Interior energy on one projected physical cell

This is the non-touching companion of `BoundaryCellReadout`: translate the
ambient equation to the well-placed cube, subtract the ambient-window mean,
apply interior Caccioppoli at `(1/2,s/2)`, and read the core energy back on the
physical scale-`k-2` cell.

PROVENANCE: mirrors the composition of `CaccioppoliInteriorDatum.lean` and
`CaccioppoliInteriorEnergy.lean` in Algsuperdiff.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Mean-subtracted interior Caccioppoli on a projected cell, in the original
physical coefficient field. -/
theorem exists_projectedInteriorCellEnergy_readout (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
        (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        sOrder.1 ≤ 1 / 4 → k ≤ (m : ℤ) → q ∈ cube d (m : ℤ) →
        openCubeAtScale
            (q - Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) (k - 1) ⊆
          openCubeSet (originCube d k) →
        ∃ g0 : Vec d → Vec d,
          ∃ u0 : H1Function (openCubeSet (originCube d k)),
            (∀ x, g0 x = g (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d k) sOrder
              FiniteLpExponent.two (fun x => g (x +
                Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            (∀ x, u0.toFun x = u.toFun (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            IsForcedEquation (originCube d k)
                (aCutoffFamily M L
                  (translatePotentialSample
                    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                u0 (fun x => -g0 x) ∧
            ForceBesovRegularity (originCube d k) sOrder.1 (fun x => -g0 x) ∧
            normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
                (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.grad x)) ≤
              (81 : ℝ) ^ d *
                (caccioppoliWithRHSPrefactor C (originCube d k)
                    (aCutoffFamily M L
                      (translatePotentialSample
                        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                    (1 / 2) (sOrder.1 / 2) *
                  (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                      (aCutoffFamily M L
                        (translatePotentialSample
                          (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)) *
                    Real.rpow (3 : ℝ) (-2 * (((originCube d k).scale : ℤ) : ℝ)) *
                    normalizedL2SqOnSet (openCubeSet (originCube d k))
                      (fun y => u0.toFun y - c0) +
                  Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                    Real.rpow
                      (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                        (aCutoffFamily M L
                          (translatePotentialSample
                            (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)))
                      (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo
                      (originCube d k) sOrder.1 (fun x => -g0 x) ^ 2)) := by
  obtain ⟨C, hC, hinterior⟩ := exists_interior_caccioppoli_quarter_subConst d
  refine ⟨C, hC, ?_⟩
  intro M L omega m k q sOrder u h g c0 hdir hg hh hs4 hkm hq hpatch
  obtain ⟨g0, u0, _h0, _v, hg0, hu0val, hgLocal, hu0, heq, _hv,
      _hh0val, _hh0, _hhLocal, _htrace, hgReg, _hhReg⟩ :=
    exists_projectedBoundaryDatum_regular M L omega m k q sOrder u h g
      hdir hg hh hkm
  have hbound := hinterior u0 c0 heq
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by linarith only [sOrder.2.1] : 0 < sOrder.1 / 2)
    (by linarith only [hs4] : sOrder.1 / 2 ≤ 1 / 4)
    (by linarith only [sOrder.2.2] : (1 / 2 : ℝ) + sOrder.1 / 2 < 1)
    hpatch (by simpa [show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hgReg)
  have hread := normalizedCutoffEnergy_truncatedCube_le_projectedCore
    M L omega hq hkm u u0 hu0
  have hfactor : (0 : ℝ) ≤ (81 : ℝ) ^ d := by positivity
  have hfinal := hread.trans (mul_le_mul_of_nonneg_left hbound hfactor)
  refine ⟨g0, u0, hg0, hgLocal, hu0val, heq, hgReg, ?_⟩
  simpa [show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
