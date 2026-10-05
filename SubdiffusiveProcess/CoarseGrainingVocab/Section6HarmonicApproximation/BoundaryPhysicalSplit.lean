module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryWindowPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.WindowDomain

@[expose] public section

/-!
# Physical pricing of the boundary part of the cell split

The projected datum difference is transported back to the ambient solution.
When the neighbouring cell exits the ambient cube, the ambient structural
`H¹₀` witness is then priced by the boundary-window zero-set Poincare lemma.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The projected solution-minus-datum norm is controlled by the ambient
zero-trace witness on the fixed boundary window. -/
theorem cubeLpNorm_projectedDatumDifference_le_boundaryWindow
    {m k : ℤ} {q : Vec d}
    (u h : H1Function (openCubeSet (originCube d m)))
    (rho : H10Function (openCubeSet (originCube d m)))
    (hval : ∀ x, u.toFun x = h.toFun x + rho.toH1Function.toFun x)
    (hkm : k ≤ m) (hq : q ∈ cube d m)
    (hnot : ¬ translatedCube d (k - 1) q ⊆ cube d m)
    (u0 h0 : H1Function (openCubeSet (originCube d k)))
    (hu0 : ∀ x, u0.toFun x = u.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hh0 : ∀ x, h0.toFun x = h.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k)) :
    cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
        (fun x => u0.toFun x - h0.toFun x) ≤
      projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
          Real.sqrt ((volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        ∑ j : Fin d,
          (eLpNorm (fun x => rho.grad x j) 2
            (volume.restrict
              (translatedCube d (k + 1) q ∩ cube d m))).toReal := by
  classical
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let P : Set (Vec d) := translatedCube d k c
  let W : Set (Vec d) := translatedCube d (k + 1) q ∩ cube d m
  have hPset : P = translateSet c (openCubeSet (originCube d k)) := by
    dsimp [P]
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hWset : W = truncatedCube d m (k + 1) q := by
    rfl
  have hPsub : P ⊆ W := by
    have hbase := Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_truncatedCube
      (d := d) (m := m) (j := k + 1) q hq (by simpa using hkm)
    rw [show k + 1 - 1 = k by ring] at hbase
    rw [hWset]
    exact hbase
  have hPpos : 0 < (volume P).toReal := by
    rw [hPset, volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d k)
  have hrhoW : MemLp rho.toFun 2 (volume.restrict W) :=
    rho.toH1Function.memL2.mono_measure
      (Measure.restrict_mono_set volume (by
        rw [hWset]
        exact Section6ExcessDecay.truncatedCube_subset_cube d m (k + 1) q))
  have hmonoENN : eLpNorm rho.toFun 2 (volume.restrict P) ≤
      eLpNorm rho.toFun 2 (volume.restrict W) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hPsub)
  have hmono : (eLpNorm rho.toFun 2 (volume.restrict P)).toReal ≤
      (eLpNorm rho.toFun 2 (volume.restrict W)).toReal :=
    ENNReal.toReal_mono hrhoW.eLpNorm_ne_top hmonoENN
  have hframe : cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
      (fun x => u0.toFun x - h0.toFun x) = normalizedL2On P rho.toFun := by
    calc
      cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
          (fun x => u0.toFun x - h0.toFun x) =
          normalizedL2On (openCubeSet (originCube d k))
            (fun x => u0.toFun x - h0.toFun x) :=
        (normalizedL2On_openCubeSet_eq_cubeLpNorm (originCube d k)
          (u0.memL2.sub h0.memL2)).symm
      _ = normalizedL2On P rho.toFun := by
        unfold normalizedL2On
        rw [hPset, Ch01.volumeAverage_translateSet_eq_comp_addRight]
        congr 2
        funext x
        change (u0.toFun x - h0.toFun x) ^ 2 = rho.toFun (x + c) ^ 2
        rw [hu0 x, hh0 x, hval (x + c)]
        ring
  have hdict : normalizedL2On P rho.toFun =
      (eLpNorm rho.toFun 2 (volume.restrict P)).toReal /
        Real.sqrt ((volume P).toReal) :=
    normalizedL2On_eq_toReal_eLpNorm_div
      (rho.toH1Function.memL2.mono_measure
        (Measure.restrict_mono_set volume (hPsub.trans (by
          rw [hWset]
          exact Section6ExcessDecay.truncatedCube_subset_cube d m (k + 1) q))))
  have hPoin := eLpNorm_le_projectedBoundaryWindowPoincare hnot rho
  have hdiv : (eLpNorm rho.toFun 2 (volume.restrict P)).toReal /
        Real.sqrt ((volume P).toReal) ≤
      (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k *
          ∑ j : Fin d, (eLpNorm (fun x => rho.grad x j) 2
            (volume.restrict W)).toReal) /
        Real.sqrt ((volume P).toReal) := by
    exact div_le_div_of_nonneg_right (hmono.trans hPoin)
      (Real.sqrt_nonneg _)
  rw [hframe, hdict]
  refine hdiv.trans_eq ?_
  dsimp [P, W]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
