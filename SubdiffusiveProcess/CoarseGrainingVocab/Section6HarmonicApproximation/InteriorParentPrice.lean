module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2

@[expose] public section

/-!
# Parent-oscillation price for an interior projected cell

The projected origin-cube `L²` term is transported back to its physical cube
and compared with the containing manuscript window by the exact volume ratio.

The argument uses normalized-volume transport.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Physical-window price of the projected parent square. -/
theorem normalizedL2SqOnSet_projected_le_window
    {m k : ℤ} {q : Vec d} {U : Set (Vec d)}
    (u : H1Function (openCubeSet (originCube d m)))
    (u0 : H1Function (openCubeSet (originCube d k))) (c0 : ℝ)
    (hu0 : ∀ x, u0.toFun x = u.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hPsub : translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre q m k) ⊆ U)
    (hUsub : U ⊆ openCubeSet (originCube d m))
    (hUpos : 0 < (volume U).toReal)
    (hPpos : 0 < (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) :
    normalizedL2SqOnSet (openCubeSet (originCube d k))
        (fun x => u0.toFun x - c0) ≤
      ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        normalizedL2On U (fun x => u.toFun x - c0) ^ 2 := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let P : Set (Vec d) := translatedCube d k c
  have hPset : P = translateSet c (openCubeSet (originCube d k)) := by
    dsimp [P]
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hframe : cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
      (fun x => u0.toFun x - c0) = normalizedL2On P (fun x => u.toFun x - c0) := by
    calc
      cubeLpNorm (originCube d k) (2 : ℝ≥0∞) (fun x => u0.toFun x - c0) =
          normalizedL2On (openCubeSet (originCube d k))
            (fun x => u0.toFun x - c0) :=
        (normalizedL2On_openCubeSet_eq_cubeLpNorm (originCube d k)
          (u0.memL2.sub (memLp_const c0))).symm
      _ = normalizedL2On P (fun x => u.toFun x - c0) := by
        unfold normalizedL2On
        rw [hPset, Ch01.volumeAverage_translateSet_eq_comp_addRight]
        congr 2
        funext x
        change (u0.toFun x - c0) ^ 2 = (u.toFun (x + c) - c0) ^ 2
        rw [hu0 x]
  have hint : IntegrableOn (fun x => (u.toFun x - c0) ^ 2) U := by
    have hmem : MemLp (fun x => u.toFun x - c0) 2 (volume.restrict U) :=
      (u.memL2.sub (memLp_const c0)).mono_measure
        (Measure.restrict_mono_set volume hUsub)
    exact hmem.integrable_sq
  have hnorm := normalizedL2On_le_of_subset hPsub hUpos hPpos hint
  have hN : 0 ≤ normalizedL2On U (fun x => u.toFun x - c0) :=
    normalizedL2On_nonneg U _
  have hratio : 0 ≤ (volume U).toReal / (volume P).toReal := by positivity
  have hsquare := pow_le_pow_left₀ (normalizedL2On_nonneg P _) hnorm 2
  have hu0norm : MemLp (fun x => u0.toFun x - c0) 2
      (normalizedCubeMeasure (originCube d k)) := by
    simpa only [Pi.sub_apply] using!
      u0.memL2_normalizedCubeMeasure.sub (memLp_const c0)
  rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq
    (originCube d k) (fun x => u0.toFun x - c0)
      hu0norm, hframe]
  calc
    normalizedL2On P (fun x => u.toFun x - c0) ^ 2 ≤
        (Real.sqrt ((volume U).toReal / (volume P).toReal) *
          normalizedL2On U (fun x => u.toFun x - c0)) ^ 2 := hsquare
    _ = ((volume U).toReal / (volume P).toReal) *
          normalizedL2On U (fun x => u.toFun x - c0) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hratio]

/-- Unsquared companion of `normalizedL2SqOnSet_projected_le_window`, used by
the boundary normalization decomposition before the final square is taken. -/
theorem normalizedL2On_projected_le_window
    {m k : ℤ} {q : Vec d} {U : Set (Vec d)}
    (u : H1Function (openCubeSet (originCube d m)))
    (u0 : H1Function (openCubeSet (originCube d k))) (c0 : ℝ)
    (hu0 : ∀ x, u0.toFun x = u.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hPsub : translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre q m k) ⊆ U)
    (hUsub : U ⊆ openCubeSet (originCube d m))
    (hUpos : 0 < (volume U).toReal)
    (hPpos : 0 < (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) :
    normalizedL2On (openCubeSet (originCube d k))
        (fun x => u0.toFun x - c0) ≤
      Real.sqrt ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        normalizedL2On U (fun x => u.toFun x - c0) := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let P : Set (Vec d) := translatedCube d k c
  have hPset : P = translateSet c (openCubeSet (originCube d k)) := by
    dsimp [P]
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hframe : normalizedL2On (openCubeSet (originCube d k))
      (fun x => u0.toFun x - c0) = normalizedL2On P (fun x => u.toFun x - c0) := by
    unfold normalizedL2On
    rw [hPset, Ch01.volumeAverage_translateSet_eq_comp_addRight]
    congr 2
    funext x
    change (u0.toFun x - c0) ^ 2 = (u.toFun (x + c) - c0) ^ 2
    rw [hu0 x]
  have hint : IntegrableOn (fun x => (u.toFun x - c0) ^ 2) U := by
    have hmem : MemLp (fun x => u.toFun x - c0) 2 (volume.restrict U) :=
      (u.memL2.sub (memLp_const c0)).mono_measure
        (Measure.restrict_mono_set volume hUsub)
    exact hmem.integrable_sq
  rw [hframe]
  exact normalizedL2On_le_of_subset hPsub hUpos hPpos hint

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
