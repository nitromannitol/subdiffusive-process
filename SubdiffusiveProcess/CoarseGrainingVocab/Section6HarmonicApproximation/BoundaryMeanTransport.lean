module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanZeroPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorParentPrice
public import Homogenization.Sobolev.FiniteLpCoordinate

@[expose] public section

/-!
# Transport of the boundary normalization defect

The scalar isolated in `BoundaryMeanDefect` is transported from the projected
origin frame to the literal physical projected cube.  No estimate is made in
this file.

the frame identity in the mean-control section of

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}



theorem sum_normalizedL2On_coord_le_dimension_mul_vector
    {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W)) :
    ∑ i : Fin d, normalizedL2On W (fun x => F x i) ≤
      (d : ℝ) * vectorNormalizedL2On W F := by
  have hcoordMem : ∀ i : Fin d,
      MemLp (fun x => F x i) 2 (volume.restrict W) := by
    intro i
    apply hF.mono
    · exact ((continuous_apply i).comp
        (HilbertVec.continuousLinearEquivVec d).continuous).comp_aestronglyMeasurable hF.aestronglyMeasurable
    · filter_upwards with x
      simpa only [Real.norm_eq_abs, ← euclideanNorm_eq_norm_ofVec] using
          abs_coordinate_le_euclideanNorm (F x) i
  have hnormMem : MemLp (fun x => euclideanNorm (F x)) 2
      (volume.restrict W) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using hF.norm
  have hterm : ∀ i : Fin d,
      normalizedL2On W (fun x => F x i) ≤ vectorNormalizedL2On W F := by
    intro i
    rw [Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div (hcoordMem i)]
    rw [show vectorNormalizedL2On W F =
        (eLpNorm (fun x => euclideanNorm (F x)) 2
          (volume.restrict W)).toReal / Real.sqrt ((volume W).toReal) by
      exact Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div hnormMem]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply ENNReal.toReal_mono hnormMem.eLpNorm_ne_top
    calc
      eLpNorm (fun x => F x i) 2 (volume.restrict W) ≤
          eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) :=
        coordinate_eLpNorm_le_euclidean
          (volume.restrict W) FiniteLpExponent.two F i
      _ = eLpNorm (fun x => euclideanNorm (F x)) 2 (volume.restrict W) := by
        simpa only [euclideanNorm_eq_norm_ofVec] using
          (eLpNorm_norm (p := 2) (μ := volume.restrict W)
            (fun x => HilbertVec.ofVec (F x)) hF.aestronglyMeasurable).symm
  calc
    ∑ i : Fin d, normalizedL2On W (fun x => F x i) ≤
        ∑ _i : Fin d, vectorNormalizedL2On W F :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * vectorNormalizedL2On W F := by simp

/-- The projected mean defect is exactly the physical mean of `u-h` on the
well-placed cube. -/
theorem volumeAverage_projected_sub_eq_physical
    {m k : ℤ} {q : Vec d}
    (u h : H1Function (openCubeSet (originCube d m)))
    (u₀ h₀ : H1Function (openCubeSet (originCube d k)))
    (hu₀ : ∀ x, u₀.toFun x = u.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hh₀ : ∀ x, h₀.toFun x = h.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k)) :
    volumeAverage (openCubeSet (originCube d k))
        (fun x => u₀.toFun x - h₀.toFun x) =
      volumeAverage
        (translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q m k))
        (fun x => u.toFun x - h.toFun x) := by
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q m k
  have hset : translatedCube d k c =
      translateSet c (openCubeSet (originCube d k)) := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  rw [hset, Ch01.volumeAverage_translateSet_eq_comp_addRight]
  congr 1
  funext x
  rw [hu₀ x, hh₀ x]

/-- One projected boundary-gradient coordinate transported to an ambient
window.  The square-root volume ratio is the exact normalized-measure cost. -/
theorem normalizedL2On_projected_grad_coord_le_window
    {m k : ℤ} {q : Vec d} {U : Set (Vec d)}
    (h : H1Function (openCubeSet (originCube d m)))
    (h₀ : H1Function (openCubeSet (originCube d k)))
    (hh₀ : ∀ x, h₀.grad x = h.grad
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (i : Fin d)
    (hPsub : translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre q m k) ⊆ U)
    (hUsub : U ⊆ openCubeSet (originCube d m))
    (hUpos : 0 < (volume U).toReal)
    (hPpos : 0 < (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) :
    normalizedL2On (openCubeSet (originCube d k)) (fun x => h₀.grad x i) ≤
      Real.sqrt ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        normalizedL2On U (fun x => h.grad x i) := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let P : Set (Vec d) := translatedCube d k c
  have hPset : P = translateSet c (openCubeSet (originCube d k)) := by
    dsimp [P]
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hframe : normalizedL2On (openCubeSet (originCube d k))
      (fun x => h₀.grad x i) = normalizedL2On P (fun x => h.grad x i) := by
    unfold normalizedL2On
    rw [hPset, Ch01.volumeAverage_translateSet_eq_comp_addRight]
    congr 2
    funext x
    have hi := congrFun (hh₀ x) i
    simpa only [c] using congrArg (fun r : ℝ => r ^ 2) hi
  have hint : IntegrableOn (fun x => (h.grad x i) ^ 2) U := by
    have hmem : MemLp (fun x => h.grad x i) 2 (volume.restrict U) :=
      (h.gradMemL2 i).mono_measure (Measure.restrict_mono_set volume hUsub)
    exact hmem.integrable_sq
  rw [hframe]
  exact Section6Iteration.normalizedL2On_le_of_subset hPsub hUpos hPpos hint

/-- The complete coordinate sum in the projected mean-zero Poincare estimate
is transported to a single Euclidean normalized `L²` norm on the ambient
window. -/
theorem sum_normalizedL2On_projected_grad_le_window_vector
    {m k : ℤ} {q : Vec d} {U : Set (Vec d)}
    (h : H1Function (openCubeSet (originCube d m)))
    (h₀ : H1Function (openCubeSet (originCube d k)))
    (hh₀ : ∀ x, h₀.grad x = h.grad
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hPsub : translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre q m k) ⊆ U)
    (hUsub : U ⊆ openCubeSet (originCube d m))
    (hUpos : 0 < (volume U).toReal)
    (hPpos : 0 < (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) :
    ∑ i : Fin d,
        normalizedL2On (openCubeSet (originCube d k)) (fun x => h₀.grad x i) ≤
      (d : ℝ) *
        Real.sqrt ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
          vectorNormalizedL2On U h.grad := by
  let R : ℝ := Real.sqrt ((volume U).toReal /
    (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal)
  have hcoord : ∀ i : Fin d,
      normalizedL2On (openCubeSet (originCube d k)) (fun x => h₀.grad x i) ≤
        R * normalizedL2On U (fun x => h.grad x i) := by
    intro i
    exact normalizedL2On_projected_grad_coord_le_window h h₀ hh₀ i
      hPsub hUsub hUpos hPpos
  have hsum : ∑ i : Fin d,
      normalizedL2On (openCubeSet (originCube d k)) (fun x => h₀.grad x i) ≤
      R * ∑ i : Fin d, normalizedL2On U (fun x => h.grad x i) := by
    calc
      ∑ i : Fin d,
          normalizedL2On (openCubeSet (originCube d k)) (fun x => h₀.grad x i) ≤
          ∑ i : Fin d, R * normalizedL2On U (fun x => h.grad x i) :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = R * ∑ i : Fin d, normalizedL2On U (fun x => h.grad x i) := by
        rw [Finset.mul_sum]
  have hmem : MemLp (fun x => HilbertVec.ofVec (h.grad x)) 2
      (volume.restrict U) :=
    (memHilbertVectorL2_hilbertifyVecField h.grad_memVectorL2).mono_measure
      (Measure.restrict_mono_set volume hUsub)
  have hvec := sum_normalizedL2On_coord_le_dimension_mul_vector hmem
  calc
    ∑ i : Fin d,
        normalizedL2On (openCubeSet (originCube d k)) (fun x => h₀.grad x i) ≤
        R * ∑ i : Fin d, normalizedL2On U (fun x => h.grad x i) := hsum
    _ ≤ R * ((d : ℝ) * vectorNormalizedL2On U h.grad) := by
      exact mul_le_mul_of_nonneg_left hvec (Real.sqrt_nonneg _)
    _ = (d : ℝ) * R * vectorNormalizedL2On U h.grad := by ring

/-- Fractional pricing of the transported projected coordinate sum.  The two
surviving quantities are exactly the ambient boundary slope and the ambient
fractional fluctuation from the manuscript display. -/
theorem sum_normalizedL2On_projected_grad_le_mean_add_fractional
    {m k : ℤ} {q : Vec d} {U : Set (Vec d)} {s D : ℝ}
    (h : H1Function (openCubeSet (originCube d m)))
    (h₀ : H1Function (openCubeSet (originCube d k)))
    (hh₀ : ∀ x, h₀.grad x = h.grad
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hPsub : translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre q m k) ⊆ U)
    (hUsub : U ⊆ openCubeSet (originCube d m))
    (hUmeas : MeasurableSet U) (hU0 : 0 < volume U) (hUtop : volume U ≠ ⊤)
    (hPpos : 0 < (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal)
    (hs : 0 < s)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D)
    (hfrac : fractionalSeminormOn U s h.grad ≠ ⊤) :
    ∑ i : Fin d,
        normalizedL2On (openCubeSet (originCube d k)) (fun x => h₀.grad x i) ≤
      (d : ℝ) *
        Real.sqrt ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        (D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
            (volume U).toReal ^ (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn U s h.grad).toReal +
          euclideanNorm (averageVecOn U h.grad)) := by
  let R : ℝ := Real.sqrt ((volume U).toReal /
    (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal)
  have hUpos : 0 < (volume U).toReal := ENNReal.toReal_pos hU0.ne' hUtop
  have hmem : MemLp (fun x => HilbertVec.ofVec (h.grad x)) 2
      (volume.restrict U) :=
    (memHilbertVectorL2_hilbertifyVecField h.grad_memVectorL2).mono_measure
      (Measure.restrict_mono_set volume hUsub)
  have htransport := sum_normalizedL2On_projected_grad_le_window_vector
    h h₀ hh₀ hPsub hUsub hUpos hPpos
  have hsplit := vectorNormalizedL2On_le_sub_averageVecOn_add_mean hUpos hmem
  have hpoin := vectorNormalizedL2On_sub_averageVecOn_le_fractionalSeminormOn
    hUmeas hU0 hUtop hs hdiam hmem hfrac
  have hvector : vectorNormalizedL2On U h.grad ≤
      D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
          (volume U).toReal ^ (-(1 / 2 : ℝ)) *
            (fractionalSeminormOn U s h.grad).toReal +
        euclideanNorm (averageVecOn U h.grad) :=
    hsplit.trans (add_le_add hpoin (le_refl _))
  exact htransport.trans (mul_le_mul_of_nonneg_left hvector (by
    exact mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _)))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
