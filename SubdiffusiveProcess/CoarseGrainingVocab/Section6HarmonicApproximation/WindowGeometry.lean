import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellCover
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalTransport

/-!
# Analytic geometry of the ambient truncated window

This file packages the measure, diameter, `L²`, and fractional-finiteness
facts repeatedly consumed when a projected cell is priced by the ambient
window `U_(m,n)(x)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Finiteness of the normalized fractional seminorm is inherited by a
positive-volume subset. -/
theorem memFractionalOn_mono_set
    {A B : Set (Vec d)} {s : ℝ} {f : Vec d → Vec d}
    (hBA : B ⊆ A) (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ∞)
    (hB0 : volume B ≠ 0)
    (hA : MemFractionalOn A s f) :
    MemFractionalOn B s f := by
  have hcoef : ((volume B)⁻¹ * volume A) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hB0) hAtop)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hcoef hA)
    (fractionalSeminormOn_mono_set hBA hA0 hAtop s f)

/-- The frozen boundary-gradient hypothesis restricts to every positive
truncated window. -/
theorem memFractionalOn_truncatedCube_of_domain
    {m n : ℤ} {x : Vec d} {s : ℝ} {f : Vec d → Vec d}
    (hx : x ∈ cube d m) (hnm : n - 1 ≤ m)
    (hfrac : MemFractionalOn (cube d m) s f) :
    MemFractionalOn (truncatedCube d m n x) s f := by
  have hUreal := Section6ExcessDecay.volume_toReal_truncatedCube_pos x hx hnm
  have hU0 : volume (truncatedCube d m n x) ≠ 0 :=
    (ENNReal.toReal_ne_zero.mp hUreal.ne').1
  have hA0 : volume (cube d m) ≠ 0 := by
    rw [cube]
    have hreal : 0 < (volume (openCubeSet (originCube d m))).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos (originCube d m)
    exact (ENNReal.toReal_ne_zero.mp hreal.ne').1
  have hAtop : volume (cube d m) ≠ ∞ := by
    rw [cube]
    exact (volume_openCubeSet_lt_top (originCube d m)).ne
  exact memFractionalOn_mono_set
    (Section6ExcessDecay.truncatedCube_subset_cube d m n x)
    hA0 hAtop hU0 hfrac

/-- The gradient of an ambient `H¹` function is Hilbert-valued `L²` on every
truncated subwindow. -/
theorem memLp_hilbertGradient_truncatedCube
    {m n : ℤ} {x : Vec d}
    (h : H1Function (openCubeSet (originCube d m))) :
    MemLp (fun q => HilbertVec.ofVec (h.grad q)) 2
      (volume.restrict (truncatedCube d m n x)) := by
  have hL2 : MemLp (fun q => HilbertVec.ofVec (h.grad q)) 2
      (volume.restrict (openCubeSet (originCube d m))) :=
    memHilbertVectorL2_hilbertifyVecField h.grad_memVectorL2
  exact hL2.mono_measure
    (Measure.restrict_mono
      (Section6ExcessDecay.truncatedCube_subset_cube d m n x) le_rfl)

/-- A scale-`n` truncated window has Euclidean diameter at most `d 3^n`. -/
theorem euclideanDiameter_truncatedCube_le
    {m n : ℤ} {x : Vec d} :
    ∀ p ∈ truncatedCube d m n x, ∀ q ∈ truncatedCube d m n x,
      euclideanNorm (p - q) ≤ (d : ℝ) * (3 : ℝ) ^ n := by
  intro p hp q hq
  have hdist : dist p q ≤ (3 : ℝ) ^ n := by
    have hlt := Metric.mem_ball.mp
      (Section6ExcessDecay.truncatedCube_subset_ball hp hq)
    exact le_of_lt (by simpa [dist_comm] using hlt)
  have heu := euclideanDist_le_dimension_mul_dist p q
  unfold euclideanDist at heu
  exact heu.trans (mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg d))

/-- A translated origin cube has positive real volume. -/
theorem volume_translate_openOriginCube_toReal_pos (k : ℤ) (c : Vec d) :
    0 < (volume (translateSet c (openCubeSet (originCube d k)))).toReal := by
  rw [volume_translateSet_eq, volume_openCubeSet_toReal]
  exact cubeVolume_pos (originCube d k)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
