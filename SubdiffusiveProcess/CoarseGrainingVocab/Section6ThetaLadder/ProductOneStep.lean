import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductComparisonLinear
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.OneStep
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Composition

/-!
# Theta-perturbed ladder: product comparison into the landed recurrence

This is the promised reuse seam.  A unit-harmonic comparator and its local
normalized `L²` error are inserted into the existing Schauder producer and
`excess_oneStep_of_schauder`; no excess recurrence is reproved.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The landed one-step recurrence with the product-comparison error exposed
as a single local normalized `L²` slot. -/
theorem excess_oneStep_of_productComparison
    (hd : d ≠ 0) {domain n : ℤ} {k : ℕ} (hk : 6 ≤ k)
    {x y : Vec d} (hx : x ∈ cube d domain) (hnm : n - 1 ≤ domain)
    (hcube : translatedCube d (n - 4) x ⊆ cube d domain)
    (hsub : truncatedCube d domain (n - 4) x ⊆
      translatedCube d (n - 2) y)
    (u : H1Function (openCubeSet (originCube d domain)))
    (w : H1Function (translatedCube d (n - 2) y))
    (hw : IsWeaklyHarmonicOn (fun _ ↦ (1 : ℝ))
      (translatedCube d (n - 2) y) w)
    {D : ℝ}
    (hD : normalizedL2On (truncatedCube d domain (n - 4) x)
      (fun p ↦ u.toFun p - w.toFun p) ≤ D) :
    excess (n - (k : ℤ))
        (truncatedCube d domain (n - (k : ℤ)) x) u.toFun ≤
      oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
          excess n (truncatedCube d domain n x) u.toFun +
        oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k *
          ((3 : ℝ) ^ (-n) * D) := by
  have hu_n : MemLp u.toFun 2
      (volume.restrict (truncatedCube d domain n x)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d domain n x) le_rfl)
  obtain ⟨v, K, hvae, hvmem, hK0, hint, hgrad, hholder, hschauder⟩ :=
    Section6Schauder.exists_gradientHolder_of_weaklyHarmonic
      (d := d) (m := domain) (n := n) (x := x) (y := y)
      hd hx (by omega) hcube hsub hw
  have hv4 : MemLp v 2
      (volume.restrict (truncatedCube d domain (n - 4) x)) :=
    hvmem.restrict _
  have hone := excess_oneStep_of_schauder
    (d := d) (m := domain) (n := n) (k := k) (Kh := 0)
      hk hx hnm hu_n hv4 hK0
      (Section6Schauder.schauderInteriorConst_nonneg d)
      hint hgrad hholder hschauder
  have herrorEq :
      normalizedL2On (truncatedCube d domain (n - 4) x)
          (fun p ↦ u.toFun p - v p) =
        normalizedL2On (truncatedCube d domain (n - 4) x)
          (fun p ↦ u.toFun p - w.toFun p) := by
    refine normalizedL2On_congr_ae ?_
    have hres : v =ᵐ[volume.restrict
        (truncatedCube d domain (n - 4) x)] w.toFun :=
      hvae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hres] with p hp
    rw [hp]
  rw [herrorEq, mul_zero, add_zero] at hone
  have hcoef : 0 ≤ oneStepRemainderConst d
      (Section6Schauder.schauderInteriorConst d) k :=
    oneStepRemainderConst_nonneg d
      (Section6Schauder.schauderInteriorConst_nonneg d) k
  have hscale : 0 ≤ (3 : ℝ) ^ (-n) := (zpow_pos (by norm_num) _).le
  have hreplace := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hD hscale) hcoef
  exact hone.trans (add_le_add le_rfl hreplace)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
