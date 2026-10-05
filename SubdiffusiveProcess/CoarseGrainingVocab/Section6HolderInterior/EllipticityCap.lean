module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EllipticityPairing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalEllipticityControl
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.GoodEventErrorCap

@[expose] public section

/-!
# The good-scale ellipticity cap, in the slot row 2's Poincaré leg needs

The display `e.ellipticity.good.scale.bounds` reads: on a good
scale, the multiscale ellipticity constants of the cutoff family on the cube at
that scale are comparable to the tail average, with a **deterministic** constant.
This module assembles the lower half of that display — the only half row 2's
`hO` leg uses — out of three proved pieces:

* `Section6HarmonicApproximation.exists_section6HomogenizationError_le_of_goodEvent`
  — the good event caps the Section 6 error by a dimension-only constant (this is
  the last assertion of the proved `p.good.scale.mathcal.E`);
* `Section6HarmonicApproximation.localHomogenizationError_two_le_anchor_of_closedContainment`
  — the anchored error transports to the off-grid comparison cube;
* `Section6HarmonicApproximation.localMaxWeightedEllipticity_le_error`
  — `e.bound.Lambdas.by.Es` at `q = 2`, in the direction "small error implies
  two-sided ellipticity comparison".

Composed with `EllipticityPairing.lambdaSq_cap_mono`, the cap is delivered at the
order slot `1/2`, which is where the fractional-Poincaré leg leaves the negative
Besov norm.  Everything is **deterministic**: the only sample-dependence left is
the good-event hypothesis.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- **The good-scale ellipticity cap.**  At a good scale, the tail average times
the inverse lower multiscale ellipticity constant of the cutoff family, on the
off-grid comparison cube, is bounded by a dimension-only constant. -/
theorem exists_interiorEllipticityCap (d : ℕ) [NeZero d] :
    ∃ Kell : ℝ, 0 ≤ Kell ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L →
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, ∀ y z : Vec d,
        translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z) *
            (Ch02.lambdaSq (originCube d ((n : ℤ) - 2)) (1 / 2 : ℝ) (.finite 2)
              (aCutoffFamily M L (translatePotentialSample y omega)))⁻¹ ≤
          Kell := by
  obtain ⟨C, hC, hgood⟩ :=
    exists_section6HomogenizationError_le_of_goodEvent (d := d)
  refine ⟨2 * (d : ℝ) *
    ((Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ ((1 : ℝ) / 8) * C)) ^ 2 + 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤
        (Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ ((1 : ℝ) / 8) * C)) ^ 2 + 1 := by
      positivity
    exact mul_nonneg h1 h2
  intro M s hs L n hnL omega y z hcontain hgoodEvent
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos hdelta 2)).trans_le hs.1
  set A : Ch02.TriadicCoeffFamily d :=
    aCutoffFamily M L (translatePotentialSample y omega) with hAdef
  set Q : TriadicCube d := originCube d ((n : ℤ) - 2) with hQdef
  set sigma : ℝ :=
    tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z) with hsigmaDef
  have hsigma : 0 < sigma := by
    rw [hsigmaDef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  -- the transported local error
  have hlocal := localHomogenizationError_two_le_anchor_of_closedContainment
    M hs L n hnL omega y z hcontain hgoodEvent
  have hanchor := hgood M s hs L (n + 2) (by omega) omega z hgoodEvent
  set E : ℝ := Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
    (scalarMatrix (d := d) sigma) with hEdef
  have hE0 : 0 ≤ E := by
    rw [hEdef]
    unfold Ch02.HomogenizationErrorOnCube Ch02.HomogenizationError
      Ch02.HomogenizationErrorFinite
    refine Real.rpow_nonneg (tsum_nonneg fun j ↦ mul_nonneg ?_ ?_) _
    · simpa [Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s / 6) (q := (2 : ℝ)) j
          (by positivity))
    · exact Real.rpow_nonneg
        (Ch02.scaleResponseAtScale_infinity_nonneg Q
          (sub_le_self _ (by exact_mod_cast Nat.zero_le j)) A
          (scalarMatrix (d := d) sigma)) _
  have hpow : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ ((1 : ℝ) / 8) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have := hs.2
    linarith
  have hEbound : E ≤
      Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ ((1 : ℝ) / 8) * C) := by
    refine hlocal.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have hC0 : (0 : ℝ) ≤ C := hC.le
    have h1 : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
        section6HomogenizationError M (s / 8) L (n + 2) omega z ≤
        (3 : ℝ) ^ (s / 8 * (4 : ℝ)) * C := by
      refine mul_le_mul_of_nonneg_left hanchor (Real.rpow_nonneg (by norm_num) _)
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right hpow hC0
  -- `e.bound.Lambdas.by.Es` at `q = 2`
  have hmax := localMaxWeightedEllipticity_le_error (d := d) Q A
    (t := s / 6) (sigma := sigma) (by linarith) hsigma
  have hcap6 : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤
      2 * (d : ℝ) *
        ((Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ ((1 : ℝ) / 8) * C)) ^ 2 + 1) := by
    refine (le_max_right _ _).trans (hmax.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsq : E ^ 2 ≤
        (Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ ((1 : ℝ) / 8) * C)) ^ 2 := by
      exact pow_le_pow_left₀ hE0 hEbound 2
    linarith
  exact lambdaSq_cap_mono Q A (by linarith) (by linarith [hs.2]) hsigma.le hcap6

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
