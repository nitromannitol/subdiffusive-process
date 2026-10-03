module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorLocalError

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The complete flat-comparator coarse error on `y+cube_(n-2)`, with the
local response replaced by the anchored Section 6 error. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x => u.toFun x - v.toFun x) ≤
          (Section6Dirichlet.dirichletSpectralReadoutConstant smid d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorManuscriptBound d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n hnL omega y z hcontain hgood
  dsimp only
  intro g hg u v hu hv huv S D hS hD
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 (by norm_num)
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hE := localHomogenizationError_two_le_anchor_of_closedContainment
    M hs L n hnL omega y z hcontain hgood
  have hres := hmain ((n : ℤ) - 2) s hs0 hs1
    (aCutoffFamily M L (translatePotentialSample y omega))
    (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
    (by
      rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
      rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
      exact tailCoefficientCubeAverage_pos M L (n + 2)
        (translatePotentialSample z omega)) g hg u v hu hv huv E S D
    (by simpa only [E] using hE)
    (by simpa [originCube] using hS) hD
  simpa only [E, show ((n : ℤ) - 2) - 1 = (n : ℤ) - 3 by ring] using hres

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
