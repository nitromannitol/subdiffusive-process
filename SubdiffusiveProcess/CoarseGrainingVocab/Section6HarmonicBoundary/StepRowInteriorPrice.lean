import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.InteriorCellAtScale
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The normalized `L²` seminorm squared is the volume average of the square. -/
theorem normalizedL2On_sq_eq_volumeAverage (W : Set (Vec d)) (f : Vec d → ℝ)
    (hf : 0 ≤ ∫ p in W, f p ^ 2) :
    normalizedL2On W f ^ 2 = (volume W).toReal⁻¹ * ∫ p in W, f p ^ 2 := by
  rw [normalizedL2On, Real.sq_sqrt]
  · rfl
  · exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) hf

/-- **The interior cell price, unnormalized.**

`(♣)` of report §15.5 in the form the cover summation consumes.  The two prices
are integrals over the cell's own projected parent `P_q = q̂ + 𝔠_k`, with no
comparison to the ambient window and hence no volume ratio; the constant is the
dimension-only `K` of
`InteriorCellAtScale.exists_interiorCellEnergy_le_parentPrices_atScale`. -/
theorem exists_interiorCellEnergy_setIntegral_le_parentIntegrals_atScale
    (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ k : ℤ, k ≤ (n : ℤ) - 2 →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ cube d (m : ℤ) →
        translatedCube d k (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) ⊆
          truncatedCube d (m : ℤ) (n : ℤ) x →
        openCubeAtScale q (k - 1) ⊆ cube d (m : ℤ) →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
        let P := translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        ∫ p in truncatedCube d (m : ℤ) (k - 2) q,
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p) ≤
          K * Real.rpow (3 : ℝ)
              (2 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
            (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
                (∫ p in P, (u.toFun p - c0) ^ 2) +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) *
                ((volume P).toReal *
                  (fractionalSeminormOn P sOrder.1 g).toReal ^ 2)) := by
  obtain ⟨K, hK, hchamp⟩ := exists_interiorCellEnergy_le_parentPrices_atScale d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hmL hnm k hk z x q omega hz hx hq hparent hpatch hgood
    u h g c0 hdir hg hh
  dsimp only
  have hhFull : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad := by
    apply memCubeEuclideanFullWsp_grad_of_memFractionalOn
    simpa [cube] using hh
  have hcell := hchamp M sOrder hs L m n hmL hnm k hk z x q omega hz hx hq
    hparent hpatch hgood u h g c0 hdir hg hhFull
  dsimp only at hcell
  set P : Set (Vec d) := translatedCube d k
    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) with hPdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set cell : Set (Vec d) := truncatedCube d (m : ℤ) (k - 2) q with hcelldef
  -- volumes
  have hcellpos : 0 < (volume cell).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos q hq (by omega)
  have hcellub : (volume cell).toReal ≤ ((3 : ℝ) ^ (k - 2)) ^ d :=
    (Section6ExcessDecay.volume_toReal_truncatedCube_bounds q hq (by omega)).2
  have hPvol : (volume P).toReal = ((3 : ℝ) ^ k) ^ d := by
    rw [hPdef]
    exact Section6BoundedMultiplier.volume_translatedCube_toReal k _
  have hPpos : 0 < (volume P).toReal := by rw [hPvol]; positivity
  have hcellleP : (volume cell).toReal ≤ (volume P).toReal := by
    refine hcellub.trans ?_
    rw [hPvol]
    exact pow_le_pow_left₀ (by positivity)
      (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
  -- the cell integral is the volume times the normalized average
  have hint : ∫ p in cell,
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p) =
      (volume cell).toReal * normalizedSetAverage cell
        (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
          vecNormSq (u.grad y)) := by
    rw [normalizedSetAverage, Homogenization.volumeAverage, ← mul_assoc,
      mul_inv_cancel₀ hcellpos.ne', one_mul]
  -- the parent oscillation leg
  have hosc0 : 0 ≤ ∫ p in P, (u.toFun p - c0) ^ 2 :=
    integral_nonneg fun p => sq_nonneg _
  have hL2 : normalizedL2On P (fun y => u.toFun y - c0) ^ 2 =
      (volume P).toReal⁻¹ * ∫ p in P, (u.toFun p - c0) ^ 2 :=
    normalizedL2On_sq_eq_volumeAverage P _ hosc0
  have hlegA : (volume cell).toReal *
      normalizedL2On P (fun y => u.toFun y - c0) ^ 2 ≤
      ∫ p in P, (u.toFun p - c0) ^ 2 := by
    rw [hL2, ← mul_assoc]
    refine mul_le_of_le_one_left hosc0 ?_
    rw [mul_inv_le_iff₀ hPpos, one_mul]
    exact hcellleP
  -- the datum leg
  have hlegD : (volume cell).toReal *
      (fractionalSeminormOn P sOrder.1 g).toReal ^ 2 ≤
      (volume P).toReal * (fractionalSeminormOn P sOrder.1 g).toReal ^ 2 :=
    mul_le_mul_of_nonneg_right hcellleP (sq_nonneg _)
  -- positivity of the coefficients
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  have hcoefA : 0 ≤ sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) :=
    mul_nonneg hsigma.le (Real.rpow_nonneg (by norm_num) _)
  have hcoefD : 0 ≤ Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
      Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (inv_nonneg.mpr hsigma.le)) (Real.rpow_nonneg (by norm_num) _)
  have houter : 0 ≤ K * Real.rpow (3 : ℝ)
      (2 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) :=
    mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _)
  -- multiply the normalized bound by the cell volume
  have hmul := mul_le_mul_of_nonneg_left hcell hcellpos.le
  rw [← hint] at hmul
  refine hmul.trans ?_
  have hexpand : (volume cell).toReal *
      (K * Real.rpow (3 : ℝ)
          (2 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
        (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
            normalizedL2On P (fun y => u.toFun y - c0) ^ 2 +
          Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) *
            (fractionalSeminormOn P sOrder.1 g).toReal ^ 2)) =
      K * Real.rpow (3 : ℝ)
          (2 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
        (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
            ((volume cell).toReal *
              normalizedL2On P (fun y => u.toFun y - c0) ^ 2) +
          Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ)) *
            ((volume cell).toReal *
              (fractionalSeminormOn P sOrder.1 g).toReal ^ 2)) := by ring
  rw [hexpand]
  refine mul_le_mul_of_nonneg_left ?_ houter
  exact add_le_add (mul_le_mul_of_nonneg_left hlegA hcoefA)
    (mul_le_mul_of_nonneg_left hlegD hcoefD)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
