import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ReadyStep
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GoodStep

/-!
# Interior Hölder Step 3: `e.ready.for.iteration.lemma`, interior branch

The interior mirror of `Section6Holder.exists_holderReadyStep`.  The raw
interior recurrence is normalized by the parent coefficient and the top forcing
seminorm exactly as in the boundary rung; the two datum normalizations
(`vectorSupNormOn (cube d m) h.grad` and the top boundary seminorm) are absent
because the interior binder sets the window-contact indicator to `0`.

The conclusion deliberately reuses the landed carrier
`Section6Holder.holderReadyDefect` with its last three slots at `0`, so the
interior recurrence is literally in the shape consumed by the landed iteration
families.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The concrete one-step interior inequality `e.ready.for.iteration.lemma`. -/
theorem exists_interiorHolderReadyStep {d : ℕ} [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ k : ℕ, 0 < k → ∀ theta : ℝ,
      ∀ L m n j : ℕ, n ≤ j → k ≤ j → m ≤ L → j + 5 ≤ m →
      ∀ z ∈ cube d m,
      ¬ BoundaryTouches (truncatedCube d m j z) (cube d m) →
      ∀ omega,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d m) u g →
        MemHolder (cube d m) (1 / 2) g →
        ∀ ell : Affine d,
          ell ∈ affineMinimizers (truncatedCube d m j z) u.toFun →
          omega ∈ goodEvent M none (j + 2) z epsilon
            Section6Stopping.holderStoppingS →
          C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                  (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) ≤ theta ^ k →
          ∀ exponential : ℝ, 0 ≤ exponential →
          tailCoefficientCubeAverage M L m omega /
              tailAverage M L (j + 2) omega
                (translatedCube d (j + 2 : ℕ) z) ≤ exponential →
          let Keps := C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K
          let Kforce := C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
          let Kmean := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
          let Kboundary := C * (1 / 4 : ℝ) ^ (-3 : ℤ) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
          excess (j - k) (truncatedCube d m (j - k) z) u.toFun ≤
            theta ^ k * excess j (truncatedCube d m j z) u.toFun +
              holderRecurrenceEpsilon Keps M epsilon
                  Section6Stopping.holderStoppingS j z omega *
                Real.sqrt (vecNormSq ell.slope) +
              holderReadyDefect Kforce Kmean Kboundary
                ((3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2))) exponential
                ((tailCoefficientCubeAverage M L m omega)⁻¹ *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  holderSeminormOn (cube d m) (1 / 2) g)
                (holderRecurrenceEpsilon Keps M epsilon
                  Section6Stopping.holderStoppingS j z omega)
                0 0 0 := by
  obtain ⟨C, K, hC, hK, hraw⟩ := exists_interiorHolderGoodStep_raw hExcess
  refine ⟨C, K, hC, hK, ?_⟩
  intro M hsmall epsilon hepsilon k hk theta L m n j hnj hkj hmL hjm z hz hint
    omega u g hsol hg ell hell hgood hcontract exponential hE0 hratio
  dsimp only
  have hgfrac : ∃ sOrder : FractionalOrder, sOrder.1 = (1 / 4 : ℝ) ∧
      Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d m) sOrder FiniteLpExponent.two g :=
    Section6ExcessDecay.exists_fractionalOrder_memCubeEuclideanFullWsp_of_memHolder
      (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)) (by norm_num) le_rfl hg
  have hstep := hraw M hsmall epsilon hepsilon k hk L m j hkj hmL hjm z hz hint
    omega u g hsol hgfrac ell hell hgood
  let Keps := C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K
  let epsJ := holderRecurrenceEpsilon Keps M epsilon
    Section6Stopping.holderStoppingS j z omega
  have hepsEq : epsJ = Keps * min epsilon (M.delta ^ 2 + epsilon ^ 8 +
      accumulatedError M none (j + 2) z Section6Stopping.holderStoppingS omega) := by
    simp only [epsJ, holderRecurrenceEpsilon, if_pos hgood, mul_one]
  have htop : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hlocal : 0 < tailAverage M L (j + 2) omega
      (translatedCube d (j + 2 : ℕ) z) := by
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (j + 2) (translatePotentialSample z omega)
  have hinv : (tailAverage M L (j + 2) omega
      (translatedCube d (j + 2 : ℕ) z))⁻¹ ≤
        exponential * (tailCoefficientCubeAverage M L m omega)⁻¹ := by
    calc
      (tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) z))⁻¹ =
          (tailCoefficientCubeAverage M L m omega /
            tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) z)) *
            (tailCoefficientCubeAverage M L m omega)⁻¹ := by
        field_simp
      _ ≤ exponential * (tailCoefficientCubeAverage M L m omega)⁻¹ :=
        mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr htop.le)
  have hforcingLocal := forcing_fractional_window_le
    (m := (m : ℤ)) (j := (j : ℤ)) (x := z) (g := g) (s := (1 / 4 : ℝ))
    hz (by norm_num) (by norm_num) hg
  have hforcing :
      C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (tailAverage M L (j + 2) omega
            (translatedCube d (j + 2 : ℕ) z))⁻¹ *
          (3 : ℝ) ^ ((1 / 4 : ℝ) * j) *
          (fractionalSeminormOn (truncatedCube d m j z) (1 / 4 : ℝ) g).toReal ≤
        (C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)) *
          (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) * exponential *
          ((tailCoefficientCubeAverage M L m omega)⁻¹ *
            (3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d m) (1 / 2) g) := by
    let coef := C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
    have hcoef : 0 ≤ coef := by
      dsimp only [coef]
      positivity
    have h1 := mul_le_mul_of_nonneg_left hforcingLocal
      (mul_nonneg hcoef (inv_nonneg.mpr hlocal.le))
    have hsemi0 := holderSeminormOn_nonneg hg
    let D := coef * Section6ExcessDecay.fractionalHolderConst d *
      Real.sqrt (1 / 4 : ℝ) * (3 : ℝ) ^ ((j : ℝ) / 2) *
      holderSeminormOn (cube d m) (1 / 2) g
    have hD0 : 0 ≤ D := by
      dsimp only [D]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hcoef (Section6ExcessDecay.fractionalHolderConst_nonneg d))
            (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (by norm_num) _))
        hsemi0
    have h2 := mul_le_mul_of_nonneg_right hinv hD0
    dsimp only [D, coef] at h1 h2
    have hscale : (3 : ℝ) ^ ((j : ℝ) / 2) =
        (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) *
          (3 : ℝ) ^ ((m : ℝ) / 2) := by
      simpa only [Int.cast_natCast] using three_half_scale_decay (m : ℤ) (j : ℤ)
    norm_num only [Int.cast_natCast] at h1
    rw [hscale] at h1 h2
    ring_nf at h1 h2 ⊢
    linarith only [h1, h2]
  have hEx0 : 0 ≤ excess j (truncatedCube d m j z) u.toFun := by
    rw [Section6Iteration.excess_eq_affineExcessScaled]
    exact Section6Iteration.affineExcessScaled_nonneg _ _ _
  have hcontractTerm := mul_le_mul_of_nonneg_right hcontract hEx0
  rw [← hepsEq] at hstep
  unfold holderReadyDefect
  change excess (j - k) (truncatedCube d m (j - k) z) u.toFun ≤
    theta ^ k * excess j (truncatedCube d m j z) u.toFun +
      epsJ * Real.sqrt (vecNormSq ell.slope) +
      (_ * _ * _ * _ + _ * epsJ * (0 : ℝ) * (0 : ℝ) +
        _ * _ * (0 : ℝ) * (0 : ℝ))
  norm_num only [Nat.cast_add, Nat.cast_ofNat, mul_zero, zero_mul, add_zero]
    at hstep hcontractTerm hforcing ⊢
  nlinarith only [hstep, hcontractTerm, hforcing]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
