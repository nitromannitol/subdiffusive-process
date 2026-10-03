module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ExcessDecayInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap

@[expose] public section

/-!
# Interior Hölder Step 3: the concrete good-scale recurrence, interior branch

This is the interior mirror of `Section6Holder.exists_holderGoodStep_raw`: the
fixed manuscript scale `s = 1/4` is substituted into the interior excess-decay
input, and the local homogenization error is replaced by the accumulated-error
minimum through the (datum-free) covariance estimate
`Section6Holder.exists_holderSection6Error_le_recurrenceMin`.

Both boundary legs of the boundary rung are absent here: on the interior branch
the printed indicator `if BoundaryTouches (truncatedCube d m j z) (cube d m)`
is `0`, so the datum `h` — which the interior anchor does not supply — never
enters.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The interior Step-3 recurrence on a good scale. -/
theorem exists_interiorHolderGoodStep_raw {d : ℕ}
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ k : ℕ, 0 < k → ∀ L m j : ℕ, k ≤ j → m ≤ L → j + 5 ≤ m →
      ∀ z ∈ cube d m,
      ¬ BoundaryTouches (truncatedCube d m j z) (cube d m) →
      ∀ omega,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = (1 / 4 : ℝ) ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ ell : Affine d,
          ell ∈ affineMinimizers (truncatedCube d m j z) u.toFun →
          omega ∈ goodEvent M none (j + 2) z epsilon
            Section6Stopping.holderStoppingS →
          excess (j - k) (truncatedCube d m (j - k) z) u.toFun ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                  (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) *
              excess j (truncatedCube d m j z) u.toFun +
            (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K *
              min epsilon (M.delta ^ 2 + epsilon ^ 8 +
                accumulatedError M none (j + 2) z
                  Section6Stopping.holderStoppingS omega)) *
              Real.sqrt (vecNormSq ell.slope) +
            C * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (tailAverage M L (j + 2) omega
                (translatedCube d (j + 2 : ℕ) z))⁻¹ *
              (3 : ℝ) ^ ((1 / 4 : ℝ) * j) *
              (fractionalSeminormOn (truncatedCube d m j z)
                (1 / 4 : ℝ) g).toReal := by
  obtain ⟨C, hC, hstep⟩ := hExcess
  obtain ⟨K, hK, herr⟩ := Section6Holder.exists_holderSection6Error_le_recurrenceMin d
  -- OPEN-17 (D-073): the interior excess-decay input now prints `s^{-2}` and
  -- `s^{-8}`.  At the fixed manuscript scale `s = 1/4` both are exactly twice
  -- the printed `s^{-3/2}`, `s^{-15/2}`, so the row absorbs the change into
  -- its own existential constant; the statement is unchanged.
  have hhalf : (1 / 4 : ℝ) ^ (-1 / 2 : ℝ) = 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast (1 / 2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpowA : (1 / 4 : ℝ) ^ (-2 : ℝ) = 2 * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [show (-2 : ℝ) = (-3 / 2 : ℝ) + (-1 / 2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num), hhalf]
    ring
  have hpowB : (1 / 4 : ℝ) ^ (-8 : ℝ) = 2 * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) := by
    rw [show (-8 : ℝ) = (-15 / 2 : ℝ) + (-1 / 2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num), hhalf]
    ring
  refine ⟨2 * C, K, by linarith, hK, ?_⟩
  intro M hsmall epsilon hepsilon k hk L m j hkj hmL hjm z hz hint omega u g
    hsol hg ell hell hgood
  have hs : (1 / 4 : ℝ) ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) := by
    constructor
    · have := hsmall
      rw [Section6Stopping.holderStoppingS] at this
      norm_num at this ⊢
      nlinarith
    · exact le_rfl
  have hepsilon' : epsilon ∈ Set.Icc
      (8 * (1 / 4 : ℝ)⁻¹ * M.delta ^ 2) 1 := by
    convert hepsilon using 1
    all_goals norm_num [Section6Stopping.holderStoppingS]
  have hzlocal : z ∈ truncatedCube d m (j - 3) z :=
    mem_truncatedCube_self (j - 3 : ℤ) hz
  have hraw := hstep M (1 / 4 : ℝ) hs epsilon hepsilon' k hk L m j hkj hmL hjm
    z hz z hz hzlocal hint omega u g hsol hg ell hell
  have hgood' : omega ∈ goodEvent M none (j + 2) z epsilon
      ((1 / 4 : ℝ) / 8) := by
    convert hgood using 1
    all_goals norm_num [Section6Stopping.holderStoppingS]
  rw [Section6ExcessDecay.indicatorValue_of_mem hgood'] at hraw
  have hscale : (1 / 4 : ℝ) / 8 = Section6Stopping.holderStoppingS := by
    norm_num [Section6Stopping.holderStoppingS]
  rw [hscale, hpowA, hpowB] at hraw
  have hmath := herr M hsmall L (j + 2) (by omega) omega z epsilon hepsilon hgood
  have hfactor : 0 ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) := by positivity
  have hmath' := mul_le_mul_of_nonneg_left hmath
    (mul_nonneg hfactor (Real.sqrt_nonneg (vecNormSq ell.slope)))
  have hreplace :
      C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
          section6HomogenizationError M Section6Stopping.holderStoppingS
            L (j + 2) omega z *
          Real.sqrt (vecNormSq ell.slope) ≤
        (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K *
          min epsilon (M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M none (j + 2) z
              Section6Stopping.holderStoppingS omega)) *
            Real.sqrt (vecNormSq ell.slope) := by
    calc
      _ = C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
          Real.sqrt (vecNormSq ell.slope) *
          section6HomogenizationError M Section6Stopping.holderStoppingS
            L (j + 2) omega z := by ring
      _ ≤ _ := hmath'
      _ = _ := by ring
  have hEx0 : 0 ≤ excess (j : ℤ) (truncatedCube d m j z) u.toFun := by
    rw [Section6Iteration.excess_eq_affineExcessScaled]
    exact Section6Iteration.affineExcessScaled_nonneg _ _ _
  have hnn : (0 : ℝ) ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) *
      excess (j : ℤ) (truncatedCube d m j z) u.toFun :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _)) hEx0
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hraw hnn ⊢
  nlinarith only [hraw, hreplace, hnn]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
