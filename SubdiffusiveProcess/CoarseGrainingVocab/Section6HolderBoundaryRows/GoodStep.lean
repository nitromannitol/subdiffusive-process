import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.ExcessDecayInput
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorCovariance
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap

/-!
# Boundary Holder recurrence at one good scale, excess-decay v4
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The datum-bearing one-step recurrence with the D-073 powers. -/
theorem exists_boundaryHolderGoodStep_raw {d : ℕ}
    (hExcess : BoundaryHolderExcessDecayInput d) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ k : ℕ, 0 < k → ∀ L m j : ℕ, k ≤ j → m ≤ L → j + 5 ≤ m →
      ∀ z ∈ cube d m, ∀ omega,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = (1 / 4 : ℝ) ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d,
          ell ∈ affineMinimizers (truncatedCube d m j z) u.toFun →
          omega ∈ goodEvent M none (j + 2) z epsilon
            Section6Stopping.holderStoppingS →
          excess (j - k) (truncatedCube d m (j - k) z) u.toFun ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                  (1 / 4 : ℝ) ^ (-2 : ℝ) * epsilon) *
              excess j (truncatedCube d m j z) u.toFun +
            (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (1 / 4 : ℝ) ^ (-2 : ℝ) * K *
              min epsilon (M.delta ^ 2 + epsilon ^ 8 +
                accumulatedError M none (j + 2) z
                  Section6Stopping.holderStoppingS omega)) *
              Real.sqrt (vecNormSq ell.slope) +
            C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (1 / 4 : ℝ) ^ (-2 : ℝ) * K *
              min epsilon (M.delta ^ 2 + epsilon ^ 8 +
                accumulatedError M none (j + 2) z
                  Section6Stopping.holderStoppingS omega) *
              (if BoundaryTouches (truncatedCube d m j z) (cube d m) then
                (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
                  Real.sqrt (vecNormSq
                    (averageVecOn (truncatedCube d m j z) h.grad))
              else 0) +
            C * (1 / 4 : ℝ) ^ (-8 : ℝ) *
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (tailAverage M L (j + 2) omega
                (translatedCube d (j + 2 : ℕ) z))⁻¹ *
              (3 : ℝ) ^ ((1 / 4 : ℝ) * j) *
              (fractionalSeminormOn (truncatedCube d m j z)
                (1 / 4 : ℝ) g).toReal +
            (if BoundaryTouches (truncatedCube d m j z) (cube d m) then
              C * (1 / 4 : ℝ) ^ (-7 / 2 : ℝ) *
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((j : ℝ) / 2) *
                holderSeminormOn (truncatedCube d m j z) (1 / 2) h.grad
            else 0) := by
  obtain ⟨C, hC, hstep⟩ := hExcess
  obtain ⟨K, hK, herr⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.exists_holderSection6Error_le_recurrenceMin d
  refine ⟨C, K, hC, hK, ?_⟩
  intro M hsmall epsilon hepsilon k hk L m j hkj hmL hjm z hz omega u h g
    hsol hg hh ell hell hgood
  have hs : (1 / 4 : ℝ) ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) := by
    constructor
    · rw [Section6Stopping.holderStoppingS] at hsmall
      norm_num at hsmall ⊢
      nlinarith
    · exact le_rfl
  have hepsilon' : epsilon ∈ Set.Icc
      (8 * (1 / 4 : ℝ)⁻¹ * M.delta ^ 2) 1 := by
    convert hepsilon using 1
    all_goals norm_num [Section6Stopping.holderStoppingS]
  have hzlocal : z ∈ truncatedCube d m (j - 3) z :=
    mem_truncatedCube_self (j - 3 : ℤ) hz
  have hraw := hstep M (1 / 4 : ℝ) hs epsilon hepsilon' k hk L m j hkj hmL hjm
    z hz z hz hzlocal omega u h g hsol hg hh ell hell
  have hgood' : omega ∈ goodEvent M none (j + 2) z epsilon
      ((1 / 4 : ℝ) / 8) := by
    convert hgood using 1
    all_goals norm_num [Section6Stopping.holderStoppingS]
  rw [indicatorValue_of_mem hgood'] at hraw
  have hscale : (1 / 4 : ℝ) / 8 = Section6Stopping.holderStoppingS := by
    norm_num [Section6Stopping.holderStoppingS]
  rw [hscale] at hraw
  have hmath := herr M hsmall L (j + 2) (by omega) omega z epsilon hepsilon hgood
  have hfactor : 0 ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      (1 / 4 : ℝ) ^ (-2 : ℝ) := by positivity
  let B := Real.sqrt (vecNormSq ell.slope) +
    (if BoundaryTouches (truncatedCube d m j z) (cube d m) then
      (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m j z) h.grad))
    else 0)
  have hB : 0 ≤ B := by dsimp only [B]; split_ifs <;> positivity
  have hmath' := mul_le_mul_of_nonneg_left hmath (mul_nonneg hfactor hB)
  dsimp only [B] at hmath'
  have hreplace :
      C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (1 / 4 : ℝ) ^ (-2 : ℝ) *
          section6HomogenizationError M Section6Stopping.holderStoppingS
            L (j + 2) omega z *
          (Real.sqrt (vecNormSq ell.slope) +
            (if BoundaryTouches (truncatedCube d m j z) (cube d m) then
              (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
                Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m j z) h.grad))
            else 0)) ≤
        (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            (1 / 4 : ℝ) ^ (-2 : ℝ) * K *
          min epsilon (M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M none (j + 2) z Section6Stopping.holderStoppingS omega)) *
            Real.sqrt (vecNormSq ell.slope) +
        C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            (1 / 4 : ℝ) ^ (-2 : ℝ) * K *
          min epsilon (M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M none (j + 2) z Section6Stopping.holderStoppingS omega) *
            (if BoundaryTouches (truncatedCube d m j z) (cube d m) then
              (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
                Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m j z) h.grad))
            else 0) := by
    calc
      _ = C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (1 / 4 : ℝ) ^ (-2 : ℝ) *
          (Real.sqrt (vecNormSq ell.slope) +
            (if BoundaryTouches (truncatedCube d m j z) (cube d m) then
              (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
                Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m j z) h.grad))
            else 0)) *
          section6HomogenizationError M Section6Stopping.holderStoppingS
            L (j + 2) omega z := by ring
      _ ≤ _ := hmath'
      _ = _ := by ring
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hraw ⊢
  nlinarith only [hraw, hreplace]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
