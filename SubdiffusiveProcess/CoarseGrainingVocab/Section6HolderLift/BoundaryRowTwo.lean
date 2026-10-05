module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoAtStepFree
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoOuter
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.HarmonicPassages
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.InteriorHarmonic
public import SubdiffusiveProcess.Providers.Section6.HarmonicApproximationGoodScalesInterior

@[expose] public section

/-!
# The thresholded boundary Holder row two

The manuscript first chooses dimension-dependent large constants `C₁` and
`C₂`.  Accordingly this package exposes lower thresholds, rather than asking
for the energy row for every pair `2 ≤ C₁ ≤ C₂`.  The proof uses the sharp
datum-free interior row in the inner cube and the new four-budget outer row
elsewhere.

Argument: `ss.good.scale.estimates` and `ss.regularity.iteration`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The manuscript-aligned thresholded form of the missing weighted-gradient
row.  Its conclusion is the row printed in `e.energy.density.estimate`. -/
def BoundaryRowTwo (d : ℕ) : Prop :=
  Section6ExcessDecay.HarmonicApproximationInput d →
  ∃ (C1min C2min Crow : ℝ), 2 ≤ C1min ∧ C1min ≤ C2min ∧ 0 ≤ Crow ∧
    ∀ C1 C2 : ℝ, C1min ≤ C1 → C2min ≤ C2 → C1 ≤ C2 →
    ∀ step : ℕ, 21 ≤ step →
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
    ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
      Section6Stopping.holderStoppingEpsilon C2 alpha ∈
        Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
      M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
    ∀ L m : ℕ, m ≤ L → ∀ omega,
    ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (originCube d m) u h g →
      MemHolder (cube d m) (1 / 2) g → MemHolder (cube d m) (1 / 2) h.grad →
      ∀ n : ℕ,
        (n : ℤ) ≤ (m : ℤ) -
          (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) →
        ∀ x ∈ cube d m,
          vectorNormalizedL2On (truncatedCube d m n x)
              (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega z) •
                u.grad z) ≤
            Crow * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (vectorNormalizedL2On (cube d m)
                  (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega z) •
                    u.grad z) +
                (tailAverage M L m omega (cube d m)) ^ (-1 / 2 : ℝ) *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  holderSeminormOn (cube d m) (1 / 2) g +
                (if x ∈ cube d (m - 1) then 0 else
                  (tailAverage M L m omega (cube d m)) ^ (1 / 2 : ℝ) *
                    (3 : ℝ) ^ ((m : ℝ) / 2) *
                    fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                      (1 / 2) h.grad))

/-- The weighted-gradient row, with the large-constant choice made explicit. -/
theorem boundaryRowTwo (d : ℕ) [NeZero d] : BoundaryRowTwo d := by
  intro hHarmonic
  have hBoundaryExcess := boundaryHolderExcessDecayInput_of_harmonicInput d hHarmonic
  have hInteriorHarmonic : ∀ [NeZero d],
      Section6SealAdapters.InteriorHarmonicApproximationInput d := by
    intro _
    exact SubdiffusiveProcess.Providers.Section6.harmonic_approximation_good_scales_interior d
  have hInteriorExcess : InteriorHolderExcessDecayInput d :=
    Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
      d hInteriorHarmonic
  obtain ⟨C1i, C2i, Ci, hC1i, hC12i, hCi, hinterior⟩ :=
    exists_interiorRowTwoAtStepFree d hInteriorExcess
  obtain ⟨C1o, C2o, Co, hC1o, hC12o, hCo, houter⟩ :=
    exists_boundaryRowTwoOuterAtStepFree d hBoundaryExcess
  let C1min := max C1i C1o
  let C2min := max (max C2i C2o) C1min
  let Crow := max Ci Co
  have hC1min : (2 : ℝ) ≤ C1min := hC1i.trans (le_max_left _ _)
  have hC12min : C1min ≤ C2min := le_max_right _ _
  have hCrow : 0 ≤ Crow := hCi.trans (le_max_left _ _)
  refine ⟨C1min, C2min, Crow, hC1min, hC12min, hCrow, ?_⟩
  intro C1 C2 hC1 hC2 hC12 step hstep M hsmall alpha halpha heps hdelta
    L m hmL omega u h g hsol hg hh n hstop x hx
  have hC1i' : C1i ≤ C1 := (le_max_left C1i C1o).trans hC1
  have hC1o' : C1o ≤ C1 := (le_max_right C1i C1o).trans hC1
  have hC2i' : C2i ≤ C2 :=
    ((le_max_left C2i C2o).trans
      (le_max_left (max C2i C2o) C1min)).trans hC2
  have hC2o' : C2o ≤ C2 :=
    ((le_max_right C2i C2o).trans
      (le_max_left (max C2i C2o) C1min)).trans hC2
  have hCiCrow : Ci ≤ Crow := le_max_left _ _
  have hCoCrow : Co ≤ Crow := le_max_right _ _
  have hpow0 : 0 ≤ (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) := by
    positivity
  have hEg0 : 0 ≤ vectorNormalizedL2On (cube d (m : ℤ))
      (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega z) • u.grad z) :=
    Real.sqrt_nonneg _
  have hG0 : 0 ≤ (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
      (3 : ℝ) ^ ((m : ℝ) / 2) *
      holderSeminormOn (cube d (m : ℤ)) (1 / 2) g := by
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
        (Real.rpow_nonneg (by norm_num) _))
      (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  by_cases hxinner : x ∈ cube d ((m : ℤ) - 1)
  · have hr := hinterior C1 C2 hC1i' hC2i' hC12 step hstep M hsmall alpha
      halpha heps hdelta L m hmL omega u g hsol.2 hg n (by omega) x hxinner
    simp only [ite_eq_left hxinner, add_zero]
    exact hr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCiCrow hpow0) (add_nonneg hEg0 hG0))
  · have hr := houter C1 C2 hC1o' hC2o' hC12 step hstep M hsmall alpha
      halpha heps hdelta L m hmL omega u h g hsol hg hh n (by omega) x hx
    simp only [ite_eq_right hxinner]
    have hH0 : 0 ≤ (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
        (3 : ℝ) ^ ((m : ℝ) / 2) *
        fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
          (1 / 2) h.grad := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
          (Real.rpow_nonneg (by norm_num) _))
        (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
    exact hr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCoCrow hpow0)
      (add_nonneg (add_nonneg hEg0 hG0) hH0))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
