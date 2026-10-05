module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal

@[expose] public section

/-!
# Expected one-scale response reduction

The deterministic response is subadditive over the child partition.  After
integration, stationarity makes every child expectation equal to the centered
child-cube expectation, so the finite average collapses to that one value.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Stationarity and response subadditivity reduce a parent-cube expected
response to the expected response on any prescribed descendant scale. -/
theorem expectedJ_le_of_scale_le {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ) (hnm : n ≤ m)
    (p q : Vec d) :
    expectedJ M L m p q ≤ expectedJ M L n p q := by
  let Q := originCube d (m : ℤ)
  let D := descendantsAtScale Q (n : ℤ)
  let c : ℝ := ∫ eta, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta
    ∂M.P.toMeasure
  let A : Sample d → ℝ := fun omega =>
    ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
      centeredCutoffResponseOnCube M L n p q R omega
  have hscale : (n : ℤ) ≤ Q.scale := by
    change (n : ℤ) ≤ (m : ℤ)
    exact_mod_cast hnm
  have hDscale : ∀ R ∈ D, R.scale = (n : ℤ) := by
    intro R hR
    exact descendant_scale_eq_of_mem_descendantsAtScale hR
  have hAint : Integrable A M.P.toMeasure := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro R hR
    exact integrable_centeredCutoffResponseOnCube M L n p q R
  have hpoint : ∀ omega, cutoffResponseOnCube M L p q Q omega ≤ A omega + c := by
    intro omega
    simpa [Q, D, A, c] using
      cutoffResponseOnCube_le_centeredDescendantAverage_add_mean
        M L n m hnm p q omega
  have hmeanA : ∫ omega, A omega ∂M.P.toMeasure = 0 := by
    rw [show (fun omega => A omega) = fun omega =>
        ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
          centeredCutoffResponseOnCube M L n p q R omega by rfl,
      integral_const_mul,
      integral_finsetSum D (fun R hR =>
        integrable_centeredCutoffResponseOnCube M L n p q R)]
    have hzero : ∀ R ∈ D,
        ∫ omega, centeredCutoffResponseOnCube M L n p q R omega
          ∂M.P.toMeasure = 0 := by
      intro R hR
      exact integral_centeredCutoffResponseOnCube_eq_zero
        M L n p q R (hDscale R hR)
    have hsum :
        (∑ R ∈ D,
          ∫ omega, centeredCutoffResponseOnCube M L n p q R omega
            ∂M.P.toMeasure) = 0 := by
      exact Finset.sum_eq_zero fun R hR => hzero R hR
    rw [hsum, mul_zero]
  have hparentInt : Integrable (cutoffResponseOnCube M L p q Q) M.P.toMeasure :=
    integrable_cutoffResponseOnCube M L p q Q
  have hrightInt : Integrable (fun omega => A omega + c) M.P.toMeasure :=
    hAint.add (integrable_const c)
  have hle := integral_mono hparentInt hrightInt hpoint
  have hright : ∫ omega, A omega + c ∂M.P.toMeasure = c := by
    rw [integral_add hAint (integrable_const c), hmeanA, zero_add]
    simp
  simpa [expectedJ, cutoffResponseOnCube, Q, c, aCutoffFamily,
    aCutoffTriadicData] using hle.trans_eq hright

/-- The child-to-parent instance. -/
theorem expectedJ_le_previous {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (p q : Vec d) :
    expectedJ M L m p q ≤ expectedJ M L (m - 1) p q := by
  exact expectedJ_le_of_scale_le M L (m - 1) m (Nat.sub_le m 1) p q

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
