module

public import SubdiffusiveProcess.Static.LocalEstimateClauses
public import SubdiffusiveProcess.Frozen.Section6.Defs.CoefficientAt
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-! # Native finite-prefix harmonic cell estimate consumed by mesh normalization -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open _root_.SubdiffusiveProcess.Model

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Global smooth datum bounds in the normalized cell coordinates. -/
def HarmonicCutoffDatumSizeBound {d : ℕ} (f : Vec d → ℝ) (B : ℝ) : Prop :=
  ∀ x, |f x| ≤ B ∧ ‖fderiv ℝ f x‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B

/-- The native restriction of a smooth compactly supported unit-cell datum. -/
def cutoffHarmonicCellDatum {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    H1Function (openCubeSet (originCube d 0)) :=
  H1Function.ofContDiff (isOpen_openCubeSet _) (hf.of_le (by simp)) hc

/-- Literal all-radius growth in a physical cell of side `3^k`. For negative
physical scales the finite prefix is zero. The gradient is the native weak
representative, and faces and corners are included in the truncated ball. -/
def CutoffHarmonicCellGrowth {d : ℕ} (M : GMCModel d) (j : ℕ) (k : ℤ)
    (z : Vec d) (omega : PotentialSample d) (K : ℝ) : Prop :=
  ∀ (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (B : ℝ), 0 ≤ B → HarmonicCutoffDatumSizeBound f B →
    ∀ u : H1Function (openCubeSet (originCube d 0)),
      IsWeaklyHarmonicOn
        (fun x => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ k • x))
        (openCubeSet (originCube d 0)) u →
      HasZeroTraceDifferenceOn (openCubeSet (originCube d 0)) u
        (cutoffHarmonicCellDatum f hf hc) →
      ∀ x ∈ openCubeSet (originCube d 0), ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
          ENNReal.ofReal ((ahom M j)⁻¹ *
            aCutoff M j omega (z + (3 : ℝ) ^ k • y) * vecDot (u.grad y) (u.grad y)) ≤
          ENNReal.ofReal (K * B ^ 2 * r ^ ((d : ℝ) - 1 / 2))

end SubdiffusiveProcess.Static
