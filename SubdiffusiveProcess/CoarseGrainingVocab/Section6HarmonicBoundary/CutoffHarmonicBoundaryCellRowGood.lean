
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRowGood
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicBoundaryCellRow

@[expose] public section

/-!
# The good-event form of the boundary-cell row, at a finite cutoff

Cutoff companions of `Section6HarmonicBoundary.BoundaryCellManuscriptRowGood`
and `Section6HarmonicBoundary.boundaryCellManuscriptRow_of_good`: the binder
`m ≤ L` is deleted and the good event is `𝒢^{(L)}_{n+2,z}`.  The single changed
leaf is the cutoff error cap (through `Section6CutoffHarmonic.CutoffHarmonicLeaves`).

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The good-event form of the boundary-cell manuscript row.**

Identical to `BoundaryCellManuscriptRow` except that the four printed budgets
may be multiplied by `1 + 𝓔`, where `𝓔` is the local Section 6 homogenization
error appearing in the first leg of the frozen v6 comparison clause.  This is
the weakest row that any comparator-based route can be expected to produce. -/
def BoundaryCellManuscriptRowGood (d : ℕ) (Cboundary : ℝ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (sOrder : FractionalOrder),
    sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
  ∀ (L m n : ℕ), n + 5 ≤ m →
  ∀ (z x q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
    z ∈ cube d (m : ℤ) →
    x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
    q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
    ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
    omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
  ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d),
    IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (originCube d (m : ℤ)) u h g →
    Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
    MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
    normalizedSetAverage (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)
        (fun p ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
          vecNormSq (u.grad p)) ≤
      Cboundary *
        (1 + section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z) *
        harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g

/-- **The `(1 + 𝓔)` weakening is free.**

On the frozen v6 good event — amplitude `1` — the proved
`p.good.scale.mathcal.E` export caps `𝓔` by a dimension-only constant, so the
honest row implies the constant-coefficient row with the constant enlarged by
`1 + C(d)`. -/
theorem boundaryCellManuscriptRow_of_good (d : ℕ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hrow : BoundaryCellManuscriptRowGood d Cb) :
    ∃ Cb' : ℝ, 0 ≤ Cb' ∧ BoundaryCellManuscriptRow d Cb' := by
  obtain ⟨Cerr, hCerr0, hcap⟩ :=
    exists_section6HomogenizationError_le_of_goodEvent (d := d)
  refine ⟨Cb * (1 + Cerr), mul_nonneg hCb (by linarith), ?_⟩
  intro M sOrder hs L m n hnm z x q omega hz hx hq hbd hgood u h g hdir hg hh
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < sOrder.1 :=
    (mul_pos (by norm_num : (0 : ℝ) < 512) (pow_pos hdelta 2)).trans_le hs.1
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hB : 0 ≤ harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g :=
    harmonicPhysicalFourBudgets_nonneg M L m n z x omega hs0 hsigma.le u h g
  have hE : section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z ≤ Cerr :=
    hcap M sOrder.1 hs L (n + 2) omega z hgood
  have hstep := hrow M sOrder hs L m n hnm z x q omega hz hx hq hbd hgood
    u h g hdir hg hh
  refine hstep.trans ?_
  have hmono : Cb *
      (1 + section6HomogenizationError M (sOrder.1 / 8) L (n + 2) omega z) ≤
      Cb * (1 + Cerr) :=
    mul_le_mul_of_nonneg_left (by linarith) hCb
  exact mul_le_mul_of_nonneg_right hmono hB

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
