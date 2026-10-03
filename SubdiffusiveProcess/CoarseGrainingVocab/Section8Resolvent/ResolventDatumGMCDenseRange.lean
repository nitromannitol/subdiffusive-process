module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothRange

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ### The GMC coefficient is `C¹` -/

theorem contDiff_one_aAnchored (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    ContDiff ℝ 1 (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega) :=
  (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.contDiff_one
    (SubdiffusiveProcess.Frozen.Assumptions.anchoredLog omega)).exp

theorem contDiff_one_aCutoff (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    ContDiff ℝ 1 (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := by
  have hsum : ContDiff ℝ 1 (fun x : Vec d ↦
      ∑ k ∈ Finset.range (L + 1), (omega k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) :=
    ContDiff.sum fun k _ ↦
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.contDiff_one (omega k)).sub contDiff_const
  exact hsum.exp

theorem contDiff_one_coefficientAt (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    ContDiff ℝ 1 (coefficientAt M L omega) := by
  cases L with
  | top => exact contDiff_one_aAnchored M omega
  | coe n => exact contDiff_one_aCutoff M n omega.1

/-! ### Dense range for the paper's two pairs -/

/-- **Dense range for the reversible pair `(a, a)`.** -/
theorem hasDenseMassiveResolventRange_reversible [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    HasDenseMassiveResolventRange (coefficientAt M L omega) (coefficientAt M L omega) :=
  hasDenseMassiveResolventRange_of_contDiff (reversibleMassiveCubeBounds M L omega)
    (contDiff_one_coefficientAt M L omega) (continuous_coefficientAt M L omega)

/-- **Dense range for the divergence pair `(a, 1)`.** -/
theorem hasDenseMassiveResolventRange_divergence [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    HasDenseMassiveResolventRange (coefficientAt M L omega) (fun _ ↦ (1 : ℝ)) :=
  hasDenseMassiveResolventRange_of_contDiff (divergenceMassiveCubeBounds M L omega)
    (contDiff_one_coefficientAt M L omega) continuous_const

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
