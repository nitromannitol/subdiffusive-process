module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothRange

@[expose] public section

/-!
# Dense range for the GMC pairs, and the frozen datum from decay alone

The coefficient `coefficientAt M L omega` 
(finite cutoff) and `:49-79` (anchored limit) is the exponential of a finite sum
of potential-field layers, respectively of the anchored `C¹ˑ¹` limit.  Every
layer, and the limit, is a `PotentialField`, which by construction carries a
continuous derivative; so the coefficient is `C¹` at every `L : WithTop ℕ`.

That is exactly the hypothesis of
`hasDenseMassiveResolventRange_of_contDiff`, so
`HasDenseMassiveResolventRange` holds for both of the paper's pairs `(a, a)` and
`(a, 1)`.

## Main declarations

* `contDiff_one_coefficientAt` — the GMC coefficient is `C¹`.
* `hasDenseMassiveResolventRange_reversible`, `..._divergence`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ### The GMC coefficient is `C¹` -/

theorem contDiff_one_aAnchored (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    ContDiff ℝ 1 (_root_.SubdiffusiveProcess.Model.aAnchored M omega) :=
  (_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one
    (_root_.SubdiffusiveProcess.Model.anchoredLog omega)).exp

theorem contDiff_one_aCutoff (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ContDiff ℝ 1 (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) := by
  have hsum : ContDiff ℝ 1 (fun x : Vec d ↦
      ∑ k ∈ Finset.range (L + 1), (omega k x - _root_.SubdiffusiveProcess.Model.tauSq M.P)) :=
    ContDiff.sum fun k _ ↦
      (_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (omega k)).sub contDiff_const
  exact hsum.exp

theorem contDiff_one_coefficientAt (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    ContDiff ℝ 1 (coefficientAt M L omega) := by
  cases L with
  | top => exact contDiff_one_aAnchored M omega
  | coe n => exact contDiff_one_aCutoff M n omega.1

/-! ### Dense range for the paper's two pairs -/

/-- **Dense range for the reversible pair `(a, a)`.** -/
theorem hasDenseMassiveResolventRange_reversible [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    HasDenseMassiveResolventRange (coefficientAt M L omega) (coefficientAt M L omega) :=
  hasDenseMassiveResolventRange_of_contDiff (reversibleMassiveCubeBounds M L omega)
    (contDiff_one_coefficientAt M L omega) (continuous_coefficientAt M L omega)

/-- **Dense range for the divergence pair `(a, 1)`.** -/
theorem hasDenseMassiveResolventRange_divergence [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    HasDenseMassiveResolventRange (coefficientAt M L omega) (fun _ ↦ (1 : ℝ)) :=
  hasDenseMassiveResolventRange_of_contDiff (divergenceMassiveCubeBounds M L omega)
    (contDiff_one_coefficientAt M L omega) continuous_const

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
