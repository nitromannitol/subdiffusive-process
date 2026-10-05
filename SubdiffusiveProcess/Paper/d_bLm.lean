module

public import SubdiffusiveProcess.Frozen.Vocab.TailCoefficient

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Definition `d.bLm`, the coefficient `b_{L,m} := ahom_{m∧L} · a_L / a_{m∧L}`, as a coefficient field
`x ↦ b_{L,m}(x)` of the sample `ω` of the layers, for the standing model `M`
(`a_L = SubdiffusiveProcess.Model.aCutoff M L ω`, `ahom_m = SubdiffusiveProcess.CoarseGrainingVocab.ahom M m`).
It agrees with the frozen vocabulary `SubdiffusiveProcess.CoarseGrainingVocab.tailCoefficient` (used by
`l.ellipticity.bound`); the helper lemmas record the two closed forms displayed after the definition. -/
def d_bLm {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Homogenization.Vec d) : ℝ :=
  ahom M (min m L) *
    (_root_.SubdiffusiveProcess.Model.aCutoff M L ω x / _root_.SubdiffusiveProcess.Model.aCutoff M (min m L) ω x)

/-- `b_{L,m}` is the frozen `tailCoefficient`. -/
theorem aux_d_bLm_eq_tailCoefficient {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Homogenization.Vec d) :
    d_bLm M L m ω x = tailCoefficient M L m ω x := rfl

/-- `m ≥ L`: `b_{L,m} = ahom_L`. -/
theorem aux_d_bLm_of_ge {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ}
    (h : L ≤ m) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Homogenization.Vec d) :
    d_bLm M L m ω x = ahom M L := by
  unfold d_bLm _root_.SubdiffusiveProcess.Model.aCutoff
  rw [min_eq_right h, div_self (Real.exp_pos _).ne', mul_one]

/-- `m ≤ L`: `b_{L,m} = ahom_m · exp (∑_{j=m+1}^{L} (g_j - τ²))`. -/
theorem aux_d_bLm_of_le {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ}
    (h : m ≤ L) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Homogenization.Vec d) :
    d_bLm M L m ω x =
      ahom M m * Real.exp (∑ j ∈ Finset.Ioc m L,
        (ω j x - _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
  unfold d_bLm _root_.SubdiffusiveProcess.Model.aCutoff
  rw [min_eq_left h, ← Real.exp_sub, ← Finset.Ico_add_one_add_one_eq_Ioc,
    ← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ h)]
  rfl

end SubdiffusiveProcess.Paper
