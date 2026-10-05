module

public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_J_responseJ_isLUB (d : ℕ) (hd : 2 ≤ d) :
    (∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.Book.Ch02.CoeffOn U) (p q : Homogenization.Vec d),
      IsLUB (Homogenization.Book.Ch02.responseValueSet U a p q)
        (Homogenization.Book.Ch02.responseJ U a p q)) := by
  have _hd : 2 ≤ d := hd
  intro U a p q
  let b : Homogenization.Book.Ch02.CoeffOn U :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  have hb : Homogenization.Book.Ch02.CoeffOn.AEEq b a := by
    simpa [b] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hEll :
      Homogenization.IsEllipticFieldOn b.lam b.Lam (U : Set (Homogenization.Vec d))
        b.toCoeffField := by
    simpa [b] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hfinite : MeasureTheory.volume (U : Set (Homogenization.Vec d)) ≠ ⊤ := by
    exact isFiniteMeasure_restrict.mp
      (show MeasureTheory.IsFiniteMeasure
        (Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))) from inferInstance)
  have hvol : (MeasureTheory.volume (U : Set (Homogenization.Vec d))).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr
      ⟨U.isOpen.measure_ne_zero MeasureTheory.volume U.nonempty, hfinite⟩
  have hbdB : BddAbove (Homogenization.Book.Ch02.responseValueSet U b p q) := by
    change BddAbove
      (Homogenization.responseJValueSet (U : Set (Homogenization.Vec d)) p q
        b.toCoeffField)
    exact Homogenization.responseJValueSet_bddAbove_of_isEllipticFieldOn hEll hvol p q
  have hbd : BddAbove (Homogenization.Book.Ch02.responseValueSet U a p q) := by
    rw [← Homogenization.Book.Ch02.responseValueSet_eq_ofAEEq hb p q]
    exact hbdB
  constructor
  · intro m hm
    unfold Homogenization.Book.Ch02.responseJ
    exact le_csSup hbd hm
  · intro c hc
    unfold Homogenization.Book.Ch02.responseJ
    exact csSup_le (Homogenization.Book.Ch02.responseValueSet_nonempty U a p q) hc

end SubdiffusiveProcess.Paper

