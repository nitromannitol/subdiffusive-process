module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Scalar measurability of a symmetric operator's quadratic evaluations implies
measurability of every mixed pairing. No operator-valued measurability is asserted. -/

open MeasureTheory

namespace SubdiffusiveProcess

/-- Real polarization determines a symmetric operator's mixed pairing from three quadratic values. -/
theorem symmetric_operator_pairing_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hs : ∀ x y, inner ℝ x (T y) = inner ℝ y (T x)) (x y : E) :
    inner ℝ x (T y) =
      (inner ℝ (x + y) (T (x + y)) - inner ℝ x (T x) - inner ℝ y (T y)) / 2 := by
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hs y x]
  ring

/-- Measurable quadratic evaluations of symmetric real operators give measurable mixed pairings. -/
theorem measurable_symmetric_operator_pairing
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Ω → E →L[ℝ] E) (hs : ∀ omega x y, inner ℝ x (T omega y) = inner ℝ y (T omega x))
    (hm : ∀ x, Measurable (fun omega => inner ℝ x (T omega x))) (x y : E) :
    Measurable (fun omega => inner ℝ x (T omega y)) := by
  have he : (fun omega => inner ℝ x (T omega y)) = fun omega =>
      (inner ℝ (x + y) (T omega (x + y)) - inner ℝ x (T omega x) -
        inner ℝ y (T omega y)) / 2 :=
    funext fun omega => symmetric_operator_pairing_eq (T omega) (hs omega) x y
  rw [he]
  exact (((hm (x + y)).sub (hm x)).sub (hm y)).div_const 2

end SubdiffusiveProcess
