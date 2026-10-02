import SubdiffusiveProcess.DirichletForm.EnergyMeasure

/-! Midpoint minimality forces two local minimizers to have zero difference
energy on the observation set. Coercivity or boundary identification is separate. -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DirichletForm.EnergyMeasure

/-- If neither endpoint has more local energy than their midpoint, their difference has zero local energy. -/
theorem measure_sub_eq_zero_of_midpoint_minimal
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}
    {E : ClosedForm mu} (Gamma : EnergyMeasure E)
    (u v : Lp ℝ 2 mu) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (q : Set X) (hq : MeasurableSet q)
    (huM : (Gamma.measure u q).toReal ≤
      (Gamma.measure ((1 / 2 : ℝ) • (u + v)) q).toReal)
    (hvM : (Gamma.measure v q).toReal ≤
      (Gamma.measure ((1 / 2 : ℝ) • (u + v)) q).toReal) :
    Gamma.measure (u - v) q = 0 := by
  have huv := E.domain.add_mem hu hv
  have hm := E.domain.smul_mem (1 / 2 : ℝ) huv
  have hd := E.domain.sub_mem hu hv
  have hmid : (Gamma.measure ((1 / 2 : ℝ) • (u + v)) q).toReal =
      (1 / 4 : ℝ) * ((Gamma.measure u q).toReal +
        2 * Gamma.cross u v q + (Gamma.measure v q).toReal) := by
    rw [← Gamma.cross_self _ hm q hq, Gamma.cross_smul_left _ huv hm,
      Gamma.cross_smul_right _ _ huv _ huv, VectorMeasure.smul_apply,
      VectorMeasure.smul_apply, smul_eq_mul, smul_eq_mul,
      Gamma.cross_add_self_apply hu hv,
      Gamma.cross_self u hu q hq, Gamma.cross_self v hv q hq]
    ring
  have hdiff := Gamma.cross_sub_self_apply hu hv q
  rw [Gamma.cross_self (u - v) hd q hq, Gamma.cross_self u hu q hq,
    Gamma.cross_self v hv q hq] at hdiff
  have hzero : (Gamma.measure (u - v) q).toReal = 0 := by
    have hnonneg := ENNReal.toReal_nonneg (a := Gamma.measure (u - v) q)
    linarith only [huM, hvM, hmid, hdiff, hnonneg]
  exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right (Gamma.measure_ne_top hd q)

end DirichletForm.EnergyMeasure
