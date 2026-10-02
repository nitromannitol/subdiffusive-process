import SubdiffusiveProcess.Analysis.EquicontinuousMeasureReadout
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Ring.Real

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Analysis

/-- A continuous L² family with a common spatial modulus has continuous
pointwise representatives on the open carrier. -/
theorem continuous_representative_readout_of_continuous_Lp
    {X S : Type*} [TopologicalSpace X] [SequentialSpace X]
    [MetricSpace S] [MeasurableSpace S]
    (nu : Measure S) (Q : Set S) (hQ : IsOpen Q)
    (hpos : ∀ x ∈ Q, ∀ delta : ℝ, 0 < delta → 0 < nu (Metric.ball x delta))
    (u : X → Lp ℝ 2 nu) (hu : Continuous u)
    (R : X → S → ℝ) (hR : ∀ a, R a =ᵐ[nu] (u a : S → ℝ))
    (L : X → ℝ) (hL : Continuous L)
    (modulus : ℝ → ℝ) (hmod0 : modulus 0 = 0) (hmodc : ContinuousAt modulus 0)
    (hmodnn : ∀ r, 0 ≤ r → 0 ≤ modulus r)
    (hholder : ∀ a y, y ∈ Q → ∀ x, x ∈ Q →
      |R a y - R a x| ≤ L a * modulus (dist y x))
    (x : S) (hx : x ∈ Q) : Continuous (fun a => R a x) := by
  apply continuous_iff_seqContinuous.mpr
  intro as a has
  have hU := (hu.tendsto a).comp has
  have hprob : TendstoInMeasure nu (fun n => R (as n)) atTop (R a) :=
    (tendstoInMeasure_of_tendsto_Lp hU).congr
      (fun n => (hR (as n)).symm) (hR a).symm
  have hLs : Tendsto (fun n => L (as n)) atTop (𝓝 (L a)) := (hL.tendsto a).comp has
  obtain ⟨C, _hC, hCb⟩ :=
    (Metric.isBounded_range_of_tendsto (fun n => L (as n)) hLs).exists_pos_norm_le
  let B := max C |L a|
  have hB : 0 ≤ B := (abs_nonneg _).trans (le_max_right _ _)
  have hLa : L a ≤ B := (le_abs_self _).trans (le_max_right _ _)
  have hLan (n : ℕ) : L (as n) ≤ B := by
    apply (le_abs_self _).trans
    apply le_trans _ (le_max_left _ _)
    simpa only [Real.norm_eq_abs] using hCb _ ⟨n, rfl⟩
  apply tendsto_at_support_of_tendstoInMeasure_of_common_modulus nu
    (fun n => R (as n)) (R a) hprob x (hpos x hx)
  intro eps heps
  have hc : ContinuousAt (fun y : S => B * modulus (dist y x)) x := by
    have hd : ContinuousAt (fun y : S => dist y x) x :=
      (continuous_id.dist continuous_const).continuousAt
    have hm : ContinuousAt modulus (dist x x) := by simpa only [dist_self] using hmodc
    have hh : ContinuousAt (fun y : S => modulus (dist y x)) x :=
      ContinuousAt.comp (f := fun y : S => dist y x) hm hd
    exact continuousAt_const.mul hh
  have hv : B * modulus (dist x x) = 0 := by rw [dist_self, hmod0, mul_zero]
  obtain ⟨delta, hdelta, hsmall⟩ := Metric.continuousAt_iff.mp hc eps heps
  obtain ⟨deltaQ, hdeltaQ, hsubset⟩ := Metric.isOpen_iff.mp hQ x hx
  refine ⟨min delta deltaQ, lt_min hdelta hdeltaQ, ?_⟩
  intro y hy
  have hyD : dist y x < delta := (Metric.mem_ball.mp hy).trans_le (min_le_left _ _)
  have hyQ : y ∈ Q := hsubset ((Metric.mem_ball.mp hy).trans_le (min_le_right _ _))
  have hm : B * modulus (dist y x) < eps := by
    have h := hsmall hyD
    rw [hv, Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hB (hmodnn _ dist_nonneg))] at h
    exact h
  constructor
  · intro n
    apply (hholder (as n) y hyQ x hx).trans_lt
    exact (mul_le_mul_of_nonneg_right (hLan n) (hmodnn _ dist_nonneg)).trans_lt hm
  · apply (hholder a y hyQ x hx).trans_lt
    exact (mul_le_mul_of_nonneg_right hLa (hmodnn _ dist_nonneg)).trans_lt hm

end SubdiffusiveProcess.Analysis
