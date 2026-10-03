module

public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Lane2.LimitForm
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper



theorem zero_endpoint_gap
    (d : ℕ) (hd : 2 ≤ d)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℕ → Opens (SpatialCoordinates d))
    (hQ : ∀ n, ∃ z r, ∃ hr : 0 < r, Q n = centeredCube z r hr)
    (GE GF : (n : ℕ) → Ω → DomainL2 (Q n) →L[ℝ] DomainL2 (Q n))
    (m M : Ω → ℝ) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hbounds : ∀ᵐ ω ∂P, C0⁻¹ ≤ m ω ∧ m ω ≤ M ω ∧ M ω ≤ C0)
    (horders : ∀ᵐ ω ∂P, ∀ n,
      limitFormDomain (GE n ω) = limitFormDomain (GF n ω) ∧
      (∀ u : DomainL2 (Q n), u ∈ limitFormDomain (GE n ω) →
        (m ω * (limitFormEnergy (GE n ω) u).toReal ≤
          (limitFormEnergy (GF n ω) u).toReal ∧
        (limitFormEnergy (GF n ω) u).toReal ≤
          M ω * (limitFormEnergy (GE n ω) u).toReal)))
    (hdet : ∃ c : ℝ, ∀ᵐ ω ∂P, m ω = c)
    (hzero : ∀ᵐ ω ∂P, M ω - m ω = 0) :
    ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧
      (∀ᵐ ω ∂P, m ω = c ∧
        (∀ n, limitFormDomain (GE n ω) = limitFormDomain (GF n ω) ∧
          (∀ u : DomainL2 (Q n), u ∈ limitFormDomain (GE n ω) →
            (limitFormEnergy (GF n ω) u).toReal =
              c * (limitFormEnergy (GE n ω) u).toReal))) := by
  obtain ⟨c, hc⟩ := hdet
  haveI : (ae P).NeBot := IsProbabilityMeasure.ae_neBot
  refine ⟨c, ?_, ?_, ?_⟩
  · obtain ⟨ω, hωc, hωb⟩ := (hc.and hbounds).exists
    exact le_of_le_of_eq hωb.1 hωc
  · obtain ⟨ω, hωc, hωb, hωz⟩ := (hc.and (hbounds.and hzero)).exists
    have hM : M ω = m ω := sub_eq_zero.mp hωz
    exact le_of_eq_of_le (hM.trans hωc).symm hωb.2.2
  · filter_upwards [hbounds, horders, hc, hzero] with ω hb ho hcm hz
    have hM : M ω = c := (sub_eq_zero.mp hz).trans hcm
    refine ⟨hcm, fun n => ⟨(ho n).1, fun u hu => ?_⟩⟩
    have h1 := (ho n).2 u hu
    rw [hcm, hM] at h1
    exact le_antisymm h1.2 h1.1


end Paper
