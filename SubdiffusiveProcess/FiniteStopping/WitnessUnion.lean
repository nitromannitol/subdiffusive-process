import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic
import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison

/-! This module establishes step6 union for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- step6 union in the finite stopping construction. -/
theorem step6_union
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (Pmeas : Measure (BilateralField d)) (k : ℤ) (Bc : ℝ) (hBc : 0 < Bc)
    (W1 W2 W3 W4 : ℕ+ → Set (BilateralField d))
    (hmeas1 : ∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
        ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).restrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))]
        (W1 h))
    (hmeas2 : ∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
        ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).restrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))]
        (W2 h))
    (hmeas3 : ∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
        ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).restrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))]
        (W3 h))
    (hmeas4 : ∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
        ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).restrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))]
        (W4 h))
    (hP1 : ∀ h : ℕ+, Pmeas (W1 h) ≤
      ENNReal.ofReal (Real.exp (-((Bc + Real.log 2) + Real.log 2) * (h : ℝ))))
    (hP2 : ∀ h : ℕ+, Pmeas (W2 h) ≤
      ENNReal.ofReal (Real.exp (-((Bc + Real.log 2) + Real.log 2) * (h : ℝ))))
    (hP3 : ∀ h : ℕ+, Pmeas (W3 h) ≤
      ENNReal.ofReal (Real.exp (-((Bc + Real.log 2) + Real.log 2) * (h : ℝ))))
    (hP4 : ∀ h : ℕ+, Pmeas (W4 h) ≤
      ENNReal.ofReal (Real.exp (-((Bc + Real.log 2) + Real.log 2) * (h : ℝ)))) :
    ∃ W : ℕ+ → Set (BilateralField d),
      (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))]
          (W h)) ∧
      (∀ h : ℕ+, Pmeas (W h) ≤ ENNReal.ofReal (Real.exp (-Bc * (h : ℝ)))) ∧
      ((⋃ h : ℕ+, W h) =
        ((⋃ h : ℕ+, W1 h) ∪ (⋃ h : ℕ+, W2 h)) ∪ ((⋃ h : ℕ+, W3 h) ∪ (⋃ h : ℕ+, W4 h))) := by
  have hBc2 : 0 < Bc + Real.log 2 := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith only [hBc, hlog2]
  obtain ⟨W12, hmeas12, hP12, hU12⟩ :=
    SubdiffusiveProcess.FiniteStopping.trace_witness_union_two Pmeas k (Bc + Real.log 2) hBc2
      W1 W2 hmeas1 hmeas2 hP1 hP2
  obtain ⟨W34, hmeas34, hP34, hU34⟩ :=
    SubdiffusiveProcess.FiniteStopping.trace_witness_union_two Pmeas k (Bc + Real.log 2) hBc2
      W3 W4 hmeas3 hmeas4 hP3 hP4
  obtain ⟨W, hmeasW, hPW, hUW⟩ :=
    SubdiffusiveProcess.FiniteStopping.trace_witness_union_two Pmeas k Bc hBc
      W12 W34 hmeas12 hmeas34 hP12 hP34
  exact ⟨W, hmeasW, hPW, by rw [hUW, hU12, hU34]⟩

end SubdiffusiveProcess.FiniteStopping
