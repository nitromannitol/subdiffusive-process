import SubdiffusiveProcess.DirichletForm.PersistentTraceResponse
import SubdiffusiveProcess.Geometry.BoundaryPartitionLimits

/-! Actual finite-partition witnesses yield an arbitrary-cell trace response through
persistent refinement and closedness. The witnesses and their energy costs are inputs. -/
open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology BigOperators ENNReal
noncomputable section
namespace DirichletForm.EnergyMeasure
attribute [local instance] Classical.propDecidable

/-- Bounded partition costs and persistent cell limits give a continuous trace witness with the local packing bound. -/
theorem continuousTraceValues_of_boundary_refinement
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    {E : ClosedForm (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)))}
    (Gamma : EnergyMeasure E) (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (r s C : ℝ) (hr : 0 < r) (minLevel : ℕ)
    (P : TriadicBoundaryPartitions z R hR B r s C minLevel)
    (alpha H A : ℝ) (ha : 0 < alpha) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (b : SpatialCoordinates d → ℝ)
    (v : ℕ → DomainL2 (centeredCube z R hR)) (hv : ∀ n, v n ∈ E.domain)
    (V : ℕ → SpatialCoordinates d → ℝ)
    (hVc : ∀ n, ContinuousOn (V n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hrep : ∀ n, (v n : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))] V n)
    (Vcell : TriadicGridLabel d → SpatialCoordinates d → ℝ)
    (hEq : ∀ n i, EqOn (V n) (Vcell (P.label n i))
      (closure (triadicGridCell z R hR (P.label n i) : Set (SpatialCoordinates d))))
    (hOsc : ∀ n i x, x ∈ closure (triadicGridCell z R hR (P.label n i) : Set (SpatialCoordinates d)) →
      |V n x - b x| ≤ H * (triadicGridSide R (P.label n i)) ^ alpha)
    (hEnergy : ∀ n, E.form (v n) (v n) ≤ A * ∑ i, (triadicGridSide R (P.label n i)) ^ s)
    (hLocal : ∀ n, (Gamma.measure (v n) B).toReal ≤ A * ∑ i,
      if ((triadicGridCell z R hR (P.label n i) : Set (SpatialCoordinates d)) ∩ B).Nonempty
      then (triadicGridSide R (P.label n i)) ^ s else 0) :
    (Gamma.continuousTraceValues (closure (centeredCube z R hR : Set (SpatialCoordinates d))) B b).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues (closure (centeredCube z R hR : Set (SpatialCoordinates d))) B b)
        (sInf (Gamma.continuousTraceValues (closure (centeredCube z R hR : Set (SpatialCoordinates d))) B b)) ∧
      sInf (Gamma.continuousTraceValues (closure (centeredCube z R hR : Set (SpatialCoordinates d))) B b) ≤
        A * C * r ^ s := by
  classical
  obtain ⟨K, _, hK⟩ := P.total
  let eps : ℕ → ℝ := fun n => H * (r * (3 : ℝ) ^ (-(n : ℤ))) ^ alpha
  have heps : ∀ n, 0 ≤ eps n := fun n =>
    mul_nonneg hH (Real.rpow_nonneg (mul_nonneg hr.le (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le) _)
  have hzero : Tendsto eps atTop (𝓝 0) := triadic_holder_error_tendsto_zero H r alpha ha
  have hBS : frontier B ⊆ closure (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    intro x hx
    obtain ⟨i, hxi, _⟩ := P.boundary 0 x hx
    exact closure_mono (triadicGridCell_subset z hR (P.label 0 i)) hxi
  have hEtot : ∀ n, E.form (v n) (v n) ≤ A * K := fun n =>
    (hEnergy n).trans (mul_le_mul_of_nonneg_left (hK n) hA)
  have hEloc : ∀ n, (Gamma.measure (v n) B).toReal ≤ A * C * r ^ s := by
    intro n
    exact (hLocal n).trans ((mul_le_mul_of_nonneg_left (P.local_bound n) hA).trans_eq (mul_assoc A C (r ^ s)).symm)
  exact Gamma.continuousTraceValues_of_persistent_approximation z R hR B hB hBS
    v hv V b hVc hrep eps heps hzero
    (P.refinement_error ha.le hH V Vcell b hEq hOsc)
    (P.tendstoUniformlyOn_frontier ha hH V b hOsc) (A * K) (A * C * r ^ s) hEtot hEloc

end DirichletForm.EnergyMeasure
