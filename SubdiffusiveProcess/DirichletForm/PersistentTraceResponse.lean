module

public import SubdiffusiveProcess.DirichletForm.ContinuousTraceResponse
public import SubdiffusiveProcess.Sobolev.UniformCubeLimit
public import SubdiffusiveProcess.Compactness.UniformRefinement

@[expose] public section

/-! Persistent, bounded-energy approximants with converging boundary values
produce a continuous limiting trace witness. No approximating sequence is constructed here. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal
noncomputable section
namespace SubdiffusiveProcess.DirichletForm.EnergyMeasure

/-- Persistent approximants preserve a local response cap while their boundary errors tend to zero. -/
theorem continuousTraceValues_of_persistent_approximation
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {E : ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))}
    (Gamma : EnergyMeasure E) (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (hBS : frontier B ⊆ closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    (u : ℕ → DomainL2 (centeredCube z r hr)) (hu : ∀ n, u n ∈ E.domain)
    (V : ℕ → SpatialCoordinates d → ℝ) (b : SpatialCoordinates d → ℝ)
    (hVc : ∀ n, ContinuousOn (V n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hrep : ∀ n, (u n : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] V n)
    (eps : ℕ → ℝ) (heps : ∀ n, 0 ≤ eps n) (hzero : Tendsto eps atTop (𝓝 0))
    (hRefine : ∀ n m, n ≤ m → ∀ x,
      x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) →
      V m x = V n x ∨ (|V n x - b x| ≤ eps n ∧ |V m x - b x| ≤ eps n))
    (hTrace : TendstoUniformlyOn V b atTop (frontier B))
    (E0 K : ℝ) (hEnergy : ∀ n, E.form (u n) (u n) ≤ E0)
    (hLocal : ∀ n, (Gamma.measure (u n) B).toReal ≤ K) :
    (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d))) B b).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d))) B b)
        (sInf (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d))) B b)) ∧
      sInf (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d))) B b) ≤ K := by
  classical
  let Q := centeredCube z r hr
  let F : ℕ → closure (Q : Set (SpatialCoordinates d)) → ℝ := fun n x => V n x
  let compactQ : CompactSpace (closure (Q : Set (SpatialCoordinates d))) :=
    isCompact_iff_compactSpace.mp (centeredCube_isBounded z hr).isCompact_closure
  have hFc : ∀ n, Continuous (F n) := fun n =>
    continuousOn_iff_continuous_domRestrict.mp (hVc n)
  obtain ⟨g, hgc, hlim⟩ := exists_uniform_limit_of_persistent_refinement F hFc
    (fun x => b x) eps heps hzero (fun n m hnm x => hRefine n m hnm x x.property)
  obtain ⟨v, vc, hvc, hvr, hveq⟩ :=
    exists_cubeL2_of_continuous_closedCube z hr ⟨g, hgc⟩
  have hUniform : TendstoUniformly (fun n (x : closure (Q : Set (SpatialCoordinates d))) => V n x)
      (fun x => vc x) atTop := by
    convert hlim using 1
    exact funext (fun x => hveq x x.property)
  have hUniformOn : TendstoUniformlyOn (fun n => V n) vc atTop
      (closure (Q : Set (SpatialCoordinates d))) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    exact hUniform
  have hL2 : Tendsto (fun n => u n) atTop (𝓝 v) :=
    cube_tendsto_of_uniformly_on z hr (fun n => V n) (fun n => u n)
      (fun n => hrep n) vc v hvr hUniform
  exact Gamma.continuousTraceValues_of_tendsto (closure (Q : Set (SpatialCoordinates d))) B hB hBS
    (by
      filter_upwards [self_mem_ae_restrict Q.isOpen.measurableSet] with x hx
      exact subset_closure hx)
    (fun n => u n) (fun n => hu n) v hL2
    (fun n => V n) (fun n => V n) vc b
    (fun n => hVc n) (fun n => hrep n) hUniformOn hTrace
    (fun _ _ _ => rfl) E0 K (fun n => hEnergy n) (fun n => hLocal n)

end SubdiffusiveProcess.DirichletForm.EnergyMeasure
