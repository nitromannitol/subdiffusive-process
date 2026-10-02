import SubdiffusiveProcess.Sobolev.NativeH1
import SubdiffusiveProcess.Sobolev.KilledGraph

open MeasureTheory Set TopologicalSpace

namespace SubdiffusiveProcess

/-- A local killed Sobolev datum has the native zero-trace carrier with exactly its function and gradient representatives. -/
theorem exists_nativeH10Function_of_killedSobolevGraph
    {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (u : killedSobolevGraph Ω) :
    ∃ v : Homogenization.H10Function (Ω : Set (SpatialCoordinates d)),
      (v : SpatialCoordinates d → ℝ) = (fun x => u.val.1 x) ∧
      v.toH1Function.grad = (fun x i => u.val.2 i x) := by
  classical
  obtain ⟨v, hv_val, hv_grad⟩ :=
    exists_nativeH1Function_of_weakSobolevGraph
      (⟨u.val, killedSobolevGraph_le_weakSobolevGraph u.property⟩)
  have hu_closure :
      u.val ∈ closure
        ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) :
          Set (SobolevData Ω)) := by
    simpa [killedSobolevGraph, Submodule.topologicalClosure_coe] using u.property
  obtain ⟨z, hz, hzlim⟩ := mem_closure_iff_seq_limit.mp hu_closure
  choose φ hφ using hz
  have hval_tendsto :
      Filter.Tendsto (fun n => testL2 (φ n)) Filter.atTop
        (nhds u.val.1) := by
    apply (hzlim.fst_nhds).congr'
    filter_upwards [] with n
    change (z n).1 = (smoothSobolevData (φ n)).1
    exact (congrArg Prod.fst (hφ n)).symm
  have hgrad_tendsto :
      ∀ i : Fin d, Filter.Tendsto (fun n => testPartialL2 (φ n) i)
        Filter.atTop (nhds (u.val.2 i)) := by
    intro i
    have hi : Filter.Tendsto (fun n => (z n).2 i) Filter.atTop
        (nhds (u.val.2 i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hzlim.snd_nhds
    apply hi.congr'
    filter_upwards [] with n
    change (z n).2 i = (smoothSobolevData (φ n)).2 i
    exact (congrArg (fun q : SobolevData Ω => q.2 i) (hφ n)).symm
  have hval_norm (ψ : TestFunction Ω ℝ ⊤) :
      eLpNorm (fun x => (ψ : SpatialCoordinates d → ℝ) x - v.toFun x) 2
          (volume.restrict (Ω : Set (SpatialCoordinates d))) =
        edist (testL2 ψ) u.val.1 := by
    rw [hv_val, MeasureTheory.Lp.edist_def]
    refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
    filter_upwards [testL2_coeFn ψ] with x hx
    simp only [Pi.sub_apply, hx]
  have hgrad_norm (ψ : TestFunction Ω ℝ ⊤) (i : Fin d) :
      eLpNorm
          (fun x => (fderiv ℝ (ψ : SpatialCoordinates d → ℝ) x)
              (Homogenization.basisVec i) - v.grad x i) 2
          (volume.restrict (Ω : Set (SpatialCoordinates d))) =
        edist (testPartialL2 ψ i) (u.val.2 i) := by
    rw [hv_grad, MeasureTheory.Lp.edist_def]
    refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
    filter_upwards [testPartialL2_coeFn ψ i] with x hx
    simp only [Pi.sub_apply, Homogenization.basisVec, hx]
  have hval_edist :
      Filter.Tendsto (fun n => edist (testL2 (φ n)) u.val.1)
        Filter.atTop (nhds 0) := by
    rw [← edist_self u.val.1]
    exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp hval_tendsto
  have htendsto_val :
      Filter.Tendsto
        (fun n => eLpNorm
          (fun x => (φ n : SpatialCoordinates d → ℝ) x - v.toFun x) 2
          (volume.restrict (Ω : Set (SpatialCoordinates d))))
        Filter.atTop (nhds 0) := by
    refine hval_edist.congr ?_
    intro n
    exact (hval_norm (φ n)).symm
  have hgrad_edist :
      ∀ i : Fin d, Filter.Tendsto
        (fun n => edist (testPartialL2 (φ n) i) (u.val.2 i))
        Filter.atTop (nhds 0) := by
    intro i
    rw [← edist_self (u.val.2 i)]
    exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp
      (hgrad_tendsto i)
  have htendsto_grad :
      ∀ i : Fin d, Filter.Tendsto
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (φ n : SpatialCoordinates d → ℝ) x)
              (Homogenization.basisVec i) - v.grad x i) 2
          (volume.restrict (Ω : Set (SpatialCoordinates d))))
        Filter.atTop (nhds 0) := by
    intro i
    refine (hgrad_edist i).congr ?_
    intro n
    exact (hgrad_norm (φ n) i).symm
  let w : Homogenization.H10Function (Ω : Set (SpatialCoordinates d)) :=
    { toH1Function := v
      approx := fun n => φ n
      approx_smooth := fun n => (φ n).contDiff
      approx_hasCompactSupport := fun n => (φ n).hasCompactSupport
      approx_support_subset := fun n => (φ n).tsupport_subset
      tendsto_approx := htendsto_val
      tendsto_approx_grad := htendsto_grad }
  exact ⟨w, hv_val, hv_grad⟩

end SubdiffusiveProcess
