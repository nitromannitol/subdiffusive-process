import SubdiffusiveProcess.Sobolev.NativeH10




open MeasureTheory Set TopologicalSpace Filter
open scoped Topology Distributions

namespace SubdiffusiveProcess

/-- The reverse of `exists_nativeH10Function_of_killedSobolevGraph`: every
`Homogenization.H10Function` on the domain of an open set is represented (in
function and gradient values, a.e.) by some element of the native
`killedSobolevGraph`. -/
theorem exists_killedSobolevGraph_of_h10Function
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (v : Homogenization.H10Function (Ω : Set (SpatialCoordinates d))) :
    ∃ u : SobolevData Ω, u ∈ killedSobolevGraph Ω ∧
      (u.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (Ω : Set (SpatialCoordinates d))] v.toH1Function.toFun ∧
      ∀ i, (u.2 i : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (Ω : Set (SpatialCoordinates d))]
        (fun x => v.toH1Function.grad x i) := by
  classical
  let φ : ℕ → 𝓓(Ω, ℝ) := fun n =>
    ⟨v.approx n, v.approx_smooth n, v.approx_hasCompactSupport n, v.approx_support_subset n⟩
  let u1 : DomainL2 Ω := v.toH1Function.memL2.toLp v.toH1Function.toFun
  let u2 : Fin d → DomainL2 Ω := fun i =>
    (v.toH1Function.gradMemL2 i).toLp (fun x => v.toH1Function.grad x i)
  have hval_norm : ∀ n, eLpNorm (fun x => (φ n : SpatialCoordinates d → ℝ) x - v.toH1Function.toFun x) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d))) = edist (testL2 (φ n)) u1 := by
    intro n
    rw [MeasureTheory.Lp.edist_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [testL2_coeFn (φ n), (v.toH1Function.memL2).coeFn_toLp] with x hx hx1
    show (φ n : SpatialCoordinates d → ℝ) x - v.toH1Function.toFun x = testL2 (φ n) x - u1 x
    rw [hx, hx1]
  have hgrad_norm : ∀ (i : Fin d) (n : ℕ),
      eLpNorm (fun x => (fderiv ℝ (φ n : SpatialCoordinates d → ℝ) x)
          (Homogenization.basisVec i) - v.toH1Function.grad x i) 2
        (volume.restrict (Ω : Set (SpatialCoordinates d))) =
      edist (testPartialL2 (φ n) i) (u2 i) := by
    intro i n
    rw [MeasureTheory.Lp.edist_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [testPartialL2_coeFn (φ n) i, (v.toH1Function.gradMemL2 i).coeFn_toLp]
      with x hx hx2
    show (fderiv ℝ (φ n : SpatialCoordinates d → ℝ) x) (Homogenization.basisVec i) -
        v.toH1Function.grad x i = testPartialL2 (φ n) i x - u2 i x
    rw [show Homogenization.basisVec i = Pi.single i (1 : ℝ) from rfl, hx, hx2]
  have hval_tendsto : Tendsto (fun n => testL2 (φ n)) atTop (𝓝 u1) := by
    rw [tendsto_iff_edist_tendsto_0]
    have := v.tendsto_approx
    simpa only [← hval_norm] using this
  have hgrad_tendsto : ∀ i : Fin d,
      Tendsto (fun n => testPartialL2 (φ n) i) atTop (𝓝 (u2 i)) := by
    intro i
    rw [tendsto_iff_edist_tendsto_0]
    have := v.tendsto_approx_grad i
    simpa only [← hgrad_norm i] using this
  have htendsto : Tendsto (fun n => smoothSobolevData (φ n)) atTop (𝓝 (u1, u2)) :=
    hval_tendsto.prodMk_nhds (tendsto_pi_nhds.mpr hgrad_tendsto)
  have hmem_range : ∀ n, smoothSobolevData (φ n) ∈
      (LinearMap.range (smoothSobolevDataLinear (Ω := Ω)) : Set (SobolevData Ω)) :=
    fun n => ⟨φ n, rfl⟩
  have hmem_closure : (u1, u2) ∈
      closure ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) : Set (SobolevData Ω)) :=
    mem_closure_iff_seq_limit.mpr ⟨fun n => smoothSobolevData (φ n), hmem_range, htendsto⟩
  have hmem : (u1, u2) ∈ killedSobolevGraph Ω := by
    simpa [killedSobolevGraph, Submodule.topologicalClosure_coe] using hmem_closure
  exact ⟨(u1, u2), hmem, (v.toH1Function.memL2).coeFn_toLp,
    fun i => (v.toH1Function.gradMemL2 i).coeFn_toLp⟩

end SubdiffusiveProcess
