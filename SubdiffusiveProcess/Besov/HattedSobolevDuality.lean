module

public import SubdiffusiveProcess.Besov.HattedDuality
public import Homogenization.Sobolev.Foundations.PoincareMeanZero
public import Homogenization.Sobolev.Foundations.CubePoisson.Solver

@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal ContDiff Topology
noncomputable section
variable {d : ℕ} [NeZero d]

theorem cubeLpNorm_H1_value_eq (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    cubeLpNorm Q 2 u.toFun = ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * ‖u.toScalarL2‖ := by
  simpa only [H1Function.toScalarL2] using!
    cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet
      Q u.memL2_normalizedCubeMeasure

theorem cubeLpNorm_H1_grad_eq (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) (i : Fin d) :
    cubeLpNorm Q 2 (fun x => u.grad x i) =
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * ‖u.gradCoordToScalarL2 i‖ := by
  simpa only [H1Function.gradCoordToScalarL2] using!
    cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet
      Q (u.grad_memL2_normalizedCubeMeasure i)

theorem normalized_pairing_eq_scalarInner (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (u : H1Function (openCubeSet Q)) :
    ∫ x, f x * u.toFun x ∂normalizedCubeMeasure Q =
      (cubeVolume Q)⁻¹ * inner ℝ
        (Homogenization.toScalarL2 (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf))
        u.toScalarL2 := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg Q))]
  simp only [smul_eq_mul]
  congr 1
  rw [scalarInner_eq_integral]
  apply integral_congr_ae
  filter_upwards [Homogenization.coeFn_toScalarL2
    (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf), H1Function.coeFn_toScalarL2 u]
    with x hx hu
  rw [hx, hu]

/-- Smooth tests are dense in the complete inhomogeneous Sobolev test space. -/
theorem abs_coordinate_pairing_H1_le (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (i : Fin d) (u : H1Function (openCubeSet Q)) :
    |∫ x, F x i * u.toFun x ∂normalizedCubeMeasure Q| ≤
      (hHatNorm Q F).toReal * ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        (u.gradientCoordL2NormSum + (cubeScaleFactor Q)⁻¹ * ‖u.toScalarL2‖) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  obtain ⟨x0, hx0⟩ := Ch02.openCubeSet_nonempty Q
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hU.isOpen.mem_nhds hx0)
  let r : ℝ := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : Metric.closedBall x0 r ⊆ openCubeSet Q := by
    intro y hy
    apply hδsub
    have hy' : dist y x0 ≤ r := by simpa [Metric.mem_closedBall] using hy
    exact lt_of_le_of_lt hy' (by dsimp [r]; linarith)
  let ψ : ℕ → H1Function (openCubeSet Q) := H1Function.convexApproxSmoothH1 hU u x0 hr
  have hsmooth : ∀ n, ContDiff ℝ ∞ (ψ n).toFun := by
    intro n
    change ContDiff ℝ ∞ (H1Function.convexApproxSmoothH1 hU u x0 hr n).toFun
    rw [show (H1Function.convexApproxSmoothH1 hU u x0 hr n).toFun =
      (H1Function.convexApproxSmoothH1 hU u x0 hr n : Vec d → ℝ) from rfl,
      H1Function.convexApproxSmoothH1_toFun]
    exact contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)) (by norm_num) u.memL2 hr
      (by unfold unitConvexApproxScale; positivity)
  have hgrad : ∀ n j x, (ψ n).grad x j = fderiv ℝ (ψ n).toFun x (Pi.single j 1) := by
    intro n j x
    dsimp only [ψ]
    rw [H1Function.convexApproxSmoothH1_grad]
    rw [show (H1Function.convexApproxSmoothH1 hU u x0 hr n).toFun =
      (H1Function.convexApproxSmoothH1 hU u x0 hr n : Vec d → ℝ) from rfl,
      H1Function.convexApproxSmoothH1_toFun]
    rfl
  have hbound : ∀ n,
      |∫ x, F x i * (ψ n).toFun x ∂normalizedCubeMeasure Q| ≤
        (hHatNorm Q F).toReal * ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
          ((ψ n).gradientCoordL2NormSum + (cubeScaleFactor Q)⁻¹ * ‖(ψ n).toScalarL2‖) := by
    intro n
    have h := abs_coordinate_pairing_smooth_le Q F hF i (ψ n).toFun (hsmooth n)
    have hd : ∀ j, (fun x => fderiv ℝ (ψ n).toFun x (Pi.single j 1)) =
        fun x => (ψ n).grad x j := by
      intro j
      funext x
      exact (hgrad n j x).symm
    simp_rw [hd, cubeLpNorm_H1_grad_eq, cubeLpNorm_H1_value_eq] at h
    rw [← Finset.mul_sum] at h
    unfold H1Function.gradientCoordL2NormSum
    convert h using 1 <;> ring
  have hval := H1Function.tendsto_convexApproxSmoothH1_toScalarL2 hU u hball hr
  have hder := H1Function.tendsto_convexApproxSmoothH1_gradCoordToScalarL2 hU u hball hr
  have hpair : Filter.Tendsto
      (fun n => |∫ x, F x i * (ψ n).toFun x ∂normalizedCubeMeasure Q|) Filter.atTop
      (nhds |∫ x, F x i * u.toFun x ∂normalizedCubeMeasure Q|) := by
    simp_rw [normalized_pairing_eq_scalarInner Q _ (hF i)]
    exact ((tendsto_const_nhds.inner hval).const_mul _).abs
  have hright : Filter.Tendsto
      (fun n => (hHatNorm Q F).toReal * ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        ((ψ n).gradientCoordL2NormSum + (cubeScaleFactor Q)⁻¹ * ‖(ψ n).toScalarL2‖))
      Filter.atTop (nhds ((hHatNorm Q F).toReal * ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        (u.gradientCoordL2NormSum + (cubeScaleFactor Q)⁻¹ * ‖u.toScalarL2‖))) := by
    apply Filter.Tendsto.const_mul
    apply Filter.Tendsto.add
    · unfold H1Function.gradientCoordL2NormSum
      exact tendsto_finset_sum _ (fun j _ => (hder j).norm)
    · exact hval.norm.const_mul _
  exact le_of_tendsto_of_tendsto' hpair hright hbound

end
end SubdiffusiveProcess.Besov
