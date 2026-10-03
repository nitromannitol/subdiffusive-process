module

public import SubdiffusiveProcess.Paper.lfgc_err_compare
public import SubdiffusiveProcess.Paper.in_deterministic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Charts of cutoff coefficients with two infrared fields are close

For infrared fields `H, H'` the cutoff coefficients satisfy exactly
`A^{H'}(x) = e^{H'(x) - H(x)} A^{H}(x)`.  If the oscillation of `H' - H` on the root cube
`w + r Q₀` is at most `ε`, the two root charts are `aux_lfgc_chart_compare_ChartsClose` with the scalar
`κ = e^{(H'-H)(w)}`.  Deterministic.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal Pointwise

namespace Paper
variable {d : ℕ}

theorem aux_lfgc_cutoff_charts_cutoffCoefficient_ratio (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) :
    cutoffCoefficient M H' omega N x =
      Real.exp (H' omega x - H omega x) * cutoffCoefficient M H omega N x := by
  unfold cutoffCoefficient cutoffPotential
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem aux_lfgc_cutoff_charts_mem_centeredCube_affine (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {x : SpatialCoordinates d} (hx : x ∈ openCubeSet (originCube d 0)) :
    r • x + w ∈ (centeredCube w r hr : Set (SpatialCoordinates d)) := by
  have h0 : x ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    have := Lane4.centeredCube_zero_eq_openCubeSet_originCube (d := d) 0 (by norm_num)
    simp only [zpow_zero] at this
    rw [this]; exact hx
  rw [centeredCube_eq_pi] at h0 ⊢
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.zero_apply] at h0 ⊢
  intro i
  obtain ⟨h1, h2⟩ := h0 i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> nlinarith

/-- A.e. chart identity: the root chart of the cutoff coefficient is the rescaled scalar field. -/
theorem aux_lfgc_cutoff_charts_chart_coeff_ae (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d 0)) :
    ∀ᵐ x ∂ volume.restrict (openCubeSet Q),
      ((I.chart w r hr (Lane4.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn Q).toCoeffField x =
        scalarMatrix (cutoffCoefficient M H omega N (r • x + w)) := by
  have h1 := I.chart_eq w r hr (Lane4.cutoffPositiveCoefficient M H omega N w hr) w r hr subset_rfl Q hQ
  have h2 := Paper.aux_in_deterministic_core_cutoff_coeFn M H omega N w hr
  -- pull `h2` back along `x ↦ r • x + w`
  have hsub : translateSet w (r • openCubeSet (originCube d 0)) ⊆
      (centeredCube w r hr : Set (SpatialCoordinates d)) := by
    intro y hy
    rw [mem_translateSet_iff_sub_mem] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hxy' : r • x = y - w := hxy
    have : y = r • x + w := by rw [hxy']; abel
    rw [this]
    exact aux_lfgc_cutoff_charts_mem_centeredCube_affine w hr hx
  have h3 : ∀ᵐ x ∂ volume.restrict (openCubeSet (originCube d 0)),
      (Lane4.cutoffPositiveCoefficient M H omega N w hr).val (r • x + w) =
        cutoffCoefficient M H omega N (r • x + w) :=
    Paper.aux_in_deterministic_core_ae_affine hr w (openCubeSet (originCube d 0))
      (ae_restrict_of_ae_restrict_of_subset hsub h2)
  have h3Q := ae_restrict_of_ae_restrict_of_subset hQ h3
  filter_upwards [h1, h3Q] with x hx1 hx3
  rw [hx1]
  have e : (fun i => w i + r * x i) = r • x + w := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e, hx3]

theorem aux_lfgc_cutoff_charts_scalarMatrix_loewner {a b : ℝ} (hab : a ≤ b) : MatLoewnerLE (scalarMatrix (d := d) a) (scalarMatrix b) := by
  intro v
  rw [matVecMul_scalarMatrix, matVecMul_scalarMatrix]
  have hv : 0 ≤ vecDot v v := vecNormSq_nonneg' v
  have e1 : vecDot v (a • v) = a * vecDot v v := by
    unfold vecDot; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : vecDot v (b • v) = b * vecDot v v := by
    unfold vecDot; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  nlinarith

theorem aux_lfgc_cutoff_charts_smul_scalarMatrix (c t : ℝ) : c • scalarMatrix (d := d) t = scalarMatrix (c * t) := by
  simp only [scalarMatrix, smul_smul]

/-- Root charts of the cutoff coefficients for two infrared fields are close. -/
theorem lfgc_cutoff_charts (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (ε : ℝ)
    (hosc : ∀ y ∈ (centeredCube w r hr : Set (SpatialCoordinates d)),
      |(H' omega y - H omega y) - (H' omega w - H omega w)| ≤ ε) :
    aux_lfgc_chart_compare_ChartsClose (I.chart w r hr (Lane4.cutoffPositiveCoefficient M H omega N w hr) w r)
      (I.chart w r hr (Lane4.cutoffPositiveCoefficient M H' omega N w hr) w r)
      (Real.exp (H' omega w - H omega w)) ε := by
  intro Q hQ
  have hF := aux_lfgc_cutoff_charts_chart_coeff_ae I M H omega N w hr Q hQ
  have hF' := aux_lfgc_cutoff_charts_chart_coeff_ae I M H' omega N w hr Q hQ
  have hmem : ∀ᵐ x ∂ volume.restrict (openCubeSet Q), x ∈ openCubeSet Q :=
    ae_restrict_mem (isOpen_openCubeSet Q).measurableSet
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold CoeffOn.IsSymmetric
    filter_upwards [hF] with x hx
    rw [hx]; exact Matrix.isSymm_one.smul _
  · unfold CoeffOn.IsSymmetric
    filter_upwards [hF'] with x hx
    rw [hx]; exact Matrix.isSymm_one.smul _
  · filter_upwards [hF, hF', hmem] with x hx hx' hxm
    rw [hx, hx', aux_lfgc_cutoff_charts_smul_scalarMatrix, aux_lfgc_cutoff_charts_smul_scalarMatrix, aux_lfgc_cutoff_charts_cutoffCoefficient_ratio M H H']
    apply aux_lfgc_cutoff_charts_scalarMatrix_loewner
    have hy := hosc _ (aux_lfgc_cutoff_charts_mem_centeredCube_affine w hr (hQ hxm))
    have hpos := Lane4.cutoffCoefficient_pos M H omega N (r • x + w)
    have h1 : H' omega (r • x + w) - H omega (r • x + w) ≤ ε + (H' omega w - H omega w) := by
      linarith [(abs_le.mp hy).2]
    have h2 : Real.exp (H' omega (r • x + w) - H omega (r • x + w)) ≤
        Real.exp ε * Real.exp (H' omega w - H omega w) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (H' omega (r • x + w) - H omega (r • x + w)) *
          cutoffCoefficient M H omega N (r • x + w)
        ≤ Real.exp ε * Real.exp (H' omega w - H omega w) *
          cutoffCoefficient M H omega N (r • x + w) :=
          mul_le_mul_of_nonneg_right h2 hpos.le
      _ = _ := by ring
  · filter_upwards [hF, hF', hmem] with x hx hx' hxm
    rw [hx, hx', aux_lfgc_cutoff_charts_smul_scalarMatrix, aux_lfgc_cutoff_charts_smul_scalarMatrix, aux_lfgc_cutoff_charts_cutoffCoefficient_ratio M H H']
    apply aux_lfgc_cutoff_charts_scalarMatrix_loewner
    have hy := hosc _ (aux_lfgc_cutoff_charts_mem_centeredCube_affine w hr (hQ hxm))
    have hpos := Lane4.cutoffCoefficient_pos M H omega N (r • x + w)
    have h2 : Real.exp (-ε) * Real.exp (H' omega w - H omega w) ≤
        Real.exp (H' omega (r • x + w) - H omega (r • x + w)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hy).1])
    calc Real.exp (-ε) * (Real.exp (H' omega w - H omega w) *
          cutoffCoefficient M H omega N (r • x + w))
        = Real.exp (-ε) * Real.exp (H' omega w - H omega w) *
          cutoffCoefficient M H omega N (r • x + w) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hpos.le

end Paper
