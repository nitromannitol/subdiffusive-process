module

public import SubdiffusiveProcess.Sobolev.LocalEnergy

@[expose] public section

/-! # Relative perturbations of actual gradient energies

These deterministic estimates have the original nonconstant coefficient on
the right-hand side. The weak equations used here are discharged for the
canonical Sobolev source and boundary responses in the consumer module.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- A relative positive lower coefficient bound gives the lower energy bound. -/
theorem weightedGradientForm_mul_le (a b : PositiveCoefficient Ω) {c : ℝ} (hc : 0 < c)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c * a.val x ≤ b.val x)
    (g : HilbertGradient Ω) : c * weightedGradientForm a.val g g ≤ weightedGradientForm b.val g g := by
  have h : weightedGradientForm a.val g g ≤ c⁻¹ * weightedGradientForm b.val g g :=
    weightedGradientForm_le_mul a b c⁻¹ (by
      filter_upwards [hab] with x hx
      apply (mul_le_mul_iff_right₀ hc).mp
      calc
        c * a.val x ≤ b.val x := hx
        _ = c * (c⁻¹ * b.val x) := by field_simp) g
  have h' := mul_le_mul_of_nonneg_left h hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using h'

/-- Young's inequality absorbs half the difference energy, including its zero case. -/
theorem relative_gradient_difference_energy_le (a b : PositiveCoefficient Ω)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) {δ c : ℝ} (hc : 0 < c)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c * a.val x ≤ b.val x)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |b.val x - a.val x| ≤ δ * a.val x)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → b.val x = a.val x)
    (g h : HilbertGradient Ω)
    (heq : weightedGradientForm b.val h (h - g) = weightedGradientForm a.val g (h - g)) :
    weightedGradientForm b.val (h - g) (h - g) ≤ δ ^ 2 / c * localGradientEnergy a hs g := by
  have hd := bilinear_solution_difference (weightedGradientForm a.val) (weightedGradientForm b.val) g h heq
  have hu : weightedGradientForm b.val (h - g) (h - g) ≤
      δ ^ 2 / (2 * c) * localGradientEnergy a hs g + c / 2 * weightedGradientForm a.val (h - g) (h - g) := by
    rw [hd]
    exact (neg_le_abs _).trans (weightedGradientForm_difference_young_local a b hs hc hab hsupp g (h - g))
  have hl' := weightedGradientForm_mul_le a b hc hl (h - g)
  have hk : δ ^ 2 / (2 * c) = (δ ^ 2 / c) / 2 := by field_simp
  rw [hk] at hu
  nlinarith

/-- The changed solution's local energy is controlled by the original local mass. -/
theorem relative_gradient_local_energy_le (a b : PositiveCoefficient Ω)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) {δ c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c * a.val x ≤ b.val x)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |b.val x - a.val x| ≤ δ * a.val x)
    (hm : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), b.val x ≤ M * a.val x)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → b.val x = a.val x)
    (g h : HilbertGradient Ω)
    (heq : weightedGradientForm b.val h (h - g) = weightedGradientForm a.val g (h - g)) :
    localGradientEnergy b hs h ≤ 2 * M * (1 + δ ^ 2 / c ^ 2) * localGradientEnergy a hs g := by
  have he := relative_gradient_difference_energy_le a b hs hc hl hab hsupp g h heq
  have hv : weightedGradientForm a.val (h - g) (h - g) ≤ δ ^ 2 / c ^ 2 * localGradientEnergy a hs g := by
    have hb : weightedGradientForm a.val (h - g) (h - g) ≤
        (δ ^ 2 / c * localGradientEnergy a hs g) / c :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using (weightedGradientForm_mul_le a b hc hl _).trans he)
    convert hb using 1
    field_simp
  have hlocal : localGradientEnergy a hs h ≤
      2 * localGradientEnergy a hs g + 2 * (δ ^ 2 / c ^ 2 * localGradientEnergy a hs g) := by
    have h1 := localGradientEnergy_sub_le a hs h g
    have h2 := (localGradientEnergy_le a hs (h - g)).trans hv
    linarith
  calc
    _ ≤ M * localGradientEnergy a hs h := localGradientEnergy_le_mul b a M hm hs h
    _ ≤ M * (2 * localGradientEnergy a hs g + 2 * (δ ^ 2 / c ^ 2 * localGradientEnergy a hs g)) :=
      mul_le_mul_of_nonneg_left hlocal hM
    _ = _ := by ring

/-- Both variational sign conventions have the same local response bound. -/
theorem relative_gradient_response_difference_le (a b : PositiveCoefficient Ω)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) {δ c : ℝ} (hc : 0 < c)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c * a.val x ≤ b.val x)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |b.val x - a.val x| ≤ δ * a.val x)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → b.val x = a.val x)
    (g h : HilbertGradient Ω)
    (heq : weightedGradientForm b.val h (h - g) = weightedGradientForm a.val g (h - g))
    (hr : weightedGradientForm b.val h (h - g) = 0 ∨
      weightedGradientForm b.val h g = weightedGradientForm a.val g g) :
    |weightedGradientForm b.val h h - weightedGradientForm a.val g g| ≤
      (δ + δ ^ 2 / c) * localGradientEnergy a hs g := by
  have he := relative_gradient_difference_energy_le a b hs hc hl hab hsupp g h heq
  have hz : 0 ≤ weightedGradientForm b.val (h - g) (h - g) := by
    obtain ⟨c₀, hc₀, hb₀⟩ := b.property
    obtain ⟨c', hc', hb⟩ := weightedGradientForm_coercive b.val hc₀ hb₀
    exact (mul_nonneg (mul_nonneg hc'.le (norm_nonneg _)) (norm_nonneg _)).trans (hb _)
  have hp := weightedGradientForm_difference_self_le_local a b hs hab hsupp g
  have hd : |(weightedGradientForm b.val g g - weightedGradientForm a.val g g) -
      weightedGradientForm b.val (h - g) (h - g)| ≤
        (δ + δ ^ 2 / c) * localGradientEnergy a hs g := by
    calc
      _ ≤ |weightedGradientForm b.val g g - weightedGradientForm a.val g g| +
          |weightedGradientForm b.val (h - g) (h - g)| := abs_sub _ _
      _ ≤ δ * localGradientEnergy a hs g + δ ^ 2 / c * localGradientEnergy a hs g := by
        rw [abs_of_nonneg hz]
        exact add_le_add hp he
      _ = _ := by ring
  rcases hr with hr | hr
  · rw [bilinear_boundary_response_difference _ _ (weightedGradientForm_symm b.val) g h hr]
    exact hd
  · rw [bilinear_source_response_difference _ _ (weightedGradientForm_symm b.val) g h hr, abs_sub_comm]
    exact hd

end SubdiffusiveProcess
