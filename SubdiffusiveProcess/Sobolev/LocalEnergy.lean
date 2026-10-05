module

public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Variational.RelativeL2
public import SubdiffusiveProcess.Variational.RelativeAlgebra
public import SubdiffusiveProcess.Variational.WeightedCoefficient

@[expose] public section

/-! # Actual local energies of coordinate gradients

Localization acts on L2 gradients, not on Sobolev functions: multiplying a
function by an indicator would introduce a distributional boundary term.
The local energy below is exactly the coefficient-weighted set integral.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Positive bounded coefficients are nonnegative almost everywhere. -/
theorem positiveCoefficient_ae_nonneg (a : PositiveCoefficient Ω) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ a.val x := by
  obtain ⟨c, hc, ha⟩ := a.property
  exact ha.mono fun x hx => hc.le.trans hx

/-- The old coefficient's energy in a measurable set, for an actual L2 gradient. -/
def localGradientEnergy (a : PositiveCoefficient Ω) {s : Set (SpatialCoordinates d)}
    (hs : MeasurableSet s) (g : HilbertGradient Ω) : ℝ :=
  ∑ i : Fin d, weightedL2Form a.val (localizeL2 hs (g i)) (localizeL2 hs (g i))

/-- Exact identification with the unnormalized local gradient integral. -/
theorem localGradientEnergy_eq_integral (a : PositiveCoefficient Ω) {s : Set (SpatialCoordinates d)}
    (hs : MeasurableSet s) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g = ∑ i : Fin d,
      ∫ x in s, a.val x * (g i x) ^ 2 ∂volume.restrict (Ω : Set (SpatialCoordinates d)) := by
  simp only [localGradientEnergy, weightedL2Form_localize_self, Real.norm_eq_abs, sq_abs]

/-- Local energy is nonnegative. -/
theorem localGradientEnergy_nonneg (a : PositiveCoefficient Ω) {s : Set (SpatialCoordinates d)}
    (hs : MeasurableSet s) (g : HilbertGradient Ω) : 0 ≤ localGradientEnergy a hs g :=
  Finset.sum_nonneg fun i _ => weightedL2Form_nonneg a.val (positiveCoefficient_ae_nonneg a) (localizeL2 hs (g i))

/-- Local energy is at most the full coefficient energy. -/
theorem localGradientEnergy_le (a : PositiveCoefficient Ω) {s : Set (SpatialCoordinates d)}
    (hs : MeasurableSet s) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g ≤ weightedGradientForm a.val g g := by
  simp only [localGradientEnergy, weightedGradientForm, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply]
  exact Finset.sum_le_sum fun i _ => weightedL2Form_localize_le a.val hs
    (positiveCoefficient_ae_nonneg a) _

/-- Relative coefficient order gives the same full-gradient energy order. -/
theorem weightedGradientForm_le_mul (a b : PositiveCoefficient Ω) (c : ℝ)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ c * b.val x)
    (g : HilbertGradient Ω) : weightedGradientForm a.val g g ≤ c * weightedGradientForm b.val g g := by
  simp only [weightedGradientForm, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => weightedL2Form_le_smul c a.val b.val hab _

/-- Relative coefficient order also holds for the actual local energy. -/
theorem localGradientEnergy_le_mul (a b : PositiveCoefficient Ω) (c : ℝ)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ c * b.val x)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g ≤ c * localGradientEnergy b hs g := by
  simp only [localGradientEnergy, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => weightedL2Form_le_smul c a.val b.val hab _

/-- The local quadratic triangle inequality for two actual gradients. -/
theorem localGradientEnergy_sub_le (a : PositiveCoefficient Ω) {s : Set (SpatialCoordinates d)}
    (hs : MeasurableSet s) (g h : HilbertGradient Ω) :
    localGradientEnergy a hs g ≤ 2 * localGradientEnergy a hs h +
      2 * localGradientEnergy a hs (g - h) := by
  simp only [localGradientEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    weightedL2Form_localize_sub_le a.val hs (positiveCoefficient_ae_nonneg a) (g i) (h i)

/-- Summed relative Young inequality, localized in the original gradient only. -/
theorem weightedGradientForm_difference_young_local (a b : PositiveCoefficient Ω)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) {δ c : ℝ} (hc : 0 < c)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |b.val x - a.val x| ≤ δ * a.val x)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → b.val x = a.val x)
    (g h : HilbertGradient Ω) :
    |weightedGradientForm b.val g h - weightedGradientForm a.val g h| ≤
      δ ^ 2 / (2 * c) * localGradientEnergy a hs g + c / 2 * weightedGradientForm a.val h h := by
  simp only [weightedGradientForm, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply, localGradientEnergy,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun i _ => weightedL2Form_difference_young_local a.val b.val hs hc
    (positiveCoefficient_ae_nonneg a) hab hsupp _ _

/-- The diagonal perturbation uses the actual old local gradient energy. -/
theorem weightedGradientForm_difference_self_le_local (a b : PositiveCoefficient Ω)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) {δ : ℝ}
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |b.val x - a.val x| ≤ δ * a.val x)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → b.val x = a.val x)
    (g : HilbertGradient Ω) :
    |weightedGradientForm b.val g g - weightedGradientForm a.val g g| ≤
      δ * localGradientEnergy a hs g := by
  simp only [weightedGradientForm, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply, localGradientEnergy,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun i _ => weightedL2Form_difference_self_le_local a.val b.val hs hab hsupp _

end SubdiffusiveProcess
