module

public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

/-!
# The affine map between the unit cube and a cube of side `r`

The change-of-variables toolkit that `coercivity_dilation` rests on: the map, the
fact that it carries the unit cube about `z'` onto the cube of side `r` about `z`, the
exact pushforward of Lebesgue measure, and the resulting change of variables for lower
Lebesgue integrals over a cube.

The last of these is stated for an **arbitrary** `ℝ≥0∞`-valued integrand, with no
measurability side condition, because the map is packaged as a `MeasurableEquiv` and
`lintegral_map_equiv` applies.  That matters: the Gagliardo integrand is built from
representatives of `L²` classes, and requiring the integrand to be measurable would push a
hypothesis into every consumer.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.EllipticRegularity

variable {d : ℕ}

/-- The affine map carrying the unit cube about `z'` onto the cube of side `r` about `z`.
This is the `T` of the paper's translation-and-dilation sentence and the map
appearing in `in_J`'s `lam_dilation`. -/
def cubeDilation (z z' : SpatialCoordinates d) (r : ℝ) :
    SpatialCoordinates d → SpatialCoordinates d :=
  fun x i => z i + r * (x i - z' i)

@[simp] theorem cubeDilation_apply (z z' : SpatialCoordinates d) (r : ℝ)
    (x : SpatialCoordinates d) (i : Fin d) :
    cubeDilation z z' r x i = z i + r * (x i - z' i) := rfl

/-- `cubeDilation` is continuous, hence measurable. -/
theorem continuous_cubeDilation (z z' : SpatialCoordinates d) (r : ℝ) :
    Continuous (cubeDilation z z' r) := by
  refine continuous_pi fun i => ?_
  exact continuous_const.add (continuous_const.mul ((continuous_apply i).sub continuous_const))

/-- The map carries the unit cube about `z'` into the cube of side `r` about `z`. -/
theorem cubeDilation_mapsTo (z z' : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) :
    ∀ x ∈ (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      cubeDilation z z' r x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  intro x hx
  rw [centeredCube_eq_pi] at hx ⊢
  intro i _
  have hi := hx i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi ⊢
  constructor
  · have : -(r / 2) < r * (x i - z' i) := by nlinarith [hi.1]
    simpa [cubeDilation] using by linarith
  · have : r * (x i - z' i) < r / 2 := by nlinarith [hi.2]
    simpa [cubeDilation] using by linarith

/-- The dilation as a measurable equivalence. -/
def cubeDilationEquiv (z z' : SpatialCoordinates d) {r : ℝ} (hr : r ≠ 0) :
    SpatialCoordinates d ≃ᵐ SpatialCoordinates d where
  toFun := cubeDilation z z' r
  invFun := cubeDilation z' z r⁻¹
  left_inv := by intro x; funext i; simp [cubeDilation]; field_simp; ring
  right_inv := by intro x; funext i; simp [cubeDilation]; field_simp; ring
  measurable_toFun := (continuous_cubeDilation z z' r).measurable
  measurable_invFun := (continuous_cubeDilation z' z r⁻¹).measurable

@[simp] theorem cubeDilationEquiv_apply (z z' : SpatialCoordinates d) {r : ℝ} (hr : r ≠ 0)
    (x : SpatialCoordinates d) : cubeDilationEquiv z z' hr x = cubeDilation z z' r x := rfl

theorem map_cubeDilation_volume (z z' : SpatialCoordinates d) {r : ℝ} (hr : r ≠ 0) :
    Measure.map (cubeDilation z z' r) (volume : Measure (SpatialCoordinates d)) =
      ENNReal.ofReal |(r ^ d)⁻¹| • volume := by
  have hmsub : Measurable (fun x : SpatialCoordinates d => x - z') := measurable_id.sub_const z'
  have hmsmul : Measurable (fun x : SpatialCoordinates d => r • x) := measurable_const_smul r
  have hmadd : Measurable (fun y : SpatialCoordinates d => z + y) := measurable_const_add z
  have h1 : Measure.map (fun x : SpatialCoordinates d => x - z') volume = volume :=
    (measurePreserving_sub_right volume z').map_eq
  have h3 : Measure.map (fun y : SpatialCoordinates d => z + y) volume = volume :=
    (measurePreserving_add_left volume z).map_eq
  have hrank : Module.finrank ℝ (SpatialCoordinates d) = d := by
    simp [SpatialCoordinates, Module.finrank_fintype_fun_eq_card]
  have h2 : Measure.map (fun x : SpatialCoordinates d => r • x) volume =
      ENNReal.ofReal |(r ^ d)⁻¹| • volume := by
    have := Measure.map_addHaar_smul (volume : Measure (SpatialCoordinates d)) hr
    rwa [hrank] at this
  have hfun : cubeDilation z z' r =
      (fun y : SpatialCoordinates d => z + y) ∘
        ((fun x : SpatialCoordinates d => r • x) ∘
          (fun x : SpatialCoordinates d => x - z')) := by
    funext x i; simp [cubeDilation, Function.comp]
  rw [hfun, ← Measure.map_map hmadd (hmsmul.comp hmsub), ← Measure.map_map hmsmul hmsub,
    h1, h2, Measure.map_smul _ hmadd.aemeasurable, h3]

theorem cubeDilation_preimage_centeredCube (z z' : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0:ℝ) < 1) :
    cubeDilation z z' r ⁻¹' (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
  ext x
  simp only [Set.mem_preimage, centeredCube_eq_pi, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo, cubeDilation_apply]
  constructor
  · intro h i; have hi := h i; constructor <;> nlinarith [hi.1, hi.2]
  · intro h i; have hi := h i; constructor <;> nlinarith [hi.1, hi.2]

theorem map_cubeDilation_restrict (z z' : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (h1 : (0:ℝ) < 1) :
    Measure.map (cubeDilation z z' r)
        (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) =
      ENNReal.ofReal |(r ^ d)⁻¹| •
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hmeas : Measurable (cubeDilation z z' r) := (continuous_cubeDilation z z' r).measurable
  have hset : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  rw [← cubeDilation_preimage_centeredCube z z' hr h1, ← Measure.restrict_map hmeas hset,
    map_cubeDilation_volume z z' hr.ne', Measure.restrict_smul]

/-- Change of variables on a cube, for an arbitrary `ℝ≥0∞`-valued integrand. -/
theorem lintegral_centeredCube_cubeDilation (z z' : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0:ℝ) < 1) (g : SpatialCoordinates d → ℝ≥0∞) :
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x =
      ENNReal.ofReal (r ^ d) *
        ∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          g (cubeDilation z z' r x) := by
  have hmap := map_cubeDilation_restrict z z' hr h1
  have hcoe : ⇑(cubeDilationEquiv z z' hr.ne') = cubeDilation z z' r := rfl
  have key : ∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      g (cubeDilation z z' r x) =
      ENNReal.ofReal |(r ^ d)⁻¹| *
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x := by
    have h := lintegral_map_equiv (μ := volume.restrict
        (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) g (cubeDilationEquiv z z' hr.ne')
    rw [hcoe, hmap, lintegral_smul_measure] at h
    exact h.symm
  rw [key, ← mul_assoc]
  have : ENNReal.ofReal (r ^ d) * ENNReal.ofReal |(r ^ d)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [abs_of_pos (by positivity : (0:ℝ) < (r ^ d)⁻¹)]
    rw [mul_inv_cancel₀ (by positivity : (r:ℝ) ^ d ≠ 0)]
    simp
  rw [this, one_mul]

/-- The dilation scales Euclidean distances by `r`: this is the kernel factor of the
Gagliardo change of variables. -/
theorem sqrt_sum_sq_cubeDilation (z z' : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (cubeDilation z z' r x j - cubeDilation z z' r y j) ^ 2) =
      r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  have hstep : ∀ j : Fin d,
      (cubeDilation z z' r x j - cubeDilation z z' r y j) ^ 2 = r ^ 2 * (x j - y j) ^ 2 := by
    intro j; simp only [cubeDilation_apply]; ring
  rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]

end SubdiffusiveProcess.EllipticRegularity
