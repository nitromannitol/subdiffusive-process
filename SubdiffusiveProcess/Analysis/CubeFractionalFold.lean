module

public import SubdiffusiveProcess.Analysis.CubeFractionalSplit
public import Homogenization.Sobolev.CubeEmbedding.FoldNorm

@[expose] public section

open MeasureTheory Set Homogenization
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- The base box for the reflection extension. -/
def cubeExtensionBox (d : ℕ) : Set (SpatialCoordinates d) :=
  Box (fun _ => -(1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))

/-- Its tripled box. -/
def cubeExtensionTriple (d : ℕ) : Set (SpatialCoordinates d) :=
  Box3 (fun _ => -(1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))

/-- Coordinatewise even reflection across the faces of the unit cube. -/
def cubeExtensionFold {d : ℕ} : SpatialCoordinates d → SpatialCoordinates d :=
  Fold (fun _ => -(1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))

theorem cubeExtensionBox_eq (d : ℕ) :
    cubeExtensionBox d = (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_pi]
  simp only [cubeExtensionBox, Box, Pi.zero_apply, zero_sub, zero_add]

theorem cubeExtensionTriple_eq (d : ℕ) :
    cubeExtensionTriple d = Metric.ball (0 : SpatialCoordinates d) (3 / 2) := by
  change Box3 (fun _ => -(1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ)) = _
  rw [ball_pi _ (by norm_num : 0 < (3 : ℝ) / 2)]
  simp only [Box3, Real.ball_eq_Ioo, Pi.zero_apply, zero_sub, zero_add]
  norm_num

theorem foldR_abs_sub_le (lo hi x y : ℝ) (h : lo ≤ hi) :
    |foldR lo hi x - foldR lo hi y| ≤ |x - y| := by
  unfold foldR
  split_ifs <;> apply abs_le.mpr <;> constructor <;>
    linarith [le_abs_self (x - y), neg_le_abs (x - y)]

theorem euclideanDist_cubeExtensionFold_le {d : ℕ} (x y : SpatialCoordinates d) :
    euclideanDist (cubeExtensionFold x) (cubeExtensionFold y) ≤ euclideanDist x y := by
  unfold euclideanDist euclideanNorm vecNormSq vecDot
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have h := foldR_abs_sub_le (-(1 / 2 : ℝ)) (1 / 2) (x i) (y i) (by norm_num)
  have hsq := sq_le_sq₀ (abs_nonneg _) (abs_nonneg _) |>.mpr h
  rw [sq_abs, sq_abs] at hsq
  simpa only [cubeExtensionFold, Fold, Pi.sub_apply, pow_two] using hsq

theorem measurable_cubeExtensionFold {d : ℕ} : Measurable (cubeExtensionFold (d := d)) := by
  exact (continuous_Fold _ _ (fun _ => by norm_num)).measurable

theorem cubeExtensionFold_eq_self {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ cubeExtensionBox d) : cubeExtensionFold x = x := by
  apply Fold_of_mem
  intro i
  exact ⟨(hx i (Set.mem_univ i)).1.le, (hx i (Set.mem_univ i)).2.le⟩

theorem lintegral_cubeExtensionFold {d : ℕ} (g : SpatialCoordinates d → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ x in cubeExtensionTriple d, g (cubeExtensionFold x)) =
      (3 : ℝ≥0∞) ^ d * ∫⁻ x in cubeExtensionBox d, g x := by
  exact lintegral_foldComp hg _ _ (fun _ => by norm_num)

/-- Reflection does not increase the pointwise fractional kernel. -/
theorem cubeFractionalKernel_fold_le {d : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (f : SpatialCoordinates d → ℝ) (x y : SpatialCoordinates d) :
    cubeFractionalKernel s (fun a => f (cubeExtensionFold a)) x y ≤
      cubeFractionalKernel s f (cubeExtensionFold x) (cubeExtensionFold y) := by
  by_cases heq : cubeExtensionFold x = cubeExtensionFold y
  · simp only [cubeFractionalKernel, heq, sub_self, zero_pow (by decide : 2 ≠ 0),
      ENNReal.ofReal_zero, ENNReal.zero_div, le_refl]
  · unfold cubeFractionalKernel
    apply ENNReal.div_le_div_left
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (euclideanDist_cubeExtensionFold_le x y)) (by positivity)

/-- The fractional integral of the reflected function is controlled by the original. -/
theorem double_lintegral_cubeFractionalKernel_fold_le {d : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    (∫⁻ x in cubeExtensionTriple d, ∫⁻ y in cubeExtensionTriple d,
      cubeFractionalKernel s (fun a => f (cubeExtensionFold a)) x y) ≤
      ((3 : ℝ≥0∞) ^ d) ^ 2 *
        ∫⁻ x in cubeExtensionBox d, ∫⁻ y in cubeExtensionBox d,
          cubeFractionalKernel s f x y := by
  let K : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := cubeFractionalKernel s f
  have hK := measurable_cubeFractionalKernel s f hf
  have hinner : Measurable (fun x : SpatialCoordinates d =>
      ∫⁻ y in cubeExtensionBox d, K x y) := hK.lintegral_prod_right
  calc
    _ ≤ ∫⁻ x in cubeExtensionTriple d, ∫⁻ y in cubeExtensionTriple d,
        K (cubeExtensionFold x) (cubeExtensionFold y) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      exact cubeFractionalKernel_fold_le s hs f x y
    _ = ∫⁻ x in cubeExtensionTriple d,
        (3 : ℝ≥0∞) ^ d * ∫⁻ y in cubeExtensionBox d, K (cubeExtensionFold x) y := by
      apply lintegral_congr
      intro x
      have hslice : Measurable (fun y : SpatialCoordinates d => K (cubeExtensionFold x) y) :=
        by
          dsimp only [K]
          unfold cubeFractionalKernel euclideanDist euclideanNorm vecNormSq vecDot
          fun_prop
      exact lintegral_cubeExtensionFold (d := d) _ hslice
    _ = (3 : ℝ≥0∞) ^ d * ((3 : ℝ≥0∞) ^ d *
        ∫⁻ x in cubeExtensionBox d, ∫⁻ y in cubeExtensionBox d, K x y) := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_cubeExtensionFold _ hinner]
    _ = _ := by rw [pow_two, mul_assoc]

end SubdiffusiveProcess
