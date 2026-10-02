import SubdiffusiveProcess.Analysis.CubeFractionalFold
import SubdiffusiveProcess.Analysis.FractionalCutoffEstimate

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Reflection and a Lipschitz cutoff extend finite fractional data on the unit cube. -/
theorem exists_unit_cube_fractional_extension (d : ℕ) (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => v) < ⊤ →
      ∃ V : SpatialCoordinates d → ℝ,
        ((v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))] V) ∧
        globalFractionalSqNorm s V ≤
          ENNReal.ofReal (C * cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s v) := by
  let A : ℝ≥0∞ := (3 : ℝ≥0∞) ^ d
  let M : ℝ≥0∞ := fractionalCutoffKernelMass d s
  let K : ℝ≥0∞ := 2 * A ^ 2 / ENNReal.ofReal (s : ℝ) + (1 + 4 * M) * A
  have hM : M ≠ ⊤ := fractionalCutoffKernelMass_ne_top (by omega : 0 < d)
    s s.property.1 s.property.2
  have hA : A ≠ ⊤ := by dsimp [A]; simp
  have hs0 : ENNReal.ofReal (s : ℝ) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr s.property.1
  have hK : K ≠ ⊤ := by
    dsimp [K]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top hA)) hs0
    · exact ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr
        ⟨by norm_num, ENNReal.mul_ne_top (by norm_num) hM⟩) hA
  let C : ℝ := K.toReal + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ ENNReal.ofReal C := by
    calc
      K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro v hv
  let f : SpatialCoordinates d → ℝ := fun x => v (cubeExtensionFold x)
  let V : SpatialCoordinates d → ℝ := fractionalCutoffExtension (cubeExtensionTriple d) f
  have hvm : Measurable (v : SpatialCoordinates d → ℝ) := (Lp.stronglyMeasurable v).measurable
  have hfm : Measurable f := hvm.comp measurable_cubeExtensionFold
  have hUm : MeasurableSet (cubeExtensionTriple d) := measurableSet_Box3 _ _
  have hU : ∀ x : SpatialCoordinates d, x ∉ cubeExtensionTriple d → cubeExtensionCutoff x = 0 := by
    intro x hx
    rw [cubeExtensionTriple_eq, Metric.mem_ball, dist_zero_right] at hx
    apply cubeExtensionCutoff_eq_zero
    have hn := le_of_not_gt hx
    linarith
  refine ⟨V, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet] with x hx
    have hnorm : ‖x‖ < (1 / 2 : ℝ) := by
      change dist x 0 < (1 / 2 : ℝ) at hx
      simpa only [dist_zero_right] using hx
    have hxB : x ∈ cubeExtensionBox d := by rwa [cubeExtensionBox_eq]
    have hxU : x ∈ cubeExtensionTriple d := by
      rw [cubeExtensionTriple_eq, Metric.mem_ball, dist_zero_right]
      linarith
    simp only [V, fractionalCutoffExtension, Set.indicator_of_mem hxU,
      cubeExtensionCutoff_eq_one hnorm.le, one_mul, f, cubeExtensionFold_eq_self hxB]
  · let N : ℝ≥0∞ := ENNReal.ofReal (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s v)
    have hL2 : (∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        ENNReal.ofReal (v x ^ 2)) = ENNReal.ofReal (‖v‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
        ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      exact (eLpNorm_two_sq_eq_lintegral_sq _ _).symm
    have hL2N : ENNReal.ofReal (‖v‖ ^ 2) ≤ N := by
      apply ENNReal.ofReal_le_ofReal
      simp only [cubeFractionalSqNorm, cubeFractionalVecSqNorm, Fin.sum_univ_one,
        centeredCube_volume_real, one_pow, div_one]
      exact le_add_of_nonneg_left (sq_nonneg _)
    have hGN : cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v ≤
        N / ENNReal.ofReal (s : ℝ) := by
      have h := cubeGagliardoIntegral_le_of_cubeFractionalSqNorm_le hd
        (0 : SpatialCoordinates d) 1 one_pos s v
        (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s v) hv le_rfl
      simpa only [centeredCube_volume, one_pow, ENNReal.ofReal_one, div_one] using h
    have hfoldL2 : (∫⁻ x in cubeExtensionTriple d, ENNReal.ofReal (f x ^ 2)) =
        A * ENNReal.ofReal (‖v‖ ^ 2) := by
      rw [lintegral_cubeExtensionFold _ (hvm.pow_const 2).ennreal_ofReal,
        cubeExtensionBox_eq, hL2]
    have hfoldG : (∫⁻ x in cubeExtensionTriple d, ∫⁻ y in cubeExtensionTriple d,
        cubeFractionalKernel s f x y) ≤ A ^ 2 * cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v := by
      simpa only [cubeExtensionBox_eq, cubeGagliardoIntegral, cubeFractionalKernel]
        using double_lintegral_cubeFractionalKernel_fold_le (s : ℝ) s.property.1.le v hvm
    calc
      globalFractionalSqNorm s V ≤
          2 * (∫⁻ x in cubeExtensionTriple d, ∫⁻ y in cubeExtensionTriple d, cubeFractionalKernel s f x y) +
            (1 + 4 * M) * ∫⁻ x in cubeExtensionTriple d, ENNReal.ofReal (f x ^ 2) :=
        globalFractionalSqNorm_cutoffExtension_le s s.property.1.le _ hUm f hfm hU
      _ ≤ 2 * (A ^ 2 * cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v) +
          (1 + 4 * M) * (A * ENNReal.ofReal (‖v‖ ^ 2)) := by
        rw [hfoldL2]
        exact add_le_add (mul_le_mul_of_nonneg_left hfoldG (zero_le _)) le_rfl
      _ ≤ 2 * (A ^ 2 * (N / ENNReal.ofReal (s : ℝ))) + (1 + 4 * M) * (A * N) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hGN (zero_le _)) (zero_le _))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2N (zero_le _)) (zero_le _))
      _ = K * N := by dsimp [K]; simp only [div_eq_mul_inv]; ring
      _ ≤ ENNReal.ofReal (C * cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s v) := by
        rw [ENNReal.ofReal_mul hC.le]
        exact mul_le_mul_of_nonneg_right hKC (zero_le N)


end SubdiffusiveProcess
