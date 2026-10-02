import SubdiffusiveProcess.Analysis.FractionalZeroExtensionEnergy
import SubdiffusiveProcess.Analysis.CubeFractionalBounds

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess

theorem exists_unit_cube_fractional_zero_extension (d : ℕ) (hd : 2 ≤ d)
    (s : Set.Ioo (0 : ℝ) 1) (hs : (1 / 2 : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
        ∃ V : SpatialCoordinates d → ℝ,
          (((v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 :
              SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d))] V) ∧
          (∀ x, x ∉ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) → V x = 0) ∧
          globalFractionalSqNorm s V ≤ ENNReal.ofReal
            (C * cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) := by
  have hd0 : 0 < d := by omega
  obtain ⟨H, hH, hHardy⟩ := exists_cubeBoundary_fractional_hardy d hd0 s hs s.property.2
  let M := cubeInterpolationKernelMass d (s : ℝ)
  let K : ℝ≥0∞ := 1 + (1 + 2 * M * ENNReal.ofReal H) / ENNReal.ofReal (s : ℝ)
  have hM : M ≠ ⊤ := cubeInterpolationKernelMass_ne_top hd0 s s.property.1
  have hs0 : ENNReal.ofReal (s : ℝ) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr s.property.1
  have hKt : K ≠ ⊤ := by
    dsimp only [K]
    apply ENNReal.add_ne_top.mpr
    refine ⟨ENNReal.one_ne_top, ENNReal.div_ne_top ?_ hs0⟩
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hM) ENNReal.ofReal_ne_top⟩
  let C : ℝ := K.toReal + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hKC : K ≤ ENNReal.ofReal C := by
    calc
      K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hKt).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp only [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro v
  let f := (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1
  let V : SpatialCoordinates d → ℝ := (cubeExtensionBox d).indicator (f : SpatialCoordinates d → ℝ)
  have hfm : Measurable (f : SpatialCoordinates d → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hvfinite : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
      (fun _ : Fin 1 => f) < ⊤ :=
    cubeFractionalL2Seminorm_lt_top_of_weakSobolevGraph d hd s (0 : SpatialCoordinates d) 1 one_pos
      ⟨v.val, killedSobolevGraph_le_weakSobolevGraph v.property⟩
  obtain ⟨u, hu, _⟩ := exists_nativeH10Function_of_killedSobolevGraph v
  have hum : Measurable (u : SpatialCoordinates d → ℝ) := by rw [hu]; exact hfm
  rw [cubeExtensionBox_eq] at hHardy
  have hnative := hHardy u hum
  have hboundary : cubeBoundaryWeightedIntegral s (f : SpatialCoordinates d → ℝ) ≤
      ENNReal.ofReal H * unitCubeFractionalEnergy s f := by
    simpa only [hu] using hnative
  refine ⟨V, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet] with x hx
    have hxQ : x ∈ cubeExtensionBox d := by rwa [cubeExtensionBox_eq]
    exact (Set.indicator_of_mem hxQ f).symm
  · intro x hx
    have hxQ : x ∉ cubeExtensionBox d := by
      intro hmem
      rw [cubeExtensionBox_eq] at hmem
      exact hx (centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos hmem)
    exact Set.indicator_of_notMem hxQ f
  · let N := ENNReal.ofReal (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s f)
    have hL2 : (∫⁻ x in cubeExtensionBox d, ENNReal.ofReal (f x ^ 2)) = ENNReal.ofReal (‖f‖ ^ 2) := by
      rw [cubeExtensionBox_eq, ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
        ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      exact (eLpNorm_two_sq_eq_lintegral_sq _ _).symm
    have hL2N : ENNReal.ofReal (‖f‖ ^ 2) ≤ N := by
      apply ENNReal.ofReal_le_ofReal
      simp only [cubeFractionalSqNorm, cubeFractionalVecSqNorm, Fin.sum_univ_one,
        centeredCube_volume_real, one_pow, div_one]
      exact le_add_of_nonneg_left (sq_nonneg _)
    have hGN : unitCubeFractionalEnergy s (f : SpatialCoordinates d → ℝ) ≤
        N / ENNReal.ofReal (s : ℝ) := by
      have h := cubeGagliardoIntegral_le_of_cubeFractionalSqNorm_le hd
        (0 : SpatialCoordinates d) 1 one_pos s f
        (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s f) hvfinite le_rfl
      simpa only [unitCubeFractionalEnergy, cubeExtensionBox_eq,
        cubeGagliardoIntegral, cubeFractionalKernel,
        centeredCube_volume, one_pow, ENNReal.ofReal_one, div_one] using h
    calc
      globalFractionalSqNorm s V ≤
          (∫⁻ x in cubeExtensionBox d, ENNReal.ofReal (f x ^ 2)) +
            unitCubeFractionalEnergy s f + 2 * M * cubeBoundaryWeightedIntegral s f :=
        globalFractionalSqNorm_zeroExtension_le s s.property.1 f hfm
      _ ≤ ENNReal.ofReal (‖f‖ ^ 2) + unitCubeFractionalEnergy s f +
          2 * M * (ENNReal.ofReal H * unitCubeFractionalEnergy s f) := by
        rw [hL2]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hboundary (zero_le _))
      _ ≤ N + (N / ENNReal.ofReal (s : ℝ)) +
          2 * M * (ENNReal.ofReal H * (N / ENNReal.ofReal (s : ℝ))) :=
        add_le_add (add_le_add hL2N hGN) (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hGN (zero_le _)) (zero_le _))
      _ = K * N := by dsimp only [K]; simp only [div_eq_mul_inv]; ring
      _ ≤ ENNReal.ofReal (C * cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s f) := by
        rw [ENNReal.ofReal_mul hC.le]
        exact mul_le_mul_of_nonneg_right hKC (zero_le _ )

end SubdiffusiveProcess
