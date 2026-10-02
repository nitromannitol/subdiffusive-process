import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_root_dirichlet_coordinate
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_shifted_dirichlet_coordinate
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_root_inverse_neumann_coordinate

open MeasureTheory SubdiffusiveProcess Homogenization Homogenization.Book.Ch02 Filter
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Uniform root and translated moment bounds for the coordinate tests used
by the primal and dual response matrix banks. `false` is the Dirichlet test;
`true` is the inverse Neumann test. -/
theorem lem_as_coarse_shallow_grid_bank_coordinate_moment {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 C0 : ℝ, 0 < δ0 ∧ 0 < C0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ0 →
      ∀ (b : Bool) (i : Fin d) (Z : BilateralField d → ℝ),
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M (Pi.single i 1) b) atTop Z →
        (AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure ∧
          eLpNorm Z (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * volume.real
              (centeredCube (0 : SpatialCoordinates d) 1
                (by norm_num) : Set (SpatialCoordinates d)) * (C0 + 1))) ∧
        ∀ (k : ℕ) (w : SpatialCoordinates d),
          AEStronglyMeasurable
            (fun om => Z (aux_lem_as_coarse_shallow_grid_scaleShift k w om))
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm
            (fun om => Z (aux_lem_as_coarse_shallow_grid_scaleShift k w om))
            (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * volume.real
              (centeredCube (0 : SpatialCoordinates d) 1
                (by norm_num) : Set (SpatialCoordinates d)) * (C0 + 1)) := by
  obtain ⟨δD, CD, hδD, hCD, hD⟩ :=
    lem_as_coarse_shallow_grid_shifted_dirichlet_coordinate hd I q hq
  obtain ⟨δDroot, CDroot, hδDroot, hCDroot, hDroot⟩ :=
    lem_as_coarse_shallow_grid_root_dirichlet_coordinate hd I q hq
  obtain ⟨δN, CN, hδN, hCN, hN⟩ :=
    lem_as_coarse_shallow_grid_root_inverse_neumann_coordinate hd I q hq
  refine ⟨min (min δD δDroot) δN, max (max CD CDroot) CN,
    lt_min (lt_min hδD hδDroot) hδN,
    lt_of_lt_of_le hCD (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro M hM b i Z hconv
  have hδDb : M.delta ≤ δD :=
    le_trans hM (le_trans (min_le_left (min δD δDroot) δN) (min_le_left δD δDroot))
  have hδDrootb : M.delta ≤ δDroot :=
    le_trans hM (le_trans (min_le_left (min δD δDroot) δN) (min_le_right δD δDroot))
  have hδNb : M.delta ≤ δN := le_trans hM (min_le_right (min δD δDroot) δN)
  have he : vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
    simp [vecNormSq, vecDot, Pi.single_apply]
  have hC_D : CD + 1 ≤ max (max CD CDroot) CN + 1 := by
    have hle : CD ≤ max (max CD CDroot) CN :=
      le_trans (le_max_left CD CDroot) (le_max_left (max CD CDroot) CN)
    linarith
  have hC_Droot : CDroot + 1 ≤ max (max CD CDroot) CN + 1 := by
    have hle : CDroot ≤ max (max CD CDroot) CN :=
      le_trans (le_max_right CD CDroot) (le_max_left (max CD CDroot) CN)
    linarith
  have hC_N : CN + 1 ≤ max (max CD CDroot) CN + 1 := by
    have hle : CN ≤ max (max CD CDroot) CN := le_max_right (max CD CDroot) CN
    linarith
  have hconst_nonneg : 0 ≤ 2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) := by
    positivity
  have hboundD : ENNReal.ofReal (2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) * (CD + 1)) ≤
      ENNReal.ofReal (2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) * (max (max CD CDroot) CN + 1)) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hC_D hconst_nonneg
  have hboundDroot : ENNReal.ofReal (2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) * (CDroot + 1)) ≤
      ENNReal.ofReal (2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) * (max (max CD CDroot) CN + 1)) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hC_Droot hconst_nonneg
  have hboundN : ENNReal.ofReal (2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) * (CN + 1)) ≤
      ENNReal.ofReal (2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) * (max (max CD CDroot) CN + 1)) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hC_N hconst_nonneg
  cases b with
  | false =>
      have hconvD : TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M (Pi.single i 1) false) atTop Z := by
        simpa using hconv
      have hDroot' := hDroot M hδDrootb (Pi.single i 1) he Z hconvD
      have hDshift := hD M hδDb (Pi.single i 1) he Z hconvD
      refine ⟨?_, ?_⟩
      · exact ⟨hDroot'.1, hDroot'.2.trans hboundDroot⟩
      · intro k w
        obtain ⟨hmeas, hbound⟩ := hDshift k w
        exact ⟨hmeas, hbound.trans hboundD⟩
  | true =>
      have hconvN : TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M (Pi.single i 1) true) atTop Z := by
        simpa using hconv
      have hNroot := hN M hδNb (Pi.single i 1) he Z hconvN
      refine ⟨?_, ?_⟩
      · exact ⟨hNroot.1.1, hNroot.1.2.trans hboundN⟩
      · intro k w
        obtain ⟨hmeas, hbound⟩ := hNroot.2 k w
        exact ⟨hmeas, hbound.trans hboundN⟩

end Paper

