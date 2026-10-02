import SubdiffusiveProcess.Paper.in_represented_cutoff_geometry
import SubdiffusiveProcess.Paper.lem_cutoffs

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Every compact/open pair has the actual native cutoffs and uniform energy/growth bounds. -/
theorem in_represented_bounds_seq_local_cutoffs
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ)
    (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ
      (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey :
      ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented :
      Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (omega : Ω) (homega : omega ∈ G) :
    ∀ (K O : Set (SpatialCoordinates d)), IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (S j0).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm (S j0)
            (Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
            (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
                (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))).withDensity
                (fun y => ENNReal.ofReal
                  ((Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
                      (z j0) (hrad j0)).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)) := by
  classical
  intro K O hK hO hKO hOQ
  have hrep := hrepresented
  rcases hrep with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcomplete, _, _, _, _, _, _, _, _, _, _, hplateau, _⟩
  obtain ⟨b, W, Jmesh, hW, hKW, hWO, hrange, hone, hsupp, hmesh⟩ :=
    in_represented_cutoff_geometry z rad hrad j0 j0 (T j0) (theta j0) subset_rfl hcomplete
      (fun s o hs ho => hplateau j0 s o hs ho 0) K O hK hO hKO hOQ
  obtain ⟨chiH, chiS, chic, V, BE, BG, BH, hV, hKV, hVO, hBE, hBG, _, hchi, _⟩ :=
    aux_lem_cutoffs_rep_plateau d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0
      z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented
      omega homega b K O W Jmesh hK hO hOQ hW hKW hWO hrange hone hsupp hmesh
  refine ⟨V, chiS, chic, max BE BG, hV, hKV, hVO, hBE.trans (le_max_left _ _), fun n => ?_⟩
  obtain ⟨_, hc, hr, hv, h1, h0, _, _, he, hg, _⟩ := hchi n
  refine ⟨hc, hr, fun x hx => hv x (subset_closure hx), h1, h0,
    he.trans (le_max_left _ _), ?_⟩
  intro x hx rr hrr hrr1
  exact (hg x hx rr hrr hrr1).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_right BE BG) (Real.rpow_nonneg hrr.le t)))

end Paper

