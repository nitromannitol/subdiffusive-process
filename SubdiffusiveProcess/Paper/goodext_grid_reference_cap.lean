import SubdiffusiveProcess.Paper.goodext_catalog_root_absolute_cap
import SubdiffusiveProcess.Paper.goodext_reference_inverse_from_cell_cap



open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper
/-- The actual represented root-grid bounds give one reference inverse cap
for every countable cell, on its normalized upper-coefficient event. -/
theorem goodext_grid_reference_cap
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta
      thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (z0 : SpatialCoordinates d) (R0 : ℝ) (hR0 : 0 < R0)
    (hRoot : z j0 = z0 ∧ r j0 = R0)
    (Cells : Type) [Countable Cells] (level : Cells → ℕ)
    (centre : Cells → SpatialCoordinates d) (idx : Cells → Fin d → ℤ)
    (hcentre : ∀ b, centre b = fun i => z0 i + (3 : ℝ) ^ (-(level b : ℤ)) * idx b i)
    (hsub : ∀ b, (centeredCube (centre b) ((3 : ℝ) ^ (-(level b : ℤ)))
      (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R0 hR0 : Set (SpatialCoordinates d)))
    (scale : Cells → ℕ → Ω → ℝ) (ref hi : Cells → Ω → ℝ) (cap : ℝ)
    (hscale : ∀ b, ∀ᵐ omega ∂P, 0 < ref b omega ∧
      Tendsto (fun n => scale b n omega) atTop (𝓝 (ref b omega)))
    (hNorm : ∀ b, TendstoInMeasure P (fun n omega =>
      E.Lam (centre b) ((3 : ℝ) ^ (-(level b : ℤ))) (zpow_pos (by norm_num) _)
        (cutoffPositiveCoefficient M H (env n omega) (cutoff n)
          (centre b) (zpow_pos (by norm_num) _))
        (centre b) ((3 : ℝ) ^ (-(level b : ℤ))) ((beta - 1 / 2) / 4) 2 /
        scale b n omega) atTop (hi b)) :
    ∃ K : Ω → ℝ, (∀ omega, 0 ≤ K omega) ∧ ∀ᵐ omega ∂P, ∀ b,
      hi b omega ≤ cap → (ref b omega)⁻¹ ≤
        (K omega * ((3 : ℝ) ^ (-(level b : ℤ))) ^ (-eta)) * cap := by
  classical
  letI : NeZero d := ⟨by omega⟩
  have hRootCap := goodext_catalog_root_absolute_cap d hd M H Ω P cutoff env J j0 z r hr
    S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
    constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
    sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
    hRep z0 R0 hR0 hRoot
  have hFull : ∀ᵐ omega ∂P, omega ∈ G := by
    have h := hRep
    rcases h with ⟨_, _, _, _, _, _, _, _, _, hseq, _⟩
    rcases hseq with ⟨_, _, hnull, _⟩
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, not_not] using hnull
  let K : Ω → ℝ := fun omega => if h : omega ∈ G then Classical.choose (hRootCap omega h) else 0
  have hK : ∀ omega, 0 ≤ K omega := by
    intro omega
    by_cases h : omega ∈ G
    · simpa only [K, dif_pos h] using (Classical.choose_spec (hRootCap omega h)).1
    · simp only [K, dif_neg h, le_refl]
  have hCutoff : StrictMono cutoff := hRep.2.2.2.2.2.1
  have hSigma : (beta - 1 / 2) / 4 ∈ Ioc (0 : ℝ) 1 := by
    have ha := hRep.2.1
    have hb := hRep.2.2.1
    constructor <;> linarith only [ha.1, hb.1, hb.2]
  refine ⟨K, hK, ae_all_iff.mpr fun b => ?_⟩
  apply goodext_reference_inverse_from_cell_cap E P (centre b)
    ((3 : ℝ) ^ (-(level b : ℤ))) (zpow_pos (by norm_num) _)
    (fun n omega => cutoffPositiveCoefficient M H (env n omega) (cutoff n)
      (centre b) (zpow_pos (by norm_num) _))
    ((beta - 1 / 2) / 4) hSigma (scale b) (ref b) (hi b) K eta cap (hscale b) ?_ (hNorm b)
  filter_upwards [hFull] with omega homega
  refine ⟨hK omega, ?_⟩
  filter_upwards [hCutoff.tendsto_atTop.eventually (eventually_ge_atTop (level b))] with n hn
  have h := (Classical.choose_spec (hRootCap omega homega)).2 n (level b) (idx b) hn
    (zpow_pos (by norm_num) _)
  simp only [← hcentre b] at h
  have h' := h (hsub b)
  rw [hcentre b]
  rw [hcentre b] at h'
  simpa only [K, dif_pos homega] using h'

end Paper
